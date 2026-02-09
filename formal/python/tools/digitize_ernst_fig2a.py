"""Digitize Ernst et al. arXiv:0908.4242v1 Fig. 2a into omega(k) CSV.

This tool exists to make the B1 dataset packet auditable + repeatable.

Design constraints
- Deterministic: no RNG.
- Minimal dependencies: stdlib + numpy + scipy + pillow + PyMuPDF.
- Evidence-friendly: records axis calibration tick choices in stdout so they can be
  copied into the dataset packet notes.

Operational protocol (mirrors repository governance)
- Fixed scope: 0908.4242v1.pdf, Fig. 2a, single series.
- Point picking: all visible markers for the chosen series between the leftmost
  and rightmost marker.
- Axis calibration: two well-separated ticks on each axis.
- Uncertainties: if unreadable, use placeholders uniformly for all rows.

NOTE
This script performs *deterministic* marker extraction from a PDF render.
If marker extraction fails (e.g., PDF format changes), fall back to a manual
workflow, but keep the protocol text in the dataset packet unchanged.
"""

from __future__ import annotations

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
import csv
import hashlib
import math
import re
from dataclasses import dataclass
from pathlib import Path

import fitz  # PyMuPDF
import numpy as np
from PIL import Image
from scipy import ndimage


RE_FLOAT = re.compile(r"^[+-]?(?:\d+(?:\.\d*)?|\.\d+)$")


@dataclass(frozen=True)
class Tick:
    value: float
    x: float
    y: float


def _sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def _load_page_text_spans(page: fitz.Page) -> list[tuple[str, fitz.Rect]]:
    d = page.get_text("dict")
    spans: list[tuple[str, fitz.Rect]] = []
    for block in d.get("blocks", []):
        for line in block.get("lines", []):
            for span in line.get("spans", []):
                txt = (span.get("text") or "").strip()
                if not txt:
                    continue
                bbox = span.get("bbox")
                if not bbox:
                    continue
                spans.append((txt, fitz.Rect(bbox)))
    return spans


def _extract_numeric_ticks(
    spans: list[tuple[str, fitz.Rect]], *, region: fitz.Rect
) -> list[Tick]:
    out: list[Tick] = []
    for txt, rect in spans:
        if not region.intersects(rect):
            continue
        s = txt.strip()
        # Some PDFs split numbers into multiple spans; we keep only clean floats.
        if RE_FLOAT.match(s) is None:
            continue
        try:
            v = float(s)
        except ValueError:
            continue
        c = rect.tl + (rect.br - rect.tl) * 0.5
        out.append(Tick(value=v, x=float(c.x), y=float(c.y)))
    # Deduplicate by (value, approx position)
    out.sort(key=lambda t: (t.value, t.x, t.y))
    dedup: list[Tick] = []
    for t in out:
        if dedup:
            last = dedup[-1]
            if abs(last.value - t.value) < 1e-9 and abs(last.x - t.x) < 0.5 and abs(last.y - t.y) < 0.5:
                continue
        dedup.append(t)
    return dedup


def _choose_two_well_separated(ticks: list[Tick]) -> tuple[Tick, Tick]:
    if len(ticks) < 2:
        raise RuntimeError("Could not find at least two numeric ticks for calibration")

    # Prefer min/max value to ensure separation.
    t1 = min(ticks, key=lambda t: t.value)
    t2 = max(ticks, key=lambda t: t.value)
    if abs(t2.value - t1.value) < 1e-12:
        raise RuntimeError("Found ticks but they are not well-separated in value")
    return t1, t2


def _filter_ticks_near_common_axis_line(ticks: list[Tick], *, axis: str, tol: float = 6.0) -> list[Tick]:
    """Filter ticks to a dominant axis line by clustering in x or y.

    PDF extraction often contains ticks from nearby subpanels. For x-ticks, we
    want the cluster with a common y (baseline). For y-ticks, we want the cluster
    with a common x (left tick-label column).
    """

    if not ticks:
        return []

    if axis not in {"x", "y"}:
        raise ValueError("axis must be 'x' or 'y'")

    coord = (lambda t: t.y) if axis == "x" else (lambda t: t.x)
    ts = sorted(ticks, key=coord)

    # Build simple 1D clusters.
    clusters: list[list[Tick]] = []
    cur: list[Tick] = [ts[0]]
    for t in ts[1:]:
        if abs(coord(t) - coord(cur[-1])) <= float(tol):
            cur.append(t)
        else:
            clusters.append(cur)
            cur = [t]
    clusters.append(cur)

    # Choose the largest cluster; tie-break by widest value span.
    clusters.sort(key=lambda c: (len(c), max(tt.value for tt in c) - min(tt.value for tt in c)), reverse=True)
    best = clusters[0]

    # Within that cluster, keep only plausible tick values (non-negative; finite).
    out = [t for t in best if math.isfinite(t.value)]
    return out


def _affine_1d(x: float, *, x1: float, v1: float, x2: float, v2: float) -> float:
    if abs(x2 - x1) < 1e-12:
        raise ZeroDivisionError("Degenerate calibration: x2 == x1")
    return v1 + (x - x1) * (v2 - v1) / (x2 - x1)


def _render_page_image(doc: fitz.Document, page_index: int, *, zoom: float) -> tuple[np.ndarray, float]:
    page = doc.load_page(page_index)
    mat = fitz.Matrix(zoom, zoom)
    pix = page.get_pixmap(matrix=mat, alpha=False)
    img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
    arr = np.asarray(img)
    return arr, float(zoom)


@dataclass(frozen=True)
class MarkerComponent:
    cx_px: float
    cy_px: float
    mean_rgb: tuple[int, int, int]
    area_px: int
    bbox_w_px: int
    bbox_h_px: int
    fill_ratio: float
    has_hole: bool


def _has_enclosed_hole(comp: np.ndarray) -> bool:
    """Return True if the component contains an enclosed background region.

    Deterministic heuristic to distinguish ring-like markers (open circles) from
    filled markers / crosses.
    """

    if comp.ndim != 2:
        raise ValueError("comp must be 2D")

    h, w = comp.shape
    if h < 3 or w < 3:
        return False

    background = ~comp

    seeds = np.zeros_like(background, dtype=bool)
    seeds[0, :] = True
    seeds[-1, :] = True
    seeds[:, 0] = True
    seeds[:, -1] = True
    seeds &= background

    # Flood fill background connected to the border.
    reachable = ndimage.binary_propagation(seeds, mask=background)
    enclosed = background & (~reachable)
    return bool(enclosed.any())


def _auto_marker_components(
    rgb: np.ndarray,
    *,
    crop: tuple[int, int, int, int],
    dark_threshold: int,
    min_area: int,
    max_area: int,
    opening_kernel: int,
    opening_iterations: int,
) -> list[MarkerComponent]:
    x0, y0, x1, y1 = crop
    sub = rgb[y0:y1, x0:x1, :]
    gray = (0.2126 * sub[:, :, 0] + 0.7152 * sub[:, :, 1] + 0.0722 * sub[:, :, 2]).astype(np.float32)

    mask = gray < float(dark_threshold)

    # Light denoise only. (Over-aggressive morphology can erase small markers.)
    if int(opening_iterations) > 0:
        k = int(opening_kernel)
        if k <= 0:
            raise ValueError("opening_kernel must be positive")
        mask = ndimage.binary_opening(mask, structure=np.ones((k, k), dtype=bool), iterations=int(opening_iterations))

    lbl, n = ndimage.label(mask)
    if n == 0:
        return []

    comps: list[MarkerComponent] = []
    slices = ndimage.find_objects(lbl)
    for idx, sl in enumerate(slices, start=1):
        if sl is None:
            continue
        ys, xs = sl
        comp = lbl[ys, xs] == idx
        area = int(comp.sum())
        if area < int(min_area) or area > int(max_area):
            continue

        h = int(ys.stop - ys.start)
        w = int(xs.stop - xs.start)
        if h <= 1 or w <= 1:
            continue
        ar = float(w) / float(h)
        # Markers should be roughly circular/square; reject thin caps/lines.
        if ar < 0.70 or ar > 1.45:
            continue

        # Centroid in crop-local coords
        yy, xx = np.nonzero(comp)
        cx = float(xx.mean()) + float(xs.start)
        cy = float(yy.mean()) + float(ys.start)

        # Mean RGB (component-local)
        rr = sub[:, :, 0][ys, xs][comp]
        gg = sub[:, :, 1][ys, xs][comp]
        bb = sub[:, :, 2][ys, xs][comp]
        mean_rgb = (int(np.mean(rr)), int(np.mean(gg)), int(np.mean(bb)))

        fill_ratio = float(area) / float(h * w)
        has_hole = _has_enclosed_hole(comp)

        comps.append(
            MarkerComponent(
                cx_px=float(x0) + cx,
                cy_px=float(y0) + cy,
                mean_rgb=mean_rgb,
                area_px=int(area),
                bbox_w_px=int(w),
                bbox_h_px=int(h),
                fill_ratio=float(fill_ratio),
                has_hole=bool(has_hole),
            )
        )

    comps.sort(key=lambda m: (m.cx_px, m.cy_px))
    return comps


def _bucket_rgb(rgb: tuple[int, int, int], *, step: int = 32) -> tuple[int, int, int]:
    if step <= 0:
        raise ValueError("step must be positive")
    r, g, b = rgb
    return (int(round(r / step) * step), int(round(g / step) * step), int(round(b / step) * step))


def _bucket_float(v: float, *, step: float) -> float:
    if step <= 0:
        raise ValueError("step must be positive")
    return float(round(float(v) / float(step)) * float(step))


def write_csv(
    out_csv: Path,
    *,
    rows: list[dict[str, str]],
) -> None:
    header = [
        "source",
        "figure",
        "k_um_inv",
        "omega_over_2pi_kHz",
        "sigma_k_um_inv",
        "sigma_omega_over_2pi_kHz",
        "notes",
    ]

    out_csv.parent.mkdir(parents=True, exist_ok=True)
    with out_csv.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=header)
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in header})


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--pdf", required=True, help="Path to 0908.4242v1.pdf")
    p.add_argument("--page", type=int, default=3, help="0-based page index for the Fig. 2 page (default: 3)")
    p.add_argument("--zoom", type=float, default=4.0, help="Render zoom factor (default: 4.0)")

    # Crop bounds as fractions of the rendered page.
    # Defaults are tuned to the Fig. 2a panel on page 4 for 0908.4242v1.
    p.add_argument("--crop-x0", type=float, default=0.25)
    p.add_argument("--crop-x1", type=float, default=0.78)
    p.add_argument("--crop-y0", type=float, default=0.10)
    p.add_argument("--crop-y1", type=float, default=0.38)

    # Optional separate crop for tick-label detection (PDF text layer). If set,
    # it should bracket the plot panel tightly enough to include tick labels.
    p.add_argument("--tick-crop-x0", type=float, default=None)
    p.add_argument("--tick-crop-x1", type=float, default=None)
    p.add_argument("--tick-crop-y0", type=float, default=None)
    p.add_argument("--tick-crop-y1", type=float, default=None)

    p.add_argument("--out-csv", required=True)
    p.add_argument("--figure", default="Fig2a")
    p.add_argument("--source", default="Ernst_2009_arXiv_0908.4242v1")

    p.add_argument("--a-um", type=float, default=0.515, help="Lattice spacing a in microns (default 0.515 µm)")

    p.add_argument("--dark-threshold", type=int, default=115)
    p.add_argument("--min-area", type=int, default=12)
    p.add_argument("--max-area", type=int, default=2500)

    p.add_argument(
        "--opening-kernel",
        type=int,
        default=2,
        help="Binary opening kernel size in pixels (default: 2; used only if --opening-iterations>0)",
    )
    p.add_argument(
        "--opening-iterations",
        type=int,
        default=1,
        help="Binary opening iterations (default: 1; set 0 to disable)",
    )

    p.add_argument("--sigma-k", type=float, default=0.05)
    p.add_argument("--sigma-omega", type=float, default=0.10)

    p.add_argument(
        "--series-select",
        default="upper-envelope",
        choices=(
            "upper-envelope",
            "color-bucket",
            "monotone-lis",
            "strict-single-series",
            "strict-branch",
            "all",
        ),
        help=(
            "How to select a single Fig2a series from extracted marker candidates. "
            "'upper-envelope' keeps the max-omega marker within each k-cluster (default). "
            "'color-bucket' chooses a dominant marker-color bucket inside the plot and then keeps all points from that bucket. "
            "'monotone-lis' chooses a single monotone-increasing ω(k) sequence (longest nondecreasing subsequence in ω after sorting by k). "
            "'strict-single-series' selects exactly one marker-style cluster (shape/fill + color), requiring 15–25 points and minimal inversions. "
            "'strict-branch' selects a single smooth branch by choosing one point per k-cluster to minimize curvature under a nondecreasing ω constraint (deterministic). "
            "'all' writes all detected candidates (debug only; not protocol-compliant if multiple series exist)."
        ),
    )

    p.add_argument(
        "--color-bucket-step",
        type=int,
        default=32,
        help="RGB bucket step size for color-bucket selection (default: 32)",
    )
    p.add_argument(
        "--style-fill-step",
        type=float,
        default=0.08,
        help="Fill-ratio bucket step for strict-single-series selection (default: 0.08)",
    )
    p.add_argument(
        "--style-color-step",
        type=int,
        default=32,
        help="RGB bucket step for strict-single-series selection (default: 32)",
    )
    p.add_argument(
        "--k-cluster-tol",
        type=float,
        default=0.14,
        help="k clustering tolerance in um^-1 for series selection (default: 0.14)",
    )

    p.add_argument(
        "--axis-pad-x-frac",
        type=float,
        default=0.02,
        help="Fractional padding for axis-box x filtering (default: 0.02)",
    )
    p.add_argument(
        "--axis-pad-y-frac",
        type=float,
        default=0.06,
        help="Fractional padding for axis-box y filtering (default: 0.06)",
    )

    p.add_argument(
        "--omega-nondecreasing-tol",
        type=float,
        default=0.03,
        help=(
            "Tolerance for small ω decreases between adjacent k clusters in strict-branch; "
            "decreases beyond this are penalized (default: 0.03 kHz)"
        ),
    )

    p.add_argument(
        "--omega-decrease-penalty",
        type=float,
        default=5.0,
        help="Penalty weight for ω decreases beyond --omega-nondecreasing-tol in strict-branch (default: 5.0)",
    )

    p.add_argument(
        "--branch-allow-skip",
        action="store_true",
        help="Allow strict-branch to skip entire k-clusters (useful if extraction mixes multiple series); default selects one point per cluster",
    )

    p.add_argument(
        "--xaxis-reject-margin",
        type=float,
        default=0.35,
        help="Margin (in PDF y units) above the y(ω=0) tick used to reject x-axis/label false positives (default: 0.35)",
    )

    args = p.parse_args(argv)

    pdf_path = Path(args.pdf)
    out_csv = Path(args.out_csv)

    doc = fitz.open(pdf_path)
    page = doc.load_page(int(args.page))

    # Render for marker detection
    rgb, zoom = _render_page_image(doc, int(args.page), zoom=float(args.zoom))
    H, W = rgb.shape[0], rgb.shape[1]

    crop = (
        int(float(args.crop_x0) * W),
        int(float(args.crop_y0) * H),
        int(float(args.crop_x1) * W),
        int(float(args.crop_y1) * H),
    )

    tick_crop_spec = (args.tick_crop_x0, args.tick_crop_x1, args.tick_crop_y0, args.tick_crop_y1)
    tick_crop_is_set = any(v is not None for v in tick_crop_spec)
    if tick_crop_is_set and not all(v is not None for v in tick_crop_spec):
        raise ValueError("If any --tick-crop-* is provided, all four must be provided")

    tick_crop = crop
    if tick_crop_is_set:
        tick_crop = (
            int(float(args.tick_crop_x0) * W),
            int(float(args.tick_crop_y0) * H),
            int(float(args.tick_crop_x1) * W),
            int(float(args.tick_crop_y1) * H),
        )

    # Convert tick crop to PDF coordinate space (PyMuPDF coordinates scale linearly with zoom)
    tick_crop_pdf = fitz.Rect(
        tick_crop[0] / zoom,
        tick_crop[1] / zoom,
        tick_crop[2] / zoom,
        tick_crop[3] / zoom,
    )

    spans = _load_page_text_spans(page)

    # Regions for tick labels in PDF coords (heuristic offsets relative to plot panel)
    plot_w = float(tick_crop_pdf.x1 - tick_crop_pdf.x0)
    plot_h = float(tick_crop_pdf.y1 - tick_crop_pdf.y0)

    # x tick labels tend to straddle the crop bottom slightly.
    x_tick_region = fitz.Rect(
        tick_crop_pdf.x0,
        tick_crop_pdf.y1 - (0.12 * plot_h),
        tick_crop_pdf.x1,
        tick_crop_pdf.y1 + (0.30 * plot_h),
    )

    # y tick labels sit near the left side of the plot, but may still be inside
    # the crop if the crop includes some left margin.
    y_tick_region = fitz.Rect(
        tick_crop_pdf.x0,
        tick_crop_pdf.y0,
        tick_crop_pdf.x0 + (0.28 * plot_w),
        tick_crop_pdf.y1,
    )

    x_ticks_all = _extract_numeric_ticks(spans, region=x_tick_region)
    y_ticks_all = _extract_numeric_ticks(spans, region=y_tick_region)

    x_ticks = _filter_ticks_near_common_axis_line(x_ticks_all, axis="x")
    y_ticks = _filter_ticks_near_common_axis_line(y_ticks_all, axis="y")

    xt1, xt2 = _choose_two_well_separated(x_ticks)
    yt1, yt2 = _choose_two_well_separated(y_ticks)

    print("Axis calibration (auto-detected):")
    print(f"  x ticks: {xt1.value} at (x={xt1.x:.2f}, y={xt1.y:.2f}) and {xt2.value} at (x={xt2.x:.2f}, y={xt2.y:.2f})")
    print(f"  y ticks: {yt1.value} at (x={yt1.x:.2f}, y={yt1.y:.2f}) and {yt2.value} at (x={yt2.x:.2f}, y={yt2.y:.2f})")

    # Detect marker components in pixel space (within crop)
    comps_px = _auto_marker_components(
        rgb,
        crop=crop,
        dark_threshold=int(args.dark_threshold),
        min_area=int(args.min_area),
        max_area=int(args.max_area),
        opening_kernel=int(args.opening_kernel),
        opening_iterations=int(args.opening_iterations),
    )

    if len(comps_px) < 10:
        raise RuntimeError(
            f"Too few markers detected in crop (N={len(comps_px)}). "
            "Adjust crop or thresholds; do not proceed with sparse extraction."
        )

    # Convert pixel centroids to PDF coordinates
    comps_pdf_all = [
        (
            m.cx_px / zoom,
            m.cy_px / zoom,
            m.mean_rgb,
            m.fill_ratio,
            m.has_hole,
        )
        for m in comps_px
    ]

    # Convert to data coordinates
    a_um = float(args.a_um)
    k_factor = math.sqrt(2.0) * math.pi / a_um

    # Filter to the calibrated axis box to suppress stray text/lines.
    x_min = min(xt1.x, xt2.x)
    x_max = max(xt1.x, xt2.x)
    y_min = min(yt1.y, yt2.y)
    y_max = max(yt1.y, yt2.y)

    # Pad slightly to tolerate tick-label offsets.
    pad_x = float(args.axis_pad_x_frac) * (x_max - x_min)
    pad_y = float(args.axis_pad_y_frac) * (y_max - y_min)

    comps_pdf = [
        (cx, cy, mean_rgb, fill_ratio, has_hole)
        for (cx, cy, mean_rgb, fill_ratio, has_hole) in comps_pdf_all
        if (x_min - pad_x) <= cx <= (x_max + pad_x) and (y_min - pad_y) <= cy <= (y_max + pad_y)
    ]

    # Convert marker candidates to (k, omega) in declared units.
    candidates: list[tuple[float, float, tuple[int, int, int], float, bool]] = []
    y0_tick = yt1.y if yt1.value == 0.0 else (yt2.y if yt2.value == 0.0 else None)
    for (cx, cy, mean_rgb, fill_ratio, has_hole) in comps_pdf:
        # Exclude points on/under the x-axis tick line (common false-positives).
        if y0_tick is not None and cy >= (float(y0_tick) - float(args.xaxis_reject_margin)):
            continue

        s = _affine_1d(cx, x1=xt1.x, v1=xt1.value, x2=xt2.x, v2=xt2.value)
        omega_khz = _affine_1d(cy, x1=yt1.y, v1=yt1.value, x2=yt2.y, v2=yt2.value)

        # Reject out-of-axis-range omega (tick artifacts can map slightly negative).
        if omega_khz < -0.02:
            continue

        k_um_inv = float(s) * float(k_factor)
        # Reject clearly out-of-axis k (spurious detections left of the k=0 tick).
        if k_um_inv < -1e-6:
            continue
        candidates.append((float(k_um_inv), float(omega_khz), mean_rgb, float(fill_ratio), bool(has_hole)))

    candidates.sort(key=lambda t: (t[0], t[1]))
    print(f"Marker candidates after axis filtering: N={len(candidates)}")

    selected: list[tuple[float, float]]
    if str(args.series_select) == "all":
        selected = [(k, w) for (k, w, _, _, _) in candidates]
    elif str(args.series_select) == "color-bucket":
        step = int(args.color_bucket_step)
        buckets: dict[tuple[int, int, int], list[tuple[float, float]]] = {}
        for (k, w, rgb_mean, _, _) in candidates:
            b = _bucket_rgb(rgb_mean, step=step)
            buckets.setdefault(b, []).append((k, w))

        # Score buckets by: count (prefer 15–25), then monotonicity (few inversions), then count.
        def score(pts: list[tuple[float, float]]) -> tuple[int, int, int]:
            pts_sorted = sorted(pts, key=lambda t: t[0])
            omegas = [w for (_, w) in pts_sorted]
            inversions = sum(1 for i in range(1, len(omegas)) if omegas[i] + 1e-9 < omegas[i - 1])
            n = len(pts)
            in_range = 1 if (15 <= n <= 25) else 0
            # Higher is better: prefer in_range, then fewer inversions, then larger n
            return (in_range, -inversions, n)

        if not buckets:
            raise RuntimeError("No color buckets found")

        bucket_items = sorted(buckets.items(), key=lambda kv: score(kv[1]), reverse=True)
        print("Color buckets (top 5):")
        for b, pts in bucket_items[:5]:
            pts_sorted = sorted(pts, key=lambda t: t[0])
            omegas = [w for (_, w) in pts_sorted]
            inv = sum(1 for i in range(1, len(omegas)) if omegas[i] + 1e-9 < omegas[i - 1])
            print(f"  bucket={b} N={len(pts)} inversions={inv}")

        chosen_bucket, chosen_pts = bucket_items[0]
        print(f"Chosen bucket: {chosen_bucket} (step={step})")
        selected = list(chosen_pts)
    elif str(args.series_select) == "strict-single-series":
        tol = float(args.k_cluster_tol)
        if tol <= 0.0:
            raise ValueError("--k-cluster-tol must be positive")

        fill_step = float(args.style_fill_step)
        color_step = int(args.style_color_step)

        # Cluster by marker style only: (has_hole, fill_ratio bucket).
        # Color is *summarized* for audit but not used as a hard key, to avoid
        # splitting a single series due to anti-aliasing / render variance.
        style_buckets: dict[tuple[bool, float], list[tuple[float, float, tuple[int, int, int]]]] = {}
        for (k, w, rgb_mean, fill_ratio, has_hole) in candidates:
            key = (bool(has_hole), _bucket_float(float(fill_ratio), step=fill_step))
            style_buckets.setdefault(key, []).append((float(k), float(w), _bucket_rgb(rgb_mean, step=color_step)))

        if not style_buckets:
            raise RuntimeError("No marker-style buckets found")

        def pick_branch_by_k_cluster(
            pts: list[tuple[float, float]], *, branch: str
        ) -> list[tuple[float, float]]:
            if branch not in {"upper", "lower"}:
                raise ValueError("branch must be 'upper' or 'lower'")

            items = sorted(pts, key=lambda t: (t[0], t[1]))
            out: list[tuple[float, float]] = []
            i = 0
            while i < len(items):
                k0 = items[i][0]
                j = i + 1
                while j < len(items) and abs(items[j][0] - k0) <= tol:
                    j += 1
                cluster = items[i:j]
                out.append((max if branch == "upper" else min)(cluster, key=lambda t: t[1]))
                i = j
            out.sort(key=lambda t: t[0])
            return out

        def inversions(pts_sorted: list[tuple[float, float]]) -> int:
            ws = [w for (_, w) in pts_sorted]
            return sum(1 for i in range(1, len(ws)) if ws[i] + 1e-9 < ws[i - 1])

        def poly2_rmse(pts_sorted: list[tuple[float, float]]) -> float:
            if len(pts_sorted) < 3:
                return float("inf")
            xs = np.array([k for (k, _) in pts_sorted], dtype=float)
            ys = np.array([w for (_, w) in pts_sorted], dtype=float)
            A = np.stack([xs * xs, xs, np.ones_like(xs)], axis=1)
            coeffs, *_ = np.linalg.lstsq(A, ys, rcond=None)
            yhat = A @ coeffs
            rmse = float(np.sqrt(np.mean((ys - yhat) ** 2)))
            return rmse

        scored: list[
            tuple[
                tuple[int, int, float, int],
                tuple[bool, float],
                str,
                list[tuple[float, float]],
                dict[tuple[int, int, int], int],
            ]
        ] = []

        for key, pts3 in style_buckets.items():
            pts = [(k, w) for (k, w, _) in pts3]

            color_counts: dict[tuple[int, int, int], int] = {}
            for (_, _, cb) in pts3:
                color_counts[cb] = color_counts.get(cb, 0) + 1

            for branch in ("upper", "lower"):
                pts_sel = pick_branch_by_k_cluster(pts, branch=branch)
                n = len(pts_sel)
                inv = inversions(pts_sel)
                rmse = poly2_rmse(pts_sel)

                in_range = 1 if (15 <= n <= 25) else 0
                # Prefer in-range; then fewer inversions; then smoother; then more points.
                score = (in_range, -inv, -rmse, n)
                scored.append((score, key, branch, pts_sel, color_counts))

        scored.sort(key=lambda t: t[0], reverse=True)

        print("Marker-style buckets (top 10, after k-cluster branch pick):")
        for score, key, branch, pts_sel, color_counts in scored[:10]:
            in_range, neg_inv, neg_rmse, n = score
            top_colors = sorted(color_counts.items(), key=lambda kv: kv[1], reverse=True)[:3]
            print(
                f"  key={key} branch={branch} N={n} inversions={-neg_inv} rmse={-neg_rmse:.4g} in_range={bool(in_range)} colors={top_colors}"
            )

        best_score, best_key, best_branch, best_pts, best_colors = scored[0]
        if best_score[0] != 1:
            raise RuntimeError(
                "strict-single-series could not find a marker-style cluster with 15–25 points. "
                "Try adjusting --style-fill-step/--style-color-step or the detection thresholds."
            )

        print(
            "Chosen strict single-series bucket: "
            f"has_hole={best_key[0]} fill_bucket={best_key[1]} branch={best_branch} "
            f"(fill_step={fill_step}, color_step={color_step})"
        )
        top_colors = sorted(best_colors.items(), key=lambda kv: kv[1], reverse=True)[:5]
        print(f"Chosen bucket color summary (top 5): {top_colors}")
        selected = list(best_pts)
    elif str(args.series_select) == "strict-branch":
        tol = float(args.k_cluster_tol)
        if tol <= 0.0:
            raise ValueError("--k-cluster-tol must be positive")

        # Group candidates into k-clusters (deterministic, stable ordering).
        items = [(k, w) for (k, w, _, _, _) in candidates]
        items.sort(key=lambda t: (t[0], t[1]))

        clusters: list[list[tuple[float, float]]] = []
        cur: list[tuple[float, float]] = []
        for k, w in items:
            if not cur:
                cur = [(k, w)]
                continue
            if abs(k - cur[-1][0]) <= tol:
                cur.append((k, w))
            else:
                clusters.append(cur)
                cur = [(k, w)]
        if cur:
            clusters.append(cur)

        omega_tol = float(args.omega_nondecreasing_tol)
        if omega_tol < 0.0:
            raise ValueError("--omega-nondecreasing-tol must be non-negative")

        omega_decrease_penalty = float(args.omega_decrease_penalty)
        if omega_decrease_penalty < 0.0:
            raise ValueError("--omega-decrease-penalty must be non-negative")

        # Flatten points and assign stable global indices.
        points: list[tuple[float, float]] = []
        cluster_point_ids: list[list[int]] = []
        for c in clusters:
            ids: list[int] = []
            for p in sorted(c, key=lambda t: (t[0], t[1])):
                ids.append(len(points))
                points.append(p)
            cluster_point_ids.append(ids)

        NONE = -1  # sentinel for "no point yet"

        def omega_decrease_cost(w_prev: float, w_next: float) -> float:
            dw = float(w_prev) - float(w_next)
            if dw <= float(omega_tol):
                return 0.0
            return float(omega_decrease_penalty) * float((dw - float(omega_tol)) ** 2)

        # DP state keyed by (last2, last1) where last1 is most recent selected point id.
        # Value is (neg_count, cost). We minimize lexicographically.
        dp: dict[tuple[int, int], tuple[int, float]] = {(NONE, NONE): (0, 0.0)}
        back: list[dict[tuple[int, int], tuple[tuple[int, int], int | None]]] = []

        for ci, ids in enumerate(cluster_point_ids):
            new_dp: dict[tuple[int, int], tuple[int, float]] = {}
            bi: dict[tuple[int, int], tuple[tuple[int, int], int | None]] = {}

            if bool(args.branch_allow_skip):
                # Skip option: carry forward the previous state unchanged.
                new_dp.update(dp)
                bi.update({key: (key, None) for key in dp.keys()})

            for (last2, last1), (neg_count, cost) in dp.items():
                # Consider picking a point in this cluster.
                for pid in ids:
                    k_next, w_next = points[pid]
                    if last1 != NONE:
                        k_prev, w_prev = points[last1]
                        if k_next <= k_prev + 1e-12:
                            continue

                    new_last2, new_last1 = last1, pid
                    new_neg_count = int(neg_count) - 1
                    new_cost = float(cost)
                    if last1 != NONE:
                        _, w_prev = points[last1]
                        new_cost += omega_decrease_cost(w_prev, w_next)
                    if last2 != NONE and last1 != NONE:
                        _, w0 = points[last2]
                        _, w1 = points[last1]
                        d2 = (w_next - w1) - (w1 - w0)
                        new_cost += float(d2 * d2)

                    key = (new_last2, new_last1)
                    cand = (new_neg_count, new_cost)
                    best = new_dp.get(key)
                    if best is None or cand < best:
                        new_dp[key] = cand
                        bi[key] = ((last2, last1), pid)

            if not new_dp:
                raise RuntimeError("strict-branch: no feasible transitions (try --branch-allow-skip)")
            dp = new_dp
            back.append(bi)

        # Choose best terminal state (max count, then min cost).
        end_state = min(dp.keys(), key=lambda st: dp[st])
        neg_count, total_cost = dp[end_state]
        print(f"strict-branch DP selected N={-neg_count} points; cost={total_cost:.6g}")

        # Backtrack selected point ids.
        chosen_ids: list[int] = []
        st = end_state
        for ci in range(len(cluster_point_ids) - 1, -1, -1):
            prev_st, picked = back[ci][st]
            if picked is not None:
                chosen_ids.append(picked)
            st = prev_st
        chosen_ids.reverse()
        selected = [points[i] for i in chosen_ids]
    elif str(args.series_select) == "monotone-lis":
        # Longest nondecreasing subsequence in omega after sorting by k.
        pts = [(k, w) for (k, w, _, _, _) in candidates]
        pts.sort(key=lambda t: (t[0], t[1]))

        n = len(pts)
        if n == 0:
            selected = []
        else:
            dp = [1] * n
            prev = [-1] * n
            for i in range(n):
                for j in range(i):
                    if pts[j][1] <= pts[i][1] + 1e-12 and dp[j] + 1 > dp[i]:
                        dp[i] = dp[j] + 1
                        prev[i] = j

            end = max(range(n), key=lambda i: dp[i])
            seq: list[tuple[float, float]] = []
            while end != -1:
                seq.append(pts[end])
                end = prev[end]
            selected = list(reversed(seq))
    else:
        # Cluster by k and keep the maximum omega in each cluster (upper envelope).
        tol = float(args.k_cluster_tol)
        if tol <= 0.0:
            raise ValueError("--k-cluster-tol must be positive")

        selected = []
        i = 0
        while i < len(candidates):
            k0 = candidates[i][0]
            j = i + 1
            while j < len(candidates) and abs(candidates[j][0] - k0) <= tol:
                j += 1
            cluster = candidates[i:j]
            best = max(cluster, key=lambda t: t[1])
            selected.append((best[0], best[1]))
            i = j

    selected.sort(key=lambda t: t[0])
    print(f"Selected single-series points: N={len(selected)} (mode={args.series_select})")

    mode_note = {
        "upper-envelope": "upper-envelope per k cluster",
        "color-bucket": "dominant marker-color bucket",
        "monotone-lis": "monotone ω(k) LIS",
        "strict-single-series": "strict single-series by marker-style cluster (shape/fill + color) and k-cluster envelope",
        "strict-branch": "strict single-branch selection (smoothness DP over k clusters; nondecreasing ω)",
        "all": "all extracted markers in plot region",
    }.get(str(args.series_select), str(args.series_select))

    rows: list[dict[str, str]] = []
    for (k_um_inv, omega_khz) in selected:
        rows.append(
            {
                "source": str(args.source),
                "figure": str(args.figure),
                "k_um_inv": f"{k_um_inv:.6g}",
                "omega_over_2pi_kHz": f"{omega_khz:.6g}",
                "sigma_k_um_inv": f"{float(args.sigma_k):.6g}",
                "sigma_omega_over_2pi_kHz": f"{float(args.sigma_omega):.6g}",
                "notes": (
                    "Auto-digitized from arXiv:0908.4242v1 p4 Fig2a render; "
                    f"series selection={mode_note}; "
                    "axis calibrated via two ticks; k= s*sqrt(2)*pi/a with a=515 nm."
                ),
            }
        )

    # Sort by k ascending
    rows.sort(key=lambda r: float(r["k_um_inv"]))

    write_csv(out_csv, rows=rows)
    out_bytes = out_csv.read_bytes()

    print(f"Wrote {out_csv} rows={len(rows)} sha256={_sha256_bytes(out_bytes)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
