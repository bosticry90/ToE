"""Digitize Shammass et al. arXiv:1207.3440v2 Fig. 2 into DS-02 omega(k) CSV.

Context
- Unlike some sources, this paper does not expose a numeric omega(k) table in the
  PDF text layer; DS-02 must be digitized from the figure.
- The repo already contains an autonomous, deterministic digitizer for Ernst Fig.
  2a. This tool mirrors that approach for Shammass Fig. 2.

Design constraints
- Deterministic: no RNG.
- Minimal dependencies: stdlib + numpy + scipy + pillow + PyMuPDF.
- Output is the repository DS-02 schema, sorted by k.

Operational scope
- Default series selection is "filled circles only". Open circles are rejected
  using a deterministic hole-detection heuristic.

NOTE
This tool is best-effort and may need crop/threshold tuning if the PDF render
changes. When it fails, use WebPlotDigitizer and the converter tool.
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
import sys
from dataclasses import dataclass
from datetime import date
from pathlib import Path

import fitz  # PyMuPDF
import numpy as np
from PIL import Image
from scipy import ndimage


RE_FLOAT = re.compile(r"^[+-]?(?:\d+(?:\.\d*)?|\.\d+)$")


def _ensure_repo_root_on_syspath() -> None:
    p = Path(__file__).resolve()
    while p != p.parent:
        if (p / "formal").exists():
            repo_root = p
            if str(repo_root) not in sys.path:
                sys.path.insert(0, str(repo_root))
            return
        p = p.parent


_ensure_repo_root_on_syspath()


@dataclass(frozen=True)
class Tick:
    value: float
    x: float
    y: float


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


def _extract_numeric_ticks(spans: list[tuple[str, fitz.Rect]], *, region: fitz.Rect) -> list[Tick]:
    out: list[Tick] = []
    for txt, rect in spans:
        if not region.intersects(rect):
            continue
        s = txt.strip()
        if RE_FLOAT.match(s) is None:
            continue
        try:
            v = float(s)
        except ValueError:
            continue
        c = rect.tl + (rect.br - rect.tl) * 0.5
        out.append(Tick(value=v, x=float(c.x), y=float(c.y)))

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
    t1 = min(ticks, key=lambda t: t.value)
    t2 = max(ticks, key=lambda t: t.value)
    if abs(t2.value - t1.value) < 1e-12:
        raise RuntimeError("Found ticks but they are not well-separated in value")
    return t1, t2


def _filter_ticks_near_common_axis_line(ticks: list[Tick], *, axis: str, tol: float = 6.0) -> list[Tick]:
    if not ticks:
        return []
    if axis not in {"x", "y"}:
        raise ValueError("axis must be 'x' or 'y'")

    coord = (lambda t: t.y) if axis == "x" else (lambda t: t.x)
    ts = sorted(ticks, key=coord)

    clusters: list[list[Tick]] = []
    cur: list[Tick] = [ts[0]]
    for t in ts[1:]:
        if abs(coord(t) - coord(cur[-1])) <= float(tol):
            cur.append(t)
        else:
            clusters.append(cur)
            cur = [t]
    clusters.append(cur)

    clusters.sort(key=lambda c: (len(c), max(tt.value for tt in c) - min(tt.value for tt in c)), reverse=True)
    best = clusters[0]
    return [t for t in best if math.isfinite(t.value)]


def _affine_1d(x: float, *, x1: float, v1: float, x2: float, v2: float) -> float:
    if abs(x2 - x1) < 1e-12:
        raise ZeroDivisionError("Degenerate calibration: x2 == x1")
    return v1 + (x - x1) * (v2 - v1) / (x2 - x1)


def _render_page_image(doc: fitz.Document, page_index: int, *, zoom: float) -> tuple[np.ndarray, float]:
    page = doc.load_page(page_index)
    mat = fitz.Matrix(zoom, zoom)
    pix = page.get_pixmap(matrix=mat, alpha=False)
    img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
    return np.asarray(img), float(zoom)


def _has_enclosed_hole(comp: np.ndarray) -> bool:
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

    if int(opening_iterations) > 0:
        k = int(opening_kernel)
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
        if ar < 0.70 or ar > 1.45:
            continue

        yy, xx = np.nonzero(comp)
        cx = float(xx.mean()) + float(xs.start)
        cy = float(yy.mean()) + float(ys.start)

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


def _find_page_with_fig2(doc: fitz.Document) -> int:
    for i in range(doc.page_count):
        page = doc.load_page(i)
        text = page.get_text("text") or ""
        if "Fig. 2" in text or "Fig.2" in text:
            return i
    # Fallback: last resort, just use the last page.
    return max(0, doc.page_count - 1)


@dataclass(frozen=True)
class CropCandidateResult:
    crop_fracs: tuple[float, float, float, float]
    n_markers_raw: int
    n_candidates: int
    n_selected: int
    kmin: float
    kmax: float
    n_lowk: int
    xt1: Tick
    xt2: Tick
    yt1: Tick
    yt2: Tick
    selected: list[tuple[float, float]]

    def score(self) -> tuple[float, float, float]:
        # Prefer a point count near ~20, then maximize kmax, then maximize low-k density.
        return (abs(self.n_selected - 20.0), -self.kmax, -self.n_lowk)


def _try_crop(
    *,
    page: fitz.Page,
    rgb: np.ndarray,
    zoom: float,
    crop_fracs: tuple[float, float, float, float],
    figure_value: str,
    dark_threshold: int,
    min_area: int,
    max_area: int,
    opening_kernel: int,
    opening_iterations: int,
    axis_pad_x_frac: float,
    axis_pad_y_frac: float,
    xaxis_reject_margin: float,
) -> CropCandidateResult | None:
    H, W = rgb.shape[0], rgb.shape[1]
    x0f, x1f, y0f, y1f = crop_fracs
    crop = (int(x0f * W), int(y0f * H), int(x1f * W), int(y1f * H))

    # Tick crop in PDF coords (same box by default)
    tick_crop_pdf = fitz.Rect(crop[0] / zoom, crop[1] / zoom, crop[2] / zoom, crop[3] / zoom)

    spans = _load_page_text_spans(page)
    plot_w = float(tick_crop_pdf.x1 - tick_crop_pdf.x0)
    plot_h = float(tick_crop_pdf.y1 - tick_crop_pdf.y0)

    x_tick_region = fitz.Rect(
        tick_crop_pdf.x0,
        tick_crop_pdf.y1 - (0.12 * plot_h),
        tick_crop_pdf.x1,
        tick_crop_pdf.y1 + (0.30 * plot_h),
    )

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

    comps_px = _auto_marker_components(
        rgb,
        crop=crop,
        dark_threshold=int(dark_threshold),
        min_area=int(min_area),
        max_area=int(max_area),
        opening_kernel=int(opening_kernel),
        opening_iterations=int(opening_iterations),
    )

    # If too few, this crop probably missed the plot.
    if len(comps_px) < 10:
        return None

    comps_pdf_all = [(m.cx_px / zoom, m.cy_px / zoom, m.has_hole) for m in comps_px]

    # Axis box filter
    x_min = min(xt1.x, xt2.x)
    x_max = max(xt1.x, xt2.x)
    y_min = min(yt1.y, yt2.y)
    y_max = max(yt1.y, yt2.y)

    pad_x = float(axis_pad_x_frac) * (x_max - x_min)
    pad_y = float(axis_pad_y_frac) * (y_max - y_min)

    comps_pdf = [(cx, cy, has_hole) for (cx, cy, has_hole) in comps_pdf_all if (x_min - pad_x) <= cx <= (x_max + pad_x) and (y_min - pad_y) <= cy <= (y_max + pad_y)]

    y0_tick = yt1.y if yt1.value == 0.0 else (yt2.y if yt2.value == 0.0 else None)

    # Convert to data coords.
    candidates: list[tuple[float, float, bool]] = []
    for (cx, cy, has_hole) in comps_pdf:
        if y0_tick is not None and cy >= (float(y0_tick) - float(xaxis_reject_margin)):
            continue
        k_um_inv = _affine_1d(cx, x1=xt1.x, v1=xt1.value, x2=xt2.x, v2=xt2.value)
        omega_khz = _affine_1d(cy, x1=yt1.y, v1=yt1.value, x2=yt2.y, v2=yt2.value)
        if omega_khz < -0.02:
            continue
        if k_um_inv < -1e-6:
            continue
        candidates.append((float(k_um_inv), float(omega_khz), bool(has_hole)))

    candidates.sort(key=lambda t: (t[0], t[1]))

    # Series selection: filled circles only => has_hole=False.
    selected = [(k, w) for (k, w, has_hole) in candidates if not has_hole]

    if len(selected) < 10:
        return None

    # De-duplicate (k,w) near-identical values that can arise from thick markers.
    dedup: list[tuple[float, float]] = []
    for k, w in selected:
        if dedup and abs(dedup[-1][0] - k) < 1e-6 and abs(dedup[-1][1] - w) < 1e-6:
            continue
        dedup.append((k, w))
    selected = dedup

    ks = [k for (k, _) in selected]
    ws = [w for (_, w) in selected]

    # Basic hygiene
    if any(k < 0.0 for k in ks) or any(w < 0.0 for w in ws):
        return None

    # Enforce strict k monotonicity (no duplicates).
    if any(ks[i] >= ks[i + 1] for i in range(len(ks) - 1)):
        return None

    # Gate-like heuristics for choosing a crop.
    kmax_required = 3.33842
    n_lowk = sum(1 for k in ks if k <= 1.5)
    if max(ks) + 1e-12 < kmax_required:
        return None
    if n_lowk < 8:
        return None

    return CropCandidateResult(
        crop_fracs=crop_fracs,
        n_markers_raw=int(len(comps_px)),
        n_candidates=int(len(candidates)),
        n_selected=int(len(selected)),
        kmin=float(min(ks)),
        kmax=float(max(ks)),
        n_lowk=int(n_lowk),
        xt1=xt1,
        xt2=xt2,
        yt1=yt1,
        yt2=yt2,
        selected=selected,
    )


def _write_ds02_csv(
    out_csv: Path,
    *,
    points: list[tuple[float, float]],
    source: str,
    figure: str,
    notes: str,
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
        for (k, omega) in points:
            w.writerow(
                {
                    "source": str(source),
                    "figure": str(figure),
                    "k_um_inv": f"{float(k):.12g}",
                    "omega_over_2pi_kHz": f"{float(omega):.12g}",
                    "sigma_k_um_inv": "",
                    "sigma_omega_over_2pi_kHz": "",
                    "notes": str(notes),
                }
            )


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--pdf", required=True)
    p.add_argument("--page", type=int, default=None, help="0-based page index containing Fig. 2 (default: auto-detect)")
    p.add_argument("--zoom", type=float, default=4.0)

    p.add_argument("--out-csv", required=True)
    p.add_argument("--figure", default="Fig. 2")
    p.add_argument("--source", default="Shammass_2012_arXiv_1207.3440v2")

    # Crop bounds as fractions of the rendered page. If not set, a small grid search is used.
    p.add_argument("--crop-x0", type=float, default=None)
    p.add_argument("--crop-x1", type=float, default=None)
    p.add_argument("--crop-y0", type=float, default=None)
    p.add_argument("--crop-y1", type=float, default=None)

    p.add_argument("--dark-threshold", type=int, default=120)
    p.add_argument("--min-area", type=int, default=10)
    p.add_argument("--max-area", type=int, default=4000)
    p.add_argument("--opening-kernel", type=int, default=2)
    p.add_argument("--opening-iterations", type=int, default=1)

    p.add_argument("--axis-pad-x-frac", type=float, default=0.02)
    p.add_argument("--axis-pad-y-frac", type=float, default=0.06)
    p.add_argument("--xaxis-reject-margin", type=float, default=0.35)

    args = p.parse_args(argv)

    pdf_path = Path(args.pdf)
    out_csv = Path(args.out_csv)

    doc = fitz.open(pdf_path)

    page_index = int(args.page) if args.page is not None else _find_page_with_fig2(doc)
    page = doc.load_page(page_index)

    # This digitizer requires numeric axis tick labels in the PDF text layer.
    # Some arXiv PDFs rasterize the full figure (including tick labels), which
    # makes calibration impossible without OCR or manual digitization.
    spans = _load_page_text_spans(page)
    numeric_anywhere = _extract_numeric_ticks(spans, region=page.rect)
    if len(numeric_anywhere) < 4:
        raise RuntimeError(
            "This PDF appears to rasterize Fig. 2 axis labels (no numeric ticks in the text layer), "
            "so autonomous calibration is not possible with this tool.\n\n"
            "Recommended path:\n"
            "  1) Use WebPlotDigitizer on the rendered image:\n"
            "     formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/fig2_page5_z4.png\n"
            "  2) Export X,Y as CSV (k_um_inv, omega_over_2pi_kHz).\n"
            "  3) Convert to DS-02 schema with:\n"
            "     python formal/python/tools/convert_webplotdigitizer_to_ds02_csv.py --in <wpd.csv> --out formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/omega_k_data.csv\n"
        )

    rgb, zoom = _render_page_image(doc, page_index, zoom=float(args.zoom))

    # Determine crop candidates.
    crop_is_set = all(v is not None for v in (args.crop_x0, args.crop_x1, args.crop_y0, args.crop_y1))
    if crop_is_set:
        crops = [(float(args.crop_x0), float(args.crop_x1), float(args.crop_y0), float(args.crop_y1))]
    else:
        # Coarse search grid; deterministic.
        xs0 = [0.08, 0.10, 0.12]
        xs1 = [0.88, 0.90, 0.92]
        ys0 = [0.12, 0.14, 0.16]
        ys1 = [0.60, 0.64, 0.68]
        crops = [(x0, x1, y0, y1) for x0 in xs0 for x1 in xs1 for y0 in ys0 for y1 in ys1 if (x1 - x0) > 0.5 and (y1 - y0) > 0.35]

    best: CropCandidateResult | None = None
    tried = 0
    for crop_fracs in crops:
        tried += 1
        try:
            r = _try_crop(
                page=page,
                rgb=rgb,
                zoom=zoom,
                crop_fracs=crop_fracs,
                figure_value=str(args.figure),
                dark_threshold=int(args.dark_threshold),
                min_area=int(args.min_area),
                max_area=int(args.max_area),
                opening_kernel=int(args.opening_kernel),
                opening_iterations=int(args.opening_iterations),
                axis_pad_x_frac=float(args.axis_pad_x_frac),
                axis_pad_y_frac=float(args.axis_pad_y_frac),
                xaxis_reject_margin=float(args.xaxis_reject_margin),
            )
        except Exception:
            continue
        if r is None:
            continue
        if best is None or r.score() < best.score():
            best = r

    if best is None:
        raise RuntimeError(
            "Auto-digitization failed to find a usable crop. "
            "Try manual digitization via WebPlotDigitizer, or rerun with explicit --crop-* and threshold tuning."
        )

    # Final points, already sorted by k.
    points = best.selected

    run_date = str(date.today())
    notes = (
        "auto-digitized from arXiv:1207.3440v2 Fig. 2 render; "
        "filled circles only (hole-reject); centroid extraction; "
        f"page={page_index}; zoom={float(args.zoom):g}; crop_fracs={best.crop_fracs}; "
        f"calib_xticks=({best.xt1.value},{best.xt2.value}); calib_yticks=({best.yt1.value},{best.yt2.value}); "
        f"date {run_date}"
    )

    _write_ds02_csv(
        out_csv,
        points=points,
        source=str(args.source),
        figure=str(args.figure),
        notes=notes,
    )

    print("Digitization summary:")
    print(f"  pdf: {pdf_path}")
    print(f"  page_index: {page_index}")
    print(f"  tried_crops: {tried}")
    print(f"  chosen_crop_fracs: {best.crop_fracs}")
    print(f"  selected_points: N={best.n_selected}")
    print(f"  k range: [{best.kmin:.6g}, {best.kmax:.6g}] um^-1")
    print(f"  low-k count: N(k<=1.5)={best.n_lowk}")
    print(f"  wrote: {out_csv}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
