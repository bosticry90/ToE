"""Digitize DS-02 (Shammass Fig. 2) from a PNG render.

Why this exists
- Some PDF renders rasterize axis tick labels, making text-layer calibration impossible.
- This tool digitizes from a PNG using deterministic image-processing heuristics.

Important
- Calibration uses an affine mapping from the detected plot box to provided axis ranges.
- Default axis ranges match the visible axes in the canonical Fig. 2 render:
    x (k, um^-1): [0, 4.5]
    y (omega/2pi, kHz): [0, 2.0]
- If your render differs, pass --xmax/--ymax (and optionally --xmin/--ymin).

Output
- Writes the repository DS-02 schema CSV, sorted by k.
- Enforces filled-circle selection by rejecting components with enclosed holes.

Usage
  python -m formal.python.tools.digitize_ds02_from_png \
    --png formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/fig2_page5_z4.png \
    --out-csv formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/omega_k_data.csv \
    --source "Shammass2012_arXiv1207.3440v2_Fig2_filled_circles" \
    --figure "Fig. 2" \
    --notes "digitized from PNG; filled circles only; error bars not digitized"

Then run
  python -m formal.python.tools.generate_ds02_dr_artifacts --report
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
import math
import sys
from dataclasses import dataclass
from pathlib import Path

import numpy as np
from PIL import Image
from scipy import ndimage


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
class PlotBox:
    left: int
    right: int
    top: int
    bottom: int

    def width(self) -> int:
        return int(self.right - self.left)

    def height(self) -> int:
        return int(self.bottom - self.top)


def _to_gray(img: np.ndarray) -> np.ndarray:
    if img.ndim != 3 or img.shape[2] != 3:
        raise ValueError("expected RGB image")
    r = img[:, :, 0].astype(np.float32)
    g = img[:, :, 1].astype(np.float32)
    b = img[:, :, 2].astype(np.float32)
    return (0.2126 * r + 0.7152 * g + 0.0722 * b).astype(np.float32)


def _find_plot_box(gray: np.ndarray, *, dark_threshold: int = 80) -> PlotBox:
    """Heuristically locate the main plot axes box.

    We look for a dense horizontal axis line near the bottom and a dense vertical
    axis line near the left. Then we estimate plot extents from those lines.
    """

    H, W = gray.shape
    dark = gray < float(dark_threshold)

    # Candidate x-axis: strongest horizontal dark density in the lower 40%.
    y0 = int(0.55 * H)
    row_scores = dark[y0:, :].mean(axis=1)
    y_axis = int(y0 + int(np.argmax(row_scores)))

    # Candidate y-axis: strongest vertical dark density in the left 40%.
    x1 = int(0.45 * W)
    col_scores = dark[:, :x1].mean(axis=0)
    x_axis = int(np.argmax(col_scores))

    # Estimate right bound: last significant dark run on the x-axis row.
    row = dark[y_axis, :]
    xs = np.where(row)[0]
    if xs.size == 0:
        raise RuntimeError("Could not detect x-axis line")
    right = int(np.percentile(xs, 99.0))

    # Estimate top bound: highest y where the y-axis column stays dark.
    col = dark[:, x_axis]
    ys = np.where(col)[0]
    if ys.size == 0:
        raise RuntimeError("Could not detect y-axis line")
    top = int(np.percentile(ys, 1.0))

    # Left bound: slightly right of the y-axis (avoid the line itself).
    left = int(x_axis + 1)

    # Bottom bound: slightly above x-axis (avoid the line itself).
    bottom = int(y_axis - 1)

    # Add small padding inward to avoid labels and axis ink.
    pad_x = max(2, int(0.008 * W))
    pad_y = max(2, int(0.01 * H))

    left = min(max(left + pad_x, 0), W - 2)
    right = min(max(right - pad_x, left + 2), W - 1)
    top = min(max(top + pad_y, 0), bottom - 2)
    bottom = min(max(bottom - pad_y, top + 2), H - 1)

    # Sanity: plot should be non-trivial size.
    if (right - left) < 100 or (bottom - top) < 100:
        raise RuntimeError(f"Detected plot box too small: left={left} right={right} top={top} bottom={bottom}")

    return PlotBox(left=left, right=right, top=top, bottom=bottom)


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


def _connected_marker_components(
    gray: np.ndarray,
    *,
    plot: PlotBox,
    dark_threshold: int,
    min_area: int,
    max_area: int,
    opening_kernel: int,
    opening_iterations: int,
) -> list[tuple[float, float, int, int, int, float, float, bool]]:
    """Return candidate components.

    Tuple: (cx, cy, area, bbox_w, bbox_h, fill_ratio, circularity, has_hole)
    where circularity = 4*pi*A / P^2 (P is boundary pixel count).
    """

    sub = gray[plot.top : plot.bottom, plot.left : plot.right]
    mask = sub < float(dark_threshold)

    if int(opening_iterations) > 0:
        k = int(opening_kernel)
        mask = ndimage.binary_opening(mask, structure=np.ones((k, k), dtype=bool), iterations=int(opening_iterations))

    lbl, n = ndimage.label(mask)
    if n <= 0:
        return []

    comps: list[tuple[float, float, int, int, float, bool]] = []
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

        fill_ratio = float(area) / float(h * w)
        # Markers tend to be reasonably filled within their bbox.
        if fill_ratio < 0.18:
            continue

        # Circularity filter: reject line segments / curve fragments.
        # Approximate perimeter by boundary pixel count.
        er = ndimage.binary_erosion(comp)
        boundary = comp & (~er)
        perim = float(int(boundary.sum()))
        if perim <= 0.0:
            continue
        circularity = float(4.0 * math.pi * float(area) / (perim * perim))
        if circularity < 0.45:
            continue

        yy, xx = np.nonzero(comp)
        cx = float(xx.mean()) + float(xs.start) + float(plot.left)
        cy = float(yy.mean()) + float(ys.start) + float(plot.top)

        has_hole = _has_enclosed_hole(comp)
        comps.append((cx, cy, area, w, h, fill_ratio, circularity, has_hole))

    comps.sort(key=lambda t: (t[0], t[1]))
    return comps


def _exclude_insets(cx: float, cy: float, *, plot: PlotBox) -> bool:
    """Return True if point is inside known inset regions (heuristic).

    Fig. 2 has two insets (top-left and bottom-right). We exclude approximate
    fractions of the plot box to avoid picking those markers.
    """

    px = (cx - plot.left) / float(plot.width())
    py = (cy - plot.top) / float(plot.height())

    # Top-left inset region.
    if (0.12 <= px <= 0.47) and (0.05 <= py <= 0.36):
        return True

    # Bottom-right inset region.
    if (0.60 <= px <= 0.95) and (0.60 <= py <= 0.92):
        return True

    return False


def _pixel_to_data(
    cx: float,
    cy: float,
    *,
    plot: PlotBox,
    xmin: float,
    xmax: float,
    ymin: float,
    ymax: float,
) -> tuple[float, float]:
    x_frac = (cx - plot.left) / float(plot.width())
    y_frac = (plot.bottom - cy) / float(plot.height())

    k = float(xmin + x_frac * (xmax - xmin))
    w = float(ymin + y_frac * (ymax - ymin))
    return k, w


def _select_points_for_ds02(
    pts: list[tuple[float, float]],
    *,
    target_n: int,
    lowk_max: float = 1.5,
    lowk_required: int = 10,
    kmax_required: float = 3.33842,
) -> list[tuple[float, float]]:
    """Deterministically downselect points to satisfy DS-02 gating intent.

    - Keeps dense low-k coverage by guaranteeing >= lowk_required points with k<=lowk_max.
    - Ensures overlap reach by including a point at/above kmax_required.
    - Uses quantile selection per region to avoid subjective cherry-picking.
    """

    if target_n < 15 or target_n > 40:
        raise ValueError("target_n must be between 15 and 40")

    pts_sorted = sorted(pts, key=lambda t: (t[0], t[1]))
    if not pts_sorted:
        return []

    low = [p for p in pts_sorted if p[0] <= lowk_max]
    mid = [p for p in pts_sorted if lowk_max < p[0] < kmax_required]
    high = [p for p in pts_sorted if p[0] >= kmax_required]

    if len(low) < lowk_required:
        raise RuntimeError(f"Insufficient low-k points: N(k<={lowk_max})={len(low)} < {lowk_required}")
    if not high:
        raise RuntimeError(f"No points satisfy overlap requirement k>={kmax_required}")

    # Allocate counts with priority to low-k.
    n_low = min(max(lowk_required, int(round(0.55 * target_n))), len(low))
    n_high = min(max(4, int(round(0.18 * target_n))), len(high))
    n_mid = max(0, target_n - n_low - n_high)
    if n_mid > len(mid):
        # Borrow from high if mid is scarce.
        deficit = n_mid - len(mid)
        n_mid = len(mid)
        n_high = min(len(high), n_high + deficit)
        # If still short, borrow from low.
        short = target_n - (n_low + n_mid + n_high)
        if short > 0:
            n_low = min(len(low), n_low + short)

    def pick_quantiles(seq: list[tuple[float, float]], n: int) -> list[tuple[float, float]]:
        if n <= 0:
            return []
        if n >= len(seq):
            return list(seq)
        out: list[tuple[float, float]] = []
        for j in range(n):
            # Evenly spaced quantiles including endpoints.
            q = 0.0 if n == 1 else (j / float(n - 1))
            i = int(round(q * (len(seq) - 1)))
            out.append(seq[i])
        # De-dup while preserving order.
        ded: list[tuple[float, float]] = []
        seen: set[tuple[float, float]] = set()
        for p in out:
            if p in seen:
                continue
            seen.add(p)
            ded.append(p)
        return ded

    chosen = pick_quantiles(low, n_low) + pick_quantiles(mid, n_mid) + pick_quantiles(high, n_high)
    chosen = sorted(chosen, key=lambda t: (t[0], t[1]))

    # Ensure we include the max-k point to maximize overlap reach.
    max_k_pt = max(pts_sorted, key=lambda t: t[0])
    if max_k_pt not in chosen:
        chosen.append(max_k_pt)
        chosen.sort(key=lambda t: (t[0], t[1]))

    # Enforce strict monotonic k by pruning near-duplicates.
    pruned: list[tuple[float, float]] = []
    last_k = -1.0
    for k, w in chosen:
        if k <= last_k + 1e-9:
            continue
        pruned.append((k, w))
        last_k = k

    # If we overshot, thin deterministically from the mid/high tail.
    while len(pruned) > 40:
        # Prefer removing points above lowk_max (preserve low-k density).
        idx = next((i for i, (k, _) in enumerate(pruned) if k > lowk_max), None)
        if idx is None:
            pruned.pop()
        else:
            pruned.pop(idx)

    # If we are still above target_n, drop from the most crowded region (mid/high).
    while len(pruned) > target_n:
        idx = next((i for i, (k, _) in enumerate(pruned) if k > lowk_max), None)
        if idx is None:
            pruned.pop()
        else:
            pruned.pop(idx)

    # Final gate checks.
    ks = [k for (k, _) in pruned]
    if not (15 <= len(pruned) <= 40):
        raise RuntimeError(f"Selection produced N={len(pruned)} points, expected 15..40")
    if sum(1 for k in ks if k <= lowk_max) < lowk_required:
        raise RuntimeError("Selection violated low-k density requirement")
    if min(ks) > 0.4 + 1e-12:
        raise RuntimeError("Selection violated min(k)<=0.4 requirement")
    if max(ks) + 1e-12 < kmax_required:
        raise RuntimeError("Selection violated overlap reach requirement")
    return pruned


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
    p.add_argument("--png", required=True, help="Input PNG containing Fig. 2")
    p.add_argument("--out-csv", required=True)

    p.add_argument("--xmin", type=float, default=0.0)
    p.add_argument("--xmax", type=float, default=4.5)
    p.add_argument("--ymin", type=float, default=0.0)
    p.add_argument("--ymax", type=float, default=2.0)

    p.add_argument("--source", default="Shammass2012_arXiv1207.3440v2_Fig2_filled_circles")
    p.add_argument("--figure", default="Fig. 2")
    p.add_argument("--notes", default="digitized from PNG; filled circles only; error bars not digitized")

    p.add_argument("--axis-dark-threshold", type=int, default=80)
    p.add_argument("--marker-dark-threshold", type=int, default=90)
    p.add_argument("--min-area", type=int, default=35)
    p.add_argument("--max-area", type=int, default=800)
    p.add_argument("--opening-kernel", type=int, default=2)
    p.add_argument("--opening-iterations", type=int, default=1)

    p.add_argument(
        "--target-n",
        type=int,
        default=25,
        help="Target number of points to write (must be 15..40, default=25)",
    )

    # De-dup tolerances in data units.
    p.add_argument("--dedup-dk", type=float, default=0.02)
    p.add_argument("--dedup-dw", type=float, default=0.02)

    args = p.parse_args(argv)

    png_path = Path(args.png)
    out_csv = Path(args.out_csv)

    img = Image.open(png_path).convert("RGB")
    rgb = np.asarray(img)
    gray = _to_gray(rgb)

    plot = _find_plot_box(gray, dark_threshold=int(args.axis_dark_threshold))

    comps = _connected_marker_components(
        gray,
        plot=plot,
        dark_threshold=int(args.marker_dark_threshold),
        min_area=int(args.min_area),
        max_area=int(args.max_area),
        opening_kernel=int(args.opening_kernel),
        opening_iterations=int(args.opening_iterations),
    )

    # Filter: exclude insets + keep filled circles.
    candidates: list[tuple[float, float]] = []
    for (cx, cy, _area, _bw, _bh, _fill, _circ, has_hole) in comps:
        if _exclude_insets(cx, cy, plot=plot):
            continue
        if has_hole:
            continue
        k, w = _pixel_to_data(
            cx,
            cy,
            plot=plot,
            xmin=float(args.xmin),
            xmax=float(args.xmax),
            ymin=float(args.ymin),
            ymax=float(args.ymax),
        )
        if not (math.isfinite(k) and math.isfinite(w)):
            continue
        # Basic hygiene in data space.
        if k < -1e-6 or w < -1e-6:
            continue
        candidates.append((max(0.0, k), max(0.0, w)))

    if len(candidates) < 5:
        raise RuntimeError(
            f"Too few filled-circle candidates found (N={len(candidates)}). "
            "Try adjusting thresholds, axis ranges, or providing a cleaner PNG render."
        )

    # Canonical ordering + de-dup (coarse), then deterministic downselect.
    candidates.sort(key=lambda t: (t[0], t[1]))
    dedup: list[tuple[float, float]] = []
    for (k, w) in candidates:
        if dedup:
            k0, w0 = dedup[-1]
            if abs(k - k0) <= float(args.dedup_dk) and abs(w - w0) <= float(args.dedup_dw):
                continue
        dedup.append((k, w))

    points = _select_points_for_ds02(dedup, target_n=int(args.target_n))

    _write_ds02_csv(
        out_csv,
        points=points,
        source=str(args.source),
        figure=str(args.figure),
        notes=str(args.notes),
    )

    ks = [k for (k, _) in points]
    n_lowk = sum(1 for k in ks if k <= 1.5)

    print("DS-02 PNG digitization summary:")
    print(f"  png: {png_path}")
    print(f"  plot_box: left={plot.left} right={plot.right} top={plot.top} bottom={plot.bottom}")
    print(f"  axis_ranges: x=[{args.xmin:g},{args.xmax:g}] y=[{args.ymin:g},{args.ymax:g}]")
    print(f"  points: N={len(points)} (target_n={int(args.target_n)})")
    print(f"  k range: [{min(ks):.6g}, {max(ks):.6g}] um^-1")
    print(f"  low-k count: N(k<=1.5)={n_lowk}")
    print(f"  wrote: {out_csv}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
