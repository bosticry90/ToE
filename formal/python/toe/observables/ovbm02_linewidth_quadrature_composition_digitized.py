"""OV-BM-02 (numeric): minimal digitized linewidth vs peak-density dataset (computed lock).

Purpose
- Provide a smallest-acceptable numeric digitization target for OV-BM-02 under BM-DIG-01.

Scope / limits
- Benchmark-only numeric ingestion: no validation claim.
- No fitting, no regime averaging, no continuity claim, no cross-observable inference.

Design
- Deterministic: digitizes markers from a pinned PNG render of the Stenger (1999) PDF page.
- Writes a frozen CSV + JSON metadata wrapper under formal/external_evidence.

Digitization target (BM-DIG-01 compliant)
- Paper: Stenger et al. (1999)
- Figure: Fig. 3 (panel b)
- Series: triangles_only (one series only)
- Axes:
  - x: Peak Density [1e14 cm^-3], range [0, 5]
  - y: Width [kHz], range [0, 4]

Note
- Fig. 3(b) also includes model component curves; this minimal pass digitizes only one
  experimental series to stress-test numeric ingestion determinism.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import math
from pathlib import Path
from typing import Any

import numpy as np
from PIL import Image
from scipy import ndimage


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _to_gray(img: np.ndarray) -> np.ndarray:
    if img.ndim != 3 or img.shape[2] != 3:
        raise ValueError("expected RGB image")
    r = img[:, :, 0].astype(np.float32)
    g = img[:, :, 1].astype(np.float32)
    b = img[:, :, 2].astype(np.float32)
    return (0.2126 * r + 0.7152 * g + 0.0722 * b).astype(np.float32)


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


def _find_plot_box(gray: np.ndarray, *, dark_threshold: int = 100) -> PlotBox:
    """Heuristically locate the plot axes box inside a cropped panel image."""

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

    # Estimate bounds from the axis lines.
    row = dark[y_axis, :]
    xs = np.where(row)[0]
    if xs.size == 0:
        raise RuntimeError("Could not detect x-axis line")
    right = int(np.percentile(xs, 99.0))

    col = dark[:, x_axis]
    ys = np.where(col)[0]
    if ys.size == 0:
        raise RuntimeError("Could not detect y-axis line")
    top = int(np.percentile(ys, 1.0))

    left = int(x_axis + 1)
    bottom = int(y_axis - 1)

    # Pad inward to avoid axis ink / labels.
    pad_x = max(2, int(0.008 * W))
    pad_y = max(2, int(0.01 * H))

    left = min(max(left + pad_x, 0), W - 2)
    right = min(max(right - pad_x, left + 2), W - 1)
    top = min(max(top + pad_y, 0), bottom - 2)
    bottom = min(max(bottom - pad_y, top + 2), H - 1)

    if (right - left) < 200 or (bottom - top) < 200:
        raise RuntimeError(f"Detected plot box too small: left={left} right={right} top={top} bottom={bottom}")

    return PlotBox(left=left, right=right, top=top, bottom=bottom)


def _extract_triangle_markers(
    rgb: np.ndarray,
    *,
    panel_crop: tuple[int, int, int, int],
    plot_dark_threshold: int = 140,
) -> tuple[PlotBox, list[tuple[float, float]]]:
    """Extract triangle-marker centers from the specified panel crop.

    Returns
    - plot box in full-image coordinates
    - list of (cx, cy) pixel centers in full-image coordinates

    Heuristic rationale
    - On the Stenger (1999) Fig. 3(b) page render, triangles have a smaller
      connected-component area than the circles; we use an area gate to select
      a single series (triangles_only).
    """

    x0, y0, x1, y1 = (int(panel_crop[0]), int(panel_crop[1]), int(panel_crop[2]), int(panel_crop[3]))
    if x0 < 0 or y0 < 0 or x1 <= x0 or y1 <= y0:
        raise ValueError("invalid panel_crop")

    panel = rgb[y0:y1, x0:x1]
    gray_panel = _to_gray(panel)
    plot_local = _find_plot_box(gray_panel, dark_threshold=100)

    # Convert plot box to full-image coordinates.
    plot = PlotBox(
        left=int(plot_local.left + x0),
        right=int(plot_local.right + x0),
        top=int(plot_local.top + y0),
        bottom=int(plot_local.bottom + y0),
    )

    gray = _to_gray(rgb)
    sub = gray[plot.top : plot.bottom, plot.left : plot.right]

    mask = sub < float(plot_dark_threshold)
    # Light opening to reduce single-pixel noise.
    mask = ndimage.binary_opening(mask, structure=np.ones((2, 2), dtype=bool), iterations=1)

    lbl, n = ndimage.label(mask)
    if n <= 0:
        return plot, []

    pts: list[tuple[float, float]] = []
    slices = ndimage.find_objects(lbl)
    for idx, sl in enumerate(slices, start=1):
        if sl is None:
            continue
        ys, xs = sl
        comp = lbl[ys, xs] == idx

        area = int(comp.sum())
        # Triangle markers (filled) are smaller on the canonical render.
        if area < 40 or area > 50:
            continue

        h = int(ys.stop - ys.start)
        w = int(xs.stop - xs.start)
        if h <= 1 or w <= 1:
            continue

        ar = float(w) / float(h)
        if ar < 0.75 or ar > 1.35:
            continue

        fill_ratio = float(area) / float(h * w)
        if fill_ratio < 0.12:
            continue

        er = ndimage.binary_erosion(comp)
        boundary = comp & (~er)
        perim = float(int(boundary.sum()))
        if perim <= 0.0:
            continue

        circularity = float(4.0 * math.pi * float(area) / (perim * perim))
        # Coarse filter: reject line fragments.
        if circularity < 0.50 or circularity > 1.20:
            continue

        yy, xx = np.nonzero(comp)
        cx = float(xx.mean()) + float(xs.start) + float(plot.left)
        cy = float(yy.mean()) + float(ys.start) + float(plot.top)
        pts.append((cx, cy))

    pts.sort(key=lambda t: (t[0], t[1]))
    return plot, pts


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
    x = float(xmin) + (float(cx) - float(plot.left)) / float(plot.width()) * (float(xmax) - float(xmin))
    y = float(ymax) - (float(cy) - float(plot.top)) / float(plot.height()) * (float(ymax) - float(ymin))
    return x, y


def _digitized_points_from_png(png_path: Path) -> list[dict[str, float]]:
    rgb = np.array(Image.open(png_path).convert("RGB"))
    H, W, _ = rgb.shape

    # Page layout: Fig. 3 has panels a/b/c; panel b occupies the middle band.
    panel_b_crop = (0, int(0.28 * H), W, int(0.62 * H))

    plot, pts = _extract_triangle_markers(rgb, panel_crop=panel_b_crop)
    if len(pts) != 8:
        raise RuntimeError(
            f"Expected exactly 8 triangle markers for OV-BM-02N (triangles_only), got N={len(pts)}"
        )

    # Pixel-space uniqueness guard (avoid accidental double-detection).
    rounded_pixels = {(int(round(cx)), int(round(cy))) for (cx, cy) in pts}
    if len(rounded_pixels) != 8:
        raise RuntimeError("Non-unique triangle marker detections (pixel-space collision)")

    # Axes ranges extracted from the PDF text layer for Fig. 3(b).
    xmin, xmax = 0.0, 5.0
    ymin, ymax = 0.0, 4.0

    out: list[dict[str, float]] = []
    for cx, cy in pts:
        x, y = _pixel_to_data(cx, cy, plot=plot, xmin=xmin, xmax=xmax, ymin=ymin, ymax=ymax)
        out.append(
            {
                "peak_density_1e14_cm3": float(x),
                "width_khz": float(y),
            }
        )

    out.sort(key=lambda d: (float(d["peak_density_1e14_cm3"]), float(d["width_khz"])))

    # Data-space uniqueness (rounded) guard.
    rounded_data = {(round(float(d["peak_density_1e14_cm3"]), 6), round(float(d["width_khz"]), 6)) for d in out}
    if len(rounded_data) != 8:
        raise RuntimeError("Non-unique digitized points (data-space collision)")

    return out


@dataclass(frozen=True)
class OVBM02DigitizedLinewidthDatasetRecord:
    schema: str
    digitization_id: str
    date: str

    observable_id: str

    source: dict[str, Any]
    dataset: dict[str, Any]
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "digitization_id": str(self.digitization_id),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "source": dict(self.source),
            "dataset": dict(self.dataset),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def _render_csv_text(points: list[dict[str, float]]) -> str:
    header = ["peak_density_1e14_cm3", "width_khz"]

    def f(x: float) -> str:
        return ("%.6g" % float(x))

    lines = [",".join(header)]
    for p in points:
        lines.append(",".join([f(float(p[h])) for h in header]))
    return "\n".join(lines) + "\n"


def ovbm02_digitized_linewidth_dataset_record(*, date: str = "2026-01-24") -> OVBM02DigitizedLinewidthDatasetRecord:
    repo_root = _find_repo_root(Path(__file__))

    pdf_rel = "formal/external_evidence/bec_bragg_stenger_1999/9901109v1.pdf"
    png_rel = "formal/external_evidence/bec_bragg_stenger_1999/Fig3_page4_z4.png"

    pdf_sha = _sha256_file(repo_root / pdf_rel)
    png_sha = _sha256_file(repo_root / png_rel)

    points = _digitized_points_from_png(repo_root / png_rel)
    csv_text = _render_csv_text(points)

    csv_rel = "formal/external_evidence/bec_bragg_stenger_1999/ovbm02_digitization/linewidth_vs_peak_density_triangles.csv"
    meta_rel = "formal/external_evidence/bec_bragg_stenger_1999/ovbm02_digitization/linewidth_vs_peak_density_triangles.metadata.json"

    dataset = {
        "csv_relpath": csv_rel,
        "metadata_relpath": meta_rel,
        "row_count": int(len(points)),
        "columns": [
            {"name": "peak_density_1e14_cm3", "unit": "1e14 cm^-3", "dtype": "float"},
            {"name": "width_khz", "unit": "kHz", "dtype": "float"},
        ],
        "csv_sha256": _sha256_text(csv_text),
    }

    source = {
        "citation": "Stenger et al. (1999) — Bragg spectroscopy of a Bose–Einstein condensate",
        "arxiv_pdf_relpath": pdf_rel,
        "arxiv_pdf_sha256": pdf_sha,
        "render_png_relpath": png_rel,
        "render_png_sha256": png_sha,
        "figure": "Fig. 3 (panel b)",
        "series": "triangles_only",
        "digitization_method": "deterministic_marker_extraction_from_pinned_png",
        "axis_ranges": {
            "x": {"name": "Peak Density", "unit": "1e14 cm^-3", "min": 0.0, "max": 5.0},
            "y": {"name": "Width", "unit": "kHz", "min": 0.0, "max": 4.0},
        },
        "notes": "Smallest acceptable target under BM-DIG-01; digitizes one experimental series only; values are approximate and intended for pipeline determinism checks only.",
    }

    scope_limits = [
        "benchmark_only_numeric",
        "no_curve_fitting",
        "no_regime_averaging",
        "no_continuity_claim",
        "no_cross_observable_inference",
        "non_decisive_by_design",
    ]

    return OVBM02DigitizedLinewidthDatasetRecord(
        schema="OV-BM-02_linewidth_quadrature_composition_digitized/v1",
        digitization_id="OV-BM-02N",
        date=str(date),
        observable_id="OV-BM-02",
        source=source,
        dataset=dataset,
        scope_limits=scope_limits,
    )


def write_ovbm02_digitized_artifacts(*, date: str = "2026-01-24") -> dict[str, Path]:
    repo_root = _find_repo_root(Path(__file__))
    rec = ovbm02_digitized_linewidth_dataset_record(date=str(date))

    png_path = repo_root / rec.source["render_png_relpath"]
    if not png_path.exists():
        raise FileNotFoundError(f"Missing pinned PNG render: {png_path}")

    points = _digitized_points_from_png(png_path)
    csv_text = _render_csv_text(points)

    csv_path = repo_root / rec.dataset["csv_relpath"]
    meta_path = repo_root / rec.dataset["metadata_relpath"]

    csv_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path.parent.mkdir(parents=True, exist_ok=True)

    csv_path.write_text(csv_text, encoding="utf-8", newline="\n")

    meta_payload = {
        "schema": "OV-BM-02_digitized_dataset_metadata/v1",
        "date": rec.date,
        "observable_id": rec.observable_id,
        "digitization_id": rec.digitization_id,
        "source": rec.source,
        "dataset": rec.dataset,
        "scope_limits": rec.scope_limits,
        "record_fingerprint": rec.fingerprint(),
    }
    meta_path.write_text(json.dumps(meta_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    return {"csv": csv_path, "metadata": meta_path}


def render_ovbm02_digitized_lock_markdown(record: OVBM02DigitizedLinewidthDatasetRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-BM-02N — Digitized benchmark: linewidth vs peak density (computed)\n\n"
        "Scope / limits\n"
        "- Benchmark-only numeric ingestion; no physics validation claim\n"
        "- No fitting; no regime averaging; no continuity claim; no cross-observable inference\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovbm02_digitized_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))

    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "benchmarks"
            / "OV-BM-02_linewidth_quadrature_composition_digitized.md"
        )

    rec = ovbm02_digitized_linewidth_dataset_record(date=str(date))

    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbm02_digitized_lock_markdown(rec), encoding="utf-8")
    return out
