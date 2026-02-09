"""OV-SND-01N: minimal digitized anchor dataset from sound propagation (computed lock).

Digitization target
- Source PDF: arXiv:9711224v1 (Kavoulakis & Pethick, 1997)
- Figure: Fig. 2 (distance vs time)
- Series: squares (low-amplitude pulses)
- Axes:
  - x: Time [ms], range [0, 80]
  - y: Distance from center [μm], range [0, 200]

Purpose
- Provide a deterministic, frozen external dataset artifact (CSV + metadata) as a
  second non-Bragg anchor.

Scope / limits
- Benchmark/anchor ingestion only; no ToE validation claim.
- No fitting: we digitize points only; we do not infer c beyond acknowledging
  that the slope is interpretable as a speed.
- No continuity/averaging across regimes.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
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


def _to_gray(rgb: np.ndarray) -> np.ndarray:
    r = rgb[:, :, 0].astype(np.float32)
    g = rgb[:, :, 1].astype(np.float32)
    b = rgb[:, :, 2].astype(np.float32)
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
    H, W = gray.shape
    dark = gray < float(dark_threshold)

    # x-axis: strongest horizontal dark density in lower half
    y0 = int(0.55 * H)
    row_scores = dark[y0:, :].mean(axis=1)
    y_axis = int(y0 + int(np.argmax(row_scores)))

    # y-axis: strongest vertical dark density in left half
    x1 = int(0.45 * W)
    col_scores = dark[:, :x1].mean(axis=0)
    x_axis = int(np.argmax(col_scores))

    xs = np.where(dark[y_axis, :])[0]
    ys = np.where(dark[:, x_axis])[0]
    if xs.size == 0 or ys.size == 0:
        raise RuntimeError("Could not detect axes")

    right = int(np.percentile(xs, 99.0))
    top = int(np.percentile(ys, 1.0))
    left = int(x_axis + 1)
    bottom = int(y_axis - 1)

    pad_x = max(2, int(0.01 * W))
    pad_y = max(2, int(0.01 * H))

    left = min(max(left + pad_x, 0), W - 2)
    right = min(max(right - pad_x, left + 2), W - 1)
    top = min(max(top + pad_y, 0), bottom - 2)
    bottom = min(max(bottom - pad_y, top + 2), H - 1)

    if (right - left) < 200 or (bottom - top) < 200:
        raise RuntimeError("Detected plot box too small")

    return PlotBox(left=left, right=right, top=top, bottom=bottom)


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
    gray = _to_gray(rgb)

    plot = _find_plot_box(gray, dark_threshold=100)

    sub = gray[plot.top : plot.bottom, plot.left : plot.right]
    mask = sub < 140
    mask = ndimage.binary_opening(mask, structure=np.ones((2, 2), dtype=bool), iterations=1)

    lbl, n = ndimage.label(mask)
    if n <= 0:
        raise RuntimeError("No components detected")

    # Empirically stable selector on the pinned render:
    # - squares have connected-component area==43 and bounding box 12x11.
    pts: list[tuple[float, float]] = []
    for idx, sl in enumerate(ndimage.find_objects(lbl), start=1):
        if sl is None:
            continue
        ys, xs = sl
        comp = lbl[ys, xs] == idx

        area = int(comp.sum())
        h = int(ys.stop - ys.start)
        w = int(xs.stop - xs.start)

        if not (area == 43 and w == 12 and h == 11):
            continue

        yy, xx = np.nonzero(comp)
        cx = float(xx.mean()) + float(xs.start) + float(plot.left)
        cy = float(yy.mean()) + float(ys.start) + float(plot.top)
        pts.append((cx, cy))

    pts.sort(key=lambda t: (t[0], t[1]))

    if len(pts) != 11:
        raise RuntimeError(f"Expected exactly 11 square markers, got N={len(pts)}")

    rounded_pixels = {(int(round(cx)), int(round(cy))) for (cx, cy) in pts}
    if len(rounded_pixels) != 11:
        raise RuntimeError("Non-unique marker detections (pixel-space collision)")

    xmin, xmax = 0.0, 80.0
    ymin, ymax = 0.0, 200.0

    out: list[dict[str, float]] = []
    for cx, cy in pts:
        t_ms, dist_um = _pixel_to_data(cx, cy, plot=plot, xmin=xmin, xmax=xmax, ymin=ymin, ymax=ymax)
        out.append({"time_ms": float(t_ms), "distance_um": float(dist_um)})

    out.sort(key=lambda d: (float(d["time_ms"]), float(d["distance_um"])))

    rounded_data = {(round(float(d["time_ms"]), 6), round(float(d["distance_um"]), 6)) for d in out}
    if len(rounded_data) != 11:
        raise RuntimeError("Non-unique digitized points (data-space collision)")

    return out


def _render_csv_text(points: list[dict[str, float]]) -> str:
    header = ["time_ms", "distance_um"]

    def f(x: float) -> str:
        return ("%.6g" % float(x))

    lines = [",".join(header)]
    for p in points:
        lines.append(",".join([f(float(p[h])) for h in header]))
    return "\n".join(lines) + "\n"


@dataclass(frozen=True)
class OVSND01DigitizedPropagationDatasetRecord:
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


def ovsnd01_digitized_propagation_dataset_record(*, date: str = "2026-01-24") -> OVSND01DigitizedPropagationDatasetRecord:
    repo_root = _find_repo_root(Path(__file__))

    pdf_rel = "formal/external_evidence/bec_sound_andrews_1997/9711224v1.pdf"
    png_rel = "formal/external_evidence/bec_sound_andrews_1997/fig2_region_page4_z4.png"

    pdf_sha = _sha256_file(repo_root / pdf_rel)
    png_sha = _sha256_file(repo_root / png_rel)

    points = _digitized_points_from_png(repo_root / png_rel)
    csv_text = _render_csv_text(points)

    csv_rel = "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares.csv"
    meta_rel = "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares.metadata.json"

    dataset = {
        "csv_relpath": csv_rel,
        "metadata_relpath": meta_rel,
        "row_count": int(len(points)),
        "columns": [
            {"name": "time_ms", "unit": "ms", "dtype": "float"},
            {"name": "distance_um", "unit": "um", "dtype": "float"},
        ],
        "csv_sha256": _sha256_text(csv_text),
    }

    source = {
        "citation": "Kavoulakis & Pethick (1997), arXiv:9711224v1 — Sound Propagation in Elongated Bose-Einstein Condensed Clouds",
        "arxiv_pdf_relpath": pdf_rel,
        "arxiv_pdf_sha256": pdf_sha,
        "digitization_png_relpath": png_rel,
        "digitization_png_sha256": png_sha,
        "figure": "Fig. 2",
        "series": "squares_low_amplitude",
        "axis_ranges": {
            "x": {"name": "Time", "unit": "ms", "min": 0.0, "max": 80.0},
            "y": {"name": "Distance", "unit": "um", "min": 0.0, "max": 200.0},
        },
        "digitization_method": "deterministic_marker_extraction_from_pinned_png",
        "notes": "Digitizes squares (low-amplitude pulses) only; no fitting performed; slope is interpretable as speed but not inferred here.",
    }

    scope_limits = [
        "anchor_numeric_only",
        "no_fitting",
        "no_parameter_inference",
        "no_continuity_claim",
        "no_cross_regime_averaging",
        "non_decisive_by_design",
    ]

    return OVSND01DigitizedPropagationDatasetRecord(
        schema="OV-SND-01_sound_propagation_distance_time_digitized/v1",
        digitization_id="OV-SND-01N",
        date=str(date),
        observable_id="OV-SND-01",
        source=source,
        dataset=dataset,
        scope_limits=scope_limits,
    )


def write_ovsnd01_digitized_artifacts(*, date: str = "2026-01-24") -> dict[str, Path]:
    repo_root = _find_repo_root(Path(__file__))
    rec = ovsnd01_digitized_propagation_dataset_record(date=str(date))

    png_path = repo_root / rec.source["digitization_png_relpath"]
    if not png_path.exists():
        raise FileNotFoundError(f"Missing pinned digitization PNG: {png_path}")

    points = _digitized_points_from_png(png_path)
    csv_text = _render_csv_text(points)

    csv_path = repo_root / rec.dataset["csv_relpath"]
    meta_path = repo_root / rec.dataset["metadata_relpath"]

    csv_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path.parent.mkdir(parents=True, exist_ok=True)

    csv_path.write_text(csv_text, encoding="utf-8", newline="\n")

    meta_payload = {
        "schema": "OV-SND-01_digitized_dataset_metadata/v1",
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


def render_ovsnd01_digitized_lock_markdown(record: OVSND01DigitizedPropagationDatasetRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SND-01N — Digitized anchor: sound propagation distance vs time (computed)\n\n"
        "Scope / limits\n"
        "- Anchor numeric ingestion only; no physics validation claim\n"
        "- No fitting; no parameter inference; no continuity/averaging across regimes\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsnd01_digitized_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-SND-01_sound_propagation_distance_time_digitized.md"
        )

    rec = ovsnd01_digitized_propagation_dataset_record(date=str(date))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsnd01_digitized_lock_markdown(rec), encoding="utf-8")
    return out
