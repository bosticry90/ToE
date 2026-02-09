"""OV-SND-01N2: split square markers into two deterministic series from a pinned Andrews 1997 propagation plot.

Why this exists
- OV-SND-01N digitizes the *squares* series in Fig. 2 (distance vs time).
- The paper context suggests multiple pulse/condition series may exist.
- OV-SND-04 requires >=2 speed conditions to form >=2 mapped (c, n0) pairs.

Governance stance
- Bookkeeping only; no physics claim.
- Deterministic: if a second series cannot be separated by the pinned rule, this record
    remains BLOCKED (no fabrication, no manual clicking).

Digitization strategy (v1, bounded)
- Use the pinned Andrews page render: formal/external_evidence/bec_sound_andrews_1997/page4_z4.png
- Hardcode a crop box in image coordinates to isolate the propagation plot.
- Hardcode the plot box (axes interior) within that crop.
- Extract *all* square-marker centroids using the same pinned component signature as OV-SND-01N.
- Split into two series via a pinned rule: "largest_x_gap" on sorted time values.

Stop condition
- If the split produces too few points in either series or the largest gap is not significant,
    remain BLOCKED (this is the governance guardrail).
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

from formal.python.toe.observables.ovsnd01_sound_propagation_distance_time_digitized import (
    PlotBox,
    _pixel_to_data,
    _to_gray,
)


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


def _ols_through_origin(t: np.ndarray, y: np.ndarray) -> dict[str, float]:
    # y ≈ c*t
    denom = float(np.dot(t, t))
    if denom <= 0:
        raise ValueError("Degenerate time vector")

    c = float(np.dot(t, y) / denom)
    resid = y - c * t

    n = int(t.size)
    dof = n - 1
    s2 = float(np.dot(resid, resid) / float(dof)) if dof > 0 else float("nan")
    se_c = float(np.sqrt(s2 / denom))

    return {
        "c_um_per_ms": float(c),
        "se_um_per_ms": float(se_c),
        "n": float(n),
        "dof": float(dof),
        "residual_rms_um": float(np.sqrt(np.mean(resid**2))),
    }


def _rows_preview(points: list[dict[str, float]], *, n: int = 6) -> list[dict[str, float]]:
    out: list[dict[str, float]] = []
    for p in points[: int(n)]:
        out.append({"time_ms": float(round(float(p["time_ms"]), 6)), "distance_um": float(round(float(p["distance_um"]), 6))})
    return out


# Pinned crop/plot boxes for the pinned render.
# These were derived by a deterministic probe and then hardcoded to eliminate drift.
_PINNED_PAGE_PNG_REL = "formal/external_evidence/bec_sound_andrews_1997/page4_z4.png"
_PINNED_CROP_BOX_X0Y0X1Y1 = (1121, 1143, 2440, 1762)
_PINNED_PLOT_BOX_LRTB = (88, 1101, 11, 591)

# Pinned marker extraction parameters.
_THRESHOLD_DARK_LT = 140
_OPENING_STRUCTURE = (2, 2)
_OPENING_ITERATIONS = 1

# Pinned squares signature (OV-SND-01N).
_SQUARES_SIG = (43, 12, 11)

# Split rule parameters (v1).
_SPLIT_RULE_ID = "largest_x_gap_v1"
_MIN_POINTS_PER_SERIES = 6
_MIN_LARGEST_GAP_MS = 6.0


def _extract_square_points_from_pinned_page(png_path: Path) -> tuple[list[dict[str, float]] | None, dict[str, Any]]:
    rgb = np.array(Image.open(png_path).convert("RGB"))
    H, W, _ = rgb.shape

    x0, y0, x1, y1 = _PINNED_CROP_BOX_X0Y0X1Y1
    if not (0 <= x0 < x1 <= W and 0 <= y0 < y1 <= H):
        return None, {"reason": "invalid_hardcoded_crop_box", "image_shape": [int(H), int(W)], "crop_box": [x0, y0, x1, y1]}

    crop = rgb[y0:y1, x0:x1]
    gray = _to_gray(crop)

    left, right, top, bottom = _PINNED_PLOT_BOX_LRTB
    plot = PlotBox(left=int(left), right=int(right), top=int(top), bottom=int(bottom))
    if plot.left < 0 or plot.top < 0 or plot.right > gray.shape[1] or plot.bottom > gray.shape[0]:
        return None, {"reason": "invalid_hardcoded_plot_box", "crop_shape": [int(gray.shape[0]), int(gray.shape[1])], "plot_box": plot.__dict__}

    sub = gray[plot.top : plot.bottom, plot.left : plot.right]
    mask = sub < float(_THRESHOLD_DARK_LT)
    mask = ndimage.binary_opening(
        mask,
        structure=np.ones(_OPENING_STRUCTURE, dtype=bool),
        iterations=int(_OPENING_ITERATIONS),
    )

    lbl, n = ndimage.label(mask)
    if n <= 0:
        return None, {"reason": "no_components_detected", "plot": plot.__dict__}

    pts_px: list[tuple[float, float]] = []
    for idx, sl in enumerate(ndimage.find_objects(lbl), start=1):
        if sl is None:
            continue
        ys, xs = sl
        comp = lbl[ys, xs] == idx

        area = int(comp.sum())
        h = int(ys.stop - ys.start)
        w = int(xs.stop - xs.start)

        if (area, w, h) != _SQUARES_SIG:
            continue

        yy, xx = np.nonzero(comp)
        cx = float(xx.mean()) + float(xs.start) + float(plot.left)
        cy = float(yy.mean()) + float(ys.start) + float(plot.top)
        pts_px.append((cx, cy))

    pts_px.sort(key=lambda t: (t[0], t[1]))

    rounded_pixels = {(int(round(cx)), int(round(cy))) for (cx, cy) in pts_px}
    if len(rounded_pixels) != len(pts_px):
        return None, {"reason": "non_unique_marker_detections", "row_count": int(len(pts_px))}

    xmin, xmax = 0.0, 80.0
    ymin, ymax = 0.0, 200.0

    out: list[dict[str, float]] = []
    for cx, cy in pts_px:
        t_ms, dist_um = _pixel_to_data(cx, cy, plot=plot, xmin=xmin, xmax=xmax, ymin=ymin, ymax=ymax)
        out.append({"time_ms": float(t_ms), "distance_um": float(dist_um)})

    out.sort(key=lambda d: (float(d["time_ms"]), float(d["distance_um"])))

    rounded_data = {(round(float(d["time_ms"]), 6), round(float(d["distance_um"]), 6)) for d in out}
    if len(rounded_data) != len(out):
        return None, {"reason": "non_unique_digitized_points", "row_count": int(len(out))}

    report: dict[str, Any] = {
        "image_relpath": _PINNED_PAGE_PNG_REL,
        "hardcoded_crop_box": {"x0": int(x0), "y0": int(y0), "x1": int(x1), "y1": int(y1)},
        "hardcoded_plot_box": {"left": int(plot.left), "right": int(plot.right), "top": int(plot.top), "bottom": int(plot.bottom)},
        "threshold": {"dark_lt": int(_THRESHOLD_DARK_LT)},
        "morphology": {"binary_opening": {"structure": list(_OPENING_STRUCTURE), "iterations": int(_OPENING_ITERATIONS)}},
        "marker_signature": {"area": int(_SQUARES_SIG[0]), "w": int(_SQUARES_SIG[1]), "h": int(_SQUARES_SIG[2])},
        "row_count": int(len(out)),
    }

    return out, report


def _split_by_largest_x_gap(points: list[dict[str, float]]) -> tuple[list[dict[str, float]] | None, list[dict[str, float]] | None, dict[str, Any]]:
    if len(points) < (2 * int(_MIN_POINTS_PER_SERIES) + 1):
        return None, None, {"reason": "insufficient_points_for_split", "row_count": int(len(points))}

    pts = sorted(points, key=lambda d: (float(d["time_ms"]), float(d["distance_um"])))
    t = np.asarray([float(p["time_ms"]) for p in pts], dtype=float)
    if t.size < 3:
        return None, None, {"reason": "insufficient_points_for_split", "row_count": int(len(points))}

    gaps = np.diff(t)
    if gaps.size <= 0:
        return None, None, {"reason": "insufficient_points_for_split", "row_count": int(len(points))}

    split_idx = int(np.argmax(gaps))
    max_gap = float(gaps[split_idx])

    report: dict[str, Any] = {
        "rule_id": _SPLIT_RULE_ID,
        "largest_gap_ms": float(max_gap),
        "gap_index": int(split_idx),
        "min_largest_gap_ms": float(_MIN_LARGEST_GAP_MS),
    }

    if not (max_gap >= float(_MIN_LARGEST_GAP_MS)):
        report["reason"] = "largest_gap_too_small"
        return None, None, report

    a = pts[: split_idx + 1]
    b = pts[split_idx + 1 :]

    report["seriesA_count"] = int(len(a))
    report["seriesB_count"] = int(len(b))

    if len(a) < int(_MIN_POINTS_PER_SERIES) or len(b) < int(_MIN_POINTS_PER_SERIES):
        report["reason"] = "series_split_too_imbalanced"
        return None, None, report

    return a, b, report


def _render_csv_text(points: list[dict[str, float]]) -> str:
    header = ["time_ms", "distance_um"]

    def f(x: float) -> str:
        return ("%.6g" % float(x))

    lines = [",".join(header)]
    for p in points:
        lines.append(",".join([f(float(p[h])) for h in header]))
    return "\n".join(lines) + "\n"


@dataclass(frozen=True)
class OVSND01N2DigitizedPropagationDatasetRecord:
    schema: str
    digitization_id: str
    date: str

    observable_id: str

    status: dict[str, Any]
    source: dict[str, Any]
    dataset: dict[str, Any] | None
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "digitization_id": str(self.digitization_id),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "status": dict(self.status),
            "source": dict(self.source),
            "dataset": None if self.dataset is None else dict(self.dataset),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsnd01n2_digitized_propagation_dataset_record(*, date: str = "2026-01-24") -> OVSND01N2DigitizedPropagationDatasetRecord:
    repo_root = _find_repo_root(Path(__file__))

    pdf_rel = "formal/external_evidence/bec_sound_andrews_1997/9711224v1.pdf"
    png_rel = _PINNED_PAGE_PNG_REL

    pdf_path = repo_root / pdf_rel
    png_path = repo_root / png_rel

    blockers: list[str] = []
    if not pdf_path.exists():
        blockers.append("missing_pinned_pdf")
    if not png_path.exists():
        blockers.append("missing_pinned_png")

    dataset: dict[str, Any] | None = None
    extraction: dict[str, Any] | None = None
    if not blockers:
        pts_all, report = _extract_square_points_from_pinned_page(png_path)
        extraction = dict(report)
        if pts_all is None:
            blockers.append("square_markers_not_detectable")
        else:
            a, b, split_report = _split_by_largest_x_gap(pts_all)
            extraction["split"] = dict(split_report)
            if a is None or b is None:
                blockers.append("second_series_not_separable")
            else:
                csv_text_a = _render_csv_text(a)
                csv_text_b = _render_csv_text(b)

                csv_rel_a = "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares_seriesA.csv"
                csv_rel_b = "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares_seriesB.csv"
                meta_rel = "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares_series_split.metadata.json"

                t_a = np.asarray([float(p["time_ms"]) for p in a], dtype=float)
                y_a = np.asarray([float(p["distance_um"]) for p in a], dtype=float)
                t_b = np.asarray([float(p["time_ms"]) for p in b], dtype=float)
                y_b = np.asarray([float(p["distance_um"]) for p in b], dtype=float)
                fit_a = _ols_through_origin(t_a, y_a)
                fit_b = _ols_through_origin(t_b, y_b)

                dataset = {
                    "metadata_relpath": meta_rel,
                    "columns": [
                        {"name": "time_ms", "unit": "ms", "dtype": "float"},
                        {"name": "distance_um", "unit": "um", "dtype": "float"},
                    ],
                    "seriesA": {
                        "label": "seriesA",
                        "csv_relpath": csv_rel_a,
                        "csv_sha256": _sha256_text(csv_text_a),
                        "row_count": int(len(a)),
                        "rows_preview": _rows_preview(a, n=6),
                        "slope_fit": fit_a,
                    },
                    "seriesB": {
                        "label": "seriesB",
                        "csv_relpath": csv_rel_b,
                        "csv_sha256": _sha256_text(csv_text_b),
                        "row_count": int(len(b)),
                        "rows_preview": _rows_preview(b, n=6),
                        "slope_fit": fit_b,
                    },
                    "split_rule": {
                        "rule_id": _SPLIT_RULE_ID,
                        "min_points_per_series": int(_MIN_POINTS_PER_SERIES),
                        "min_largest_gap_ms": float(_MIN_LARGEST_GAP_MS),
                        "gap_index": int(extraction["split"].get("gap_index")),
                        "largest_gap_ms": float(extraction["split"].get("largest_gap_ms")),
                    },
                }

    status = {"blocked": bool(len(blockers) > 0), "blockers": list(blockers)}

    source = {
        "citation": "Kavoulakis & Pethick (1997), arXiv:9711224v1 — Sound Propagation in Elongated Bose-Einstein Condensed Clouds",
        "arxiv_pdf_relpath": pdf_rel,
        "arxiv_pdf_sha256": _sha256_file(pdf_path) if pdf_path.exists() else None,
        "figure_png_relpath": png_rel,
        "figure_png_sha256": _sha256_file(png_path) if png_path.exists() else None,
        "extraction": extraction,
    }

    scope_limits = [
        "bookkeeping_only",
        "no_physics_claim",
        "no_manual_clicking",
        "no_fitting",
        "non_decisive_by_design",
    ]

    return OVSND01N2DigitizedPropagationDatasetRecord(
        schema="OV-SND-01N2_sound_propagation_distance_time_digitized/v2",
        digitization_id="OV-SND-01N2",
        date=str(date),
        observable_id="OV-SND-01N2",
        status=status,
        source=source,
        dataset=dataset,
        scope_limits=scope_limits,
    )


def render_ovsnd01n2_lock_markdown(record: OVSND01N2DigitizedPropagationDatasetRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SND-01N2 — Propagation series split (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping only; no physics claim\n"
        "- Deterministic: remains blocked unless the pinned split rule produces two series with sufficient support\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsnd01n2_digitized_artifacts(*, date: str = "2026-01-24") -> dict[str, Path] | None:
    """Write CSVs+metadata if the split is unblocked.

    Returns None if blocked.
    """

    repo_root = _find_repo_root(Path(__file__))
    rec = ovsnd01n2_digitized_propagation_dataset_record(date=str(date))
    if bool(rec.status.get("blocked")) or rec.dataset is None:
        return None

    # Recompute points (deterministic) and write.
    png_path = repo_root / rec.source["figure_png_relpath"]
    pts_all, _report = _extract_square_points_from_pinned_page(png_path)
    if pts_all is None:
        return None
    a, b, _split = _split_by_largest_x_gap(pts_all)
    if a is None or b is None:
        return None

    csv_text_a = _render_csv_text(a)
    csv_text_b = _render_csv_text(b)

    csv_path_a = repo_root / str(rec.dataset["seriesA"]["csv_relpath"])
    csv_path_b = repo_root / str(rec.dataset["seriesB"]["csv_relpath"])
    meta_path = repo_root / str(rec.dataset["metadata_relpath"])

    csv_path_a.parent.mkdir(parents=True, exist_ok=True)
    csv_path_b.parent.mkdir(parents=True, exist_ok=True)
    meta_path.parent.mkdir(parents=True, exist_ok=True)

    csv_path_a.write_text(csv_text_a, encoding="utf-8", newline="\n")
    csv_path_b.write_text(csv_text_b, encoding="utf-8", newline="\n")

    payload = {
        "schema": "OV-SND-01N2_digitized_propagation_metadata/v2",
        "date": str(date),
        "observable_id": rec.observable_id,
        "digitization_id": rec.digitization_id,
        "source": rec.source,
        "dataset": rec.dataset,
        "record_fingerprint": rec.fingerprint(),
        "notes": "Written only when the pinned split rule yields two series with sufficient support; otherwise blocked.",
    }
    meta_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    return {"csv_seriesA": csv_path_a, "csv_seriesB": csv_path_b, "metadata": meta_path}


def write_ovsnd01n2_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-SND-01N2_sound_propagation_distance_time_digitized.md"

    rec = ovsnd01n2_digitized_propagation_dataset_record(date=str(date))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsnd01n2_lock_markdown(rec), encoding="utf-8")
    return out
