"""OV-BM-01 (numeric): minimal digitized mean-shift vs peak-density dataset (computed lock).

Purpose
- Provide a smallest-acceptable numeric digitization target for OV-BM-01 under BM-DIG-01.

Scope / limits
- Benchmark-only numeric ingestion: no validation claim.
- No fitting, no regime averaging, no continuity claim, no cross-observable inference.

Design
- Deterministic: raw digitized points are hard-coded (manual transcription from a pinned screenshot).
- Writes a frozen CSV + JSON metadata wrapper under formal/external_evidence.
"""

from __future__ import annotations

from dataclasses import dataclass
import csv
import hashlib
import json
from pathlib import Path
from typing import Any


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


# Minimal digitized target: panel (a), filled-circle series only.
# Values are manual transcription from the pinned screenshot.
# Columns:
# - peak_density: in 1e14 cm^-3
# - delta_nu: in kHz (center nu - nu0)
# - delta_nu_err: in kHz (approx; transcription uncertainty)
_DIGITIZED_POINTS: list[dict[str, float]] = [
    {"peak_density_1e14_cm3": 1.75, "delta_nu_khz": 1.52, "delta_nu_err_khz": 0.15},
    {"peak_density_1e14_cm3": 2.05, "delta_nu_khz": 1.78, "delta_nu_err_khz": 0.15},
    {"peak_density_1e14_cm3": 2.25, "delta_nu_khz": 1.95, "delta_nu_err_khz": 0.15},
    {"peak_density_1e14_cm3": 2.55, "delta_nu_khz": 2.18, "delta_nu_err_khz": 0.18},
    {"peak_density_1e14_cm3": 2.90, "delta_nu_khz": 2.55, "delta_nu_err_khz": 0.20},
    {"peak_density_1e14_cm3": 3.25, "delta_nu_khz": 2.85, "delta_nu_err_khz": 0.20},
    {"peak_density_1e14_cm3": 3.60, "delta_nu_khz": 3.10, "delta_nu_err_khz": 0.22},
    {"peak_density_1e14_cm3": 4.05, "delta_nu_khz": 3.28, "delta_nu_err_khz": 0.24},
    {"peak_density_1e14_cm3": 4.55, "delta_nu_khz": 3.62, "delta_nu_err_khz": 0.25},
]


@dataclass(frozen=True)
class OVBM01DigitizedMeanShiftDatasetRecord:
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


def _csv_rows() -> list[dict[str, str]]:
    # Deterministic float formatting; avoid locale variance.
    def f(x: float) -> str:
        return ("%.6g" % float(x))

    rows: list[dict[str, str]] = []
    for p in _DIGITIZED_POINTS:
        rows.append(
            {
                "peak_density_1e14_cm3": f(float(p["peak_density_1e14_cm3"])),
                "delta_nu_khz": f(float(p["delta_nu_khz"])),
                "delta_nu_err_khz": f(float(p["delta_nu_err_khz"])),
            }
        )
    return rows


def _render_csv_text() -> str:
    header = ["peak_density_1e14_cm3", "delta_nu_khz", "delta_nu_err_khz"]
    lines = [",".join(header)]
    for r in _csv_rows():
        lines.append(",".join([r[h] for h in header]))
    return "\n".join(lines) + "\n"


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def ovbm01_digitized_mean_shift_dataset_record(*, date: str = "2026-01-23") -> OVBM01DigitizedMeanShiftDatasetRecord:
    repo_root = _find_repo_root(Path(__file__))
    base = repo_root / "formal" / "external_evidence" / "bec_bragg_stenger_1999"

    pdf_rel = "formal/external_evidence/bec_bragg_stenger_1999/9901109v1.pdf"
    img_rel = "formal/external_evidence/bec_bragg_stenger_1999/Screenshot 2026-01-23 234806.png"

    pdf_sha = _sha256_file(repo_root / pdf_rel)
    img_sha = _sha256_file(repo_root / img_rel)

    csv_rel = "formal/external_evidence/bec_bragg_stenger_1999/ovbm01_digitization/mean_shift_vs_peak_density.csv"
    meta_rel = (
        "formal/external_evidence/bec_bragg_stenger_1999/ovbm01_digitization/mean_shift_vs_peak_density.metadata.json"
    )

    csv_text = _render_csv_text()

    dataset = {
        "csv_relpath": csv_rel,
        "metadata_relpath": meta_rel,
        "row_count": len(_DIGITIZED_POINTS),
        "columns": [
            {"name": "peak_density_1e14_cm3", "unit": "1e14 cm^-3", "dtype": "float"},
            {"name": "delta_nu_khz", "unit": "kHz", "dtype": "float"},
            {"name": "delta_nu_err_khz", "unit": "kHz", "dtype": "float"},
        ],
        "csv_sha256": _sha256_text(csv_text),
    }

    source = {
        "citation": "Stenger et al. (1999) — Bragg spectroscopy of a Bose–Einstein condensate",
        "arxiv_pdf_relpath": pdf_rel,
        "arxiv_pdf_sha256": pdf_sha,
        "screenshot_relpath": img_rel,
        "screenshot_sha256": img_sha,
        "figure": "Fig. 4 (panel a)",
        "series": "filled_circles_only",
        "digitization_method": "manual_transcription_from_pinned_screenshot",
        "notes": "Smallest acceptable target under BM-DIG-01; values are approximate and intended for pipeline determinism checks only.",
    }

    scope_limits = [
        "benchmark_only_numeric",
        "no_curve_fitting",
        "no_regime_averaging",
        "no_continuity_claim",
        "no_cross_observable_inference",
        "non_decisive_by_design",
    ]

    return OVBM01DigitizedMeanShiftDatasetRecord(
        schema="OV-BM-01_mean_field_line_shift_scaling_digitized/v1",
        digitization_id="OV-BM-01N",
        date=str(date),
        observable_id="OV-BM-01",
        source=source,
        dataset=dataset,
        scope_limits=scope_limits,
    )


def write_ovbm01_digitized_artifacts(*, date: str = "2026-01-23") -> dict[str, Path]:
    repo_root = _find_repo_root(Path(__file__))
    rec = ovbm01_digitized_mean_shift_dataset_record(date=str(date))

    csv_text = _render_csv_text()

    csv_path = repo_root / rec.dataset["csv_relpath"]
    meta_path = repo_root / rec.dataset["metadata_relpath"]

    csv_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path.parent.mkdir(parents=True, exist_ok=True)

    # Write CSV deterministically.
    csv_path.write_text(csv_text, encoding="utf-8", newline="\n")

    meta_payload = {
        "schema": "OV-BM-01_digitized_dataset_metadata/v1",
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


def render_ovbm01_digitized_lock_markdown(record: OVBM01DigitizedMeanShiftDatasetRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-BM-01N — Digitized benchmark: mean-field mean-shift vs peak density (computed)\n\n"
        "Scope / limits\n"
        "- Benchmark-only numeric ingestion; no physics validation claim\n"
        "- No fitting; no regime averaging; no continuity claim; no cross-observable inference\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovbm01_digitized_lock(*, lock_path: Path | None = None, date: str = "2026-01-23") -> Path:
    repo_root = _find_repo_root(Path(__file__))

    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "benchmarks"
            / "OV-BM-01_mean_field_line_shift_scaling_digitized.md"
        )

    rec = ovbm01_digitized_mean_shift_dataset_record(date=str(date))

    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbm01_digitized_lock_markdown(rec), encoding="utf-8")
    return out
