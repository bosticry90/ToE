"""OV-BM-01: baseline benchmark observable (symbolic, non-validating).

Benchmark A — Mean-field line shift scaling

Purpose
- Encode (symbolically only) a conservative, literature-stated mean-field scaling
  relationship for use as an ingestion / regime-handling stress-test.

Scope / limits
- Symbolic-only: no digitization, no extracted points, no fitting.
- No numerical parameter values are locked.
- No regime averaging, no continuity claim, no cross-observable inference.
- Non-decisive by design: this benchmark does not participate in fit-family
  selection.

Reference provenance
- Stenger et al. (1999), Bragg spectroscopy of a Bose-Einstein condensate.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


@dataclass(frozen=True)
class OVBM01MeanFieldLineShiftScalingBenchmark:
    schema: str

    observable_id: str
    category: str
    status: str
    validation: str

    symbolic_relation_latex: str
    functional_dependency: dict[str, Any]

    reference_provenance: dict[str, Any]
    scope_limits: list[str]

    notes: str

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "observable_id": str(self.observable_id),
            "category": str(self.category),
            "status": str(self.status),
            "validation": str(self.validation),
            "symbolic_relation_latex": str(self.symbolic_relation_latex),
            "functional_dependency": dict(self.functional_dependency),
            "reference_provenance": dict(self.reference_provenance),
            "scope_limits": list(self.scope_limits),
            "notes": str(self.notes),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable())


def ovbm01_mean_field_line_shift_scaling_benchmark() -> OVBM01MeanFieldLineShiftScalingBenchmark:
    return OVBM01MeanFieldLineShiftScalingBenchmark(
        schema="OV-BM-01_mean_field_line_shift_scaling_benchmark/v1",
        observable_id="OV-BM-01",
        category="Benchmark",
        status="Structural (symbolic)",
        validation="None",
        symbolic_relation_latex=r"\\langle \\Delta \\nu \\rangle \\propto \\frac{4 n_0 U}{7 h}",
        functional_dependency={
            "is_proportional": True,
            "linear_in": ["n0"],
            "variables": {
                "n0": "peak density",
                "U": "interaction strength (mean-field coupling)",
                "h": "Planck constant",
            },
            "moment": "first_moment_mean_shift",
            "not_a_dispersion_curve": True,
        },
        reference_provenance={
            "type": "literature_reference",
            "citation": "Stenger et al. (1999) — Bragg spectroscopy of a Bose–Einstein condensate",
            "role": "calibration_weight_non_validating",
        },
        scope_limits=[
            "symbolic_only",
            "no_digitization",
            "no_extracted_points",
            "no_curve_fitting",
            "no_regime_averaging",
            "no_continuity_claim",
            "no_cross_observable_inference",
            "non_decisive_by_design",
        ],
        notes=(
            "Encodes a benchmark mean-field density–shift dependency used solely to test regime handling and "
            "provenance preservation. Does not validate any ToE mechanism or imply continuity across regimes."
        ),
    )


def render_ovbm01_lock_markdown(record: OVBM01MeanFieldLineShiftScalingBenchmark) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-BM-01 — Benchmark A: mean-field line shift scaling (symbolic)\n\n"
        "Baseline benchmark observable (symbolic, non-validating).\n\n"
        "What is locked\n"
        "- Functional dependency (linear in density)\n"
        "- Symbolic proportionality form\n"
        "- First moment (mean shift), not a dispersion curve\n\n"
        "What is not locked\n"
        "- No numerical parameter values\n"
        "- No digitized points / CSV artifacts\n"
        "- No fitting, no regime averaging, no continuity claim\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovbm01_lock(*, lock_path: Path | None = None) -> Path:
    repo_root = _find_repo_root(Path(__file__))

    rec = ovbm01_mean_field_line_shift_scaling_benchmark()

    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "benchmarks"
            / "OV-BM-01_mean_field_line_shift_scaling.md"
        )

    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbm01_lock_markdown(rec), encoding="utf-8")
    return out
