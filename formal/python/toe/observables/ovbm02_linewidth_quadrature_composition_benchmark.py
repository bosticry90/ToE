"""OV-BM-02: baseline benchmark observable (symbolic, non-validating).

Benchmark B — Linewidth quadrature composition

Purpose
- Encode (symbolically only) a conservative, literature-stated linewidth
  composition rule for ingestion / regime-handling stress-testing.

Scope / limits
- Symbolic-only: no digitization, no extracted points, no fitting.
- No numerical widths are locked.
- No dominance or crossover claims.
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
class OVBM02LinewidthQuadratureCompositionBenchmark:
    schema: str

    observable_id: str
    category: str
    status: str
    validation: str

    symbolic_relation_latex: str
    mechanism_components: dict[str, Any]

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
            "mechanism_components": dict(self.mechanism_components),
            "reference_provenance": dict(self.reference_provenance),
            "scope_limits": list(self.scope_limits),
            "notes": str(self.notes),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable())


def ovbm02_linewidth_quadrature_composition_benchmark() -> OVBM02LinewidthQuadratureCompositionBenchmark:
    return OVBM02LinewidthQuadratureCompositionBenchmark(
        schema="OV-BM-02_linewidth_quadrature_composition_benchmark/v1",
        observable_id="OV-BM-02",
        category="Benchmark",
        status="Structural (symbolic)",
        validation="None",
        symbolic_relation_latex=r"\\sigma_{\\mathrm{total}}^2 = \\sigma_{\\mathrm{Doppler}}^2 + \\sigma_{\\mathrm{MF}}^2",
        mechanism_components={
            "quadrature": True,
            "components": [
                {"name": "sigma_Doppler", "meaning": "Doppler / finite-size broadening"},
                {"name": "sigma_MF", "meaning": "mean-field broadening"},
            ],
            "separation_of_mechanisms": True,
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
            "no_dominance_claim",
            "no_regime_averaging",
            "no_continuity_claim",
            "no_cross_observable_inference",
            "non_decisive_by_design",
        ],
        notes=(
            "Encodes a benchmark linewidth composition rule used to test whether the framework preserves independent "
            "contributions without forced averaging or regime blending."
        ),
    )


def render_ovbm02_lock_markdown(record: OVBM02LinewidthQuadratureCompositionBenchmark) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-BM-02 — Benchmark B: linewidth quadrature composition (symbolic)\n\n"
        "Baseline benchmark observable (symbolic, non-validating).\n\n"
        "What is locked\n"
        "- Quadrature composition structure (sum of squares)\n"
        "- Separation of mechanism contributions\n\n"
        "What is not locked\n"
        "- No numerical linewidths\n"
        "- No dominance/crossover claims\n"
        "- No digitized points / CSV artifacts\n"
        "- No fitting, no regime averaging, no continuity claim\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovbm02_lock(*, lock_path: Path | None = None) -> Path:
    repo_root = _find_repo_root(Path(__file__))

    rec = ovbm02_linewidth_quadrature_composition_benchmark()

    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "benchmarks"
            / "OV-BM-02_linewidth_quadrature_composition.md"
        )

    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbm02_lock_markdown(rec), encoding="utf-8")
    return out
