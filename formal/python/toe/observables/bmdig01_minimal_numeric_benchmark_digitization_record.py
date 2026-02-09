"""BM-DIG-01: minimal numeric benchmark digitization acceptance criteria (computed lock).

Purpose
- Specify the smallest acceptable numeric digitization target and acceptance
  criteria for converting ONE benchmark (OV-BM-01 or OV-BM-02) into a typed,
  frozen numeric artifact while preserving strict benchmark-only scope fences.

Scope / limits
- Bookkeeping / workflow governance only; no physics claim.
- Does not require or perform digitization.
- Does not change any ToE policy gates.

Design constraints
- Deterministic (no RNG, no network).
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
class BMDIG01MinimalNumericBenchmarkDigitizationRecord:
    schema: str
    date: str

    scope_statement: str

    allowed_targets: list[dict[str, Any]]
    acceptance_criteria: list[str]
    explicit_disallow: list[str]

    narrative: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "scope_statement": str(self.scope_statement),
            "allowed_targets": list(self.allowed_targets),
            "acceptance_criteria": list(self.acceptance_criteria),
            "explicit_disallow": list(self.explicit_disallow),
            "narrative": str(self.narrative),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def bmdig01_minimal_numeric_benchmark_digitization_record(
    *,
    date: str = "2026-01-23",
) -> BMDIG01MinimalNumericBenchmarkDigitizationRecord:
    scope_statement = (
        "Benchmark-only numeric digitization: frozen artifact ingestion stress test. "
        "No validation claim; no continuity inference; no regime averaging; no cross-observable inference."
    )

    allowed_targets = [
        {
            "benchmark_id": "OV-BM-01",
            "name": "Mean-field mean-shift scaling",
            "minimal_target": "Digitize a single curve/series that reports mean (first-moment) frequency shift as a function of density (or a directly stated density proxy) from one figure in Stenger (1999).",
            "what_it_tests": [
                "typed numeric artifact ingestion",
                "unit/provenance preservation",
                "no model selection from benchmark",
                "no regime blending",
            ],
        },
        {
            "benchmark_id": "OV-BM-02",
            "name": "Linewidth quadrature composition",
            "minimal_target": "Digitize a single curve/series sufficient to represent a linewidth quantity and its stated decomposition components (as available) from one figure in Stenger (1999); store components separately if the figure reports them separately.",
            "what_it_tests": [
                "multiple component storage without forced averaging",
                "quadrature structure preserved",
                "no dominance/crossover claims inferred",
            ],
        },
    ]

    acceptance_criteria = [
        "Source provenance must name paper, figure number, and (if available) page/axis labels.",
        "Digitized data must be stored as a frozen CSV (or equivalent) with explicit units for every axis.",
        "Digitization must be deterministic (no RNG) and reproducible from a pinned input image/PDF snapshot in the repo.",
        "One series only for the first pass (no mixing multiple curves, no insets).",
        "Minimum point count: N>=8 covering >=60% of the visible x-range for that series.",
        "No fitting as part of the benchmark digitization step; fitting remains a separate, explicitly-scoped operation.",
        "The resulting benchmark numeric record must assert: non-decisive by design, no continuity claim, no regime averaging, no cross-observable inference.",
        "A new OV-SEL-BM-style narrative lock must state: what changed / what did not / why, and must explicitly confirm no policy/threshold changes were triggered.",
    ]

    explicit_disallow = [
        "no sound-speed inference",
        "no dispersion-family inference",
        "no preference flips attributable to benchmark ingestion",
        "no continuity or regime crossover claim",
        "no averaging across regimes",
        "no numeric comparison used as ToE validation evidence",
    ]

    narrative = (
        "BM-DIG-01 minimal numeric benchmark digitization plan (bookkeeping-only):\n"
        "- Choose exactly one benchmark (OV-BM-01 or OV-BM-02).\n"
        "- Digitize exactly one series from exactly one figure, with explicit provenance and units.\n"
        "- Store as a frozen artifact; do not fit; do not infer; do not blend regimes.\n"
        "- Lock an OV-SEL-BM-style narrative confirming no policy triggers or preference changes occurred."
    )

    return BMDIG01MinimalNumericBenchmarkDigitizationRecord(
        schema="BM-DIG-01_minimal_numeric_benchmark_digitization/v1",
        date=str(date),
        scope_statement=scope_statement,
        allowed_targets=allowed_targets,
        acceptance_criteria=acceptance_criteria,
        explicit_disallow=explicit_disallow,
        narrative=narrative,
    )


def render_bmdig01_lock_markdown(record: BMDIG01MinimalNumericBenchmarkDigitizationRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# BM-DIG-01 — Minimal numeric benchmark digitization acceptance criteria (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / workflow governance only; no physics claim\n"
        "- Specifies smallest acceptable digitization target and acceptance criteria\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_bmdig01_lock(*, lock_path: Path | None = None, date: str = "2026-01-23") -> Path:
    repo_root = _find_repo_root(Path(__file__))

    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "policies" / "BM-DIG-01_minimal_numeric_benchmark_digitization.md"

    rec = bmdig01_minimal_numeric_benchmark_digitization_record(date=str(date))

    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_bmdig01_lock_markdown(rec), encoding="utf-8")
    return out
