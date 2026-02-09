"""SND-DIG-01: minimal density digitization acceptance criteria (computed lock).

Purpose
- Specify the smallest acceptable numeric density digitization target and acceptance
  criteria for the sound lane, enabling density-dependent scaling checks while
  preserving strict scope fences.

Scope / limits
- Bookkeeping / workflow governance only; no physics claim.
- Does not require or perform any digitization.
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
class SNDDIG01MinimalDensityDigitizationRecord:
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


def snddig01_minimal_density_digitization_record(*, date: str = "2026-01-24") -> SNDDIG01MinimalDensityDigitizationRecord:
    scope_statement = (
        "Sound-lane density digitization: frozen density anchor(s) for bookkeeping-scale checks. "
        "No validation claim; no continuity inference; no regime averaging; no cross-observable inference."
    )

    allowed_targets = [
        {
            "lane": "sound",
            "target_id": "OV-SND-03N",
            "name": "Central (or peak) density numeric anchor",
            "minimal_target": (
                "Extract a single explicitly stated density value (central or peak), with units, "
                "from a pinned source PDF snapshot used by the sound lane. Store as a frozen CSV plus "
                "JSON metadata wrapper under formal/external_evidence."
            ),
            "what_it_tests": [
                "typed numeric artifact ingestion",
                "unit/provenance preservation",
                "density as second independent variable (without implying dependence)",
            ],
        }
    ]

    acceptance_criteria = [
        "Source provenance must name paper and page context (and figure/table if applicable).",
        "Digitized density must be stored as a frozen CSV (or equivalent) with explicit units.",
        "Digitization must be deterministic (no RNG) and reproducible from pinned inputs in the repo (PDF snapshot).",
        "First pass may include a single condition only; if multiple conditions are available, they must be stored without averaging.",
        "The resulting numeric record must assert: non-decisive by design, no continuity claim, no regime averaging, no cross-observable inference.",
        "A new OV-SEL-SND-style narrative lock must state: what changed / what did not / why, and must explicitly confirm no policy/threshold changes were triggered.",
    ]

    explicit_disallow = [
        "no continuity inference from density",
        "no regime crossover claim",
        "no averaging across regimes",
        "no selection preference flip attributable to density ingestion",
        "no density imputation from unrelated observables",
    ]

    narrative = (
        "SND-DIG-01 minimal density digitization plan (bookkeeping-only):\n"
        "- Choose a pinned sound-lane source PDF already in the repo.\n"
        "- Extract at least one explicit density number with units, deterministically.\n"
        "- Store as frozen artifact + metadata; do not fit; do not infer dependence.\n"
        "- Lock an OV-SEL-SND-style narrative confirming no policy triggers or preference changes occurred."
    )

    return SNDDIG01MinimalDensityDigitizationRecord(
        schema="SND-DIG-01_minimal_density_digitization/v1",
        date=str(date),
        scope_statement=scope_statement,
        allowed_targets=allowed_targets,
        acceptance_criteria=acceptance_criteria,
        explicit_disallow=explicit_disallow,
        narrative=narrative,
    )


def render_snddig01_lock_markdown(record: SNDDIG01MinimalDensityDigitizationRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# SND-DIG-01 — Minimal density digitization acceptance criteria (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / workflow governance only; no physics claim\n"
        "- Specifies smallest acceptable density digitization target and acceptance criteria\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_snddig01_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))

    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "policies" / "SND-DIG-01_minimal_density_digitization.md"

    rec = snddig01_minimal_density_digitization_record(date=str(date))

    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_snddig01_lock_markdown(rec), encoding="utf-8")
    return out
