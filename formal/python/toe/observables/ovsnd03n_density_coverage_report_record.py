"""OV-SND-03N-COV: density coverage report for multi-condition scaling (computed lock).

Purpose
- Provide a deterministic decision gate stating how many density conditions are
  currently supported by the pinned sound-lane density artifacts, and whether
  a multi-condition constancy check is feasible without cross-source mapping.

Scope / limits
- Bookkeeping only; no physics claim.
- Does not digitize new data.
- Reports coverage/blockers only.

Rationale
- Prevents planning multi-condition checks when the pinned source supports only
  a single explicit density value.
"""

from __future__ import annotations

from dataclasses import dataclass
import csv
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.toe.observables.ovsnd02_sound_speed_from_propagation_record import (
    ovsnd02_sound_speed_from_propagation_record,
)
from formal.python.toe.observables.ovsnd03n_central_density_digitized import (
    ovsnd03n_central_density_digitized_record,
)


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


def _count_density_conditions_from_csv(csv_path: Path) -> int:
    with csv_path.open("r", encoding="utf-8", newline="") as f:
        r = csv.DictReader(f)
        if r.fieldnames != ["condition_id", "n0_cm3"]:
            raise ValueError(f"Unexpected columns: {r.fieldnames}")
        rows = list(r)

    condition_ids = [str(row["condition_id"]) for row in rows]
    if len(set(condition_ids)) != len(condition_ids):
        raise ValueError("Duplicate condition_id in density CSV")

    return int(len(rows))


@dataclass(frozen=True)
class OVSND03NDensityCoverageReportRecord:
    schema: str
    date: str

    observable_id: str

    inputs: dict[str, Any]
    coverage: dict[str, Any]
    decision: dict[str, Any]
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "inputs": dict(self.inputs),
            "coverage": dict(self.coverage),
            "decision": dict(self.decision),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsnd03n_density_coverage_report_record(*, date: str = "2026-01-24") -> OVSND03NDensityCoverageReportRecord:
    repo_root = _find_repo_root(Path(__file__))

    snd02 = ovsnd02_sound_speed_from_propagation_record(date=str(date))
    den = ovsnd03n_central_density_digitized_record(date=str(date))

    csv_rel = str(den.dataset["csv_relpath"])
    csv_path = repo_root / csv_rel

    n_density_conditions = _count_density_conditions_from_csv(csv_path)

    # Under the current sound lane, OV-SND-02 produces a single derived c value.
    n_speed_conditions = 1

    n_pairs_supported = int(min(n_density_conditions, n_speed_conditions))

    blockers: list[str] = []
    if n_density_conditions < 2:
        blockers.append("density_source_supports_only_one_explicit_condition")
    if n_speed_conditions < 2:
        blockers.append("speed_anchor_supports_only_one_condition")

    multi_condition_possible_same_source = bool(n_density_conditions >= 2 and n_speed_conditions >= 2)

    decision = {
        "n_density_conditions_supported": int(n_density_conditions),
        "n_speed_conditions_supported": int(n_speed_conditions),
        "n_pairs_supported": int(n_pairs_supported),
        "multi_condition_possible_same_source": bool(multi_condition_possible_same_source),
        "recommended_path": (
            "OptionA_same_source" if multi_condition_possible_same_source else "OptionB_cross_source_mapping_required"
        ),
        "blockers": list(blockers),
    }

    inputs = {
        "OV-SND-02": {
            "record_schema": str(snd02.schema),
            "record_fingerprint": str(snd02.fingerprint()),
            "lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
        },
        "OV-SND-03N": {
            "record_schema": str(den.schema),
            "record_fingerprint": str(den.fingerprint()),
            "lock_path": "formal/markdown/locks/observables/OV-SND-03_central_density_digitized.md",
            "density_csv_relpath": csv_rel,
        },
    }

    coverage = {
        "density_csv_row_count": int(n_density_conditions),
        "density_condition_ids": "from_csv_condition_id_column",
        "speed_condition_ids": "single_condition_OV-SND-02",
    }

    scope_limits = [
        "bookkeeping_only",
        "no_physics_claim",
        "no_new_digitization",
        "no_continuity_claim",
        "non_decisive_by_design",
    ]

    return OVSND03NDensityCoverageReportRecord(
        schema="OV-SND-03N_density_coverage_report/v1",
        date=str(date),
        observable_id="OV-SND-03N-COV",
        inputs=inputs,
        coverage=coverage,
        decision=decision,
        scope_limits=scope_limits,
    )


def render_ovsnd03n_coverage_lock_markdown(record: OVSND03NDensityCoverageReportRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SND-03N-COV — Density coverage report (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping only; no physics claim\n"
        "- Coverage + blockers only; no new digitization\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsnd03n_coverage_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-SND-03N_density_coverage_report.md"

    rec = ovsnd03n_density_coverage_report_record(date=str(date))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsnd03n_coverage_lock_markdown(rec), encoding="utf-8")
    return out
