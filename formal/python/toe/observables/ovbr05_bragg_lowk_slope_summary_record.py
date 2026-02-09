"""OV-BR-05: Bragg low-k slope summary table (computed lock).

Purpose
- Provide a single, explicit summary table of the Bragg low-k slope results
  for condition_A and condition_B, derived from already-locked OV-BR-04A/04B.

Scope / limits
- Bookkeeping/summary only; no physics claim.
- Uses locked OV-BR-04A/04B outputs; does not re-fit.
- May be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re
from pathlib import Path
from typing import Any

from formal.python.toe.constraints.admissibility_manifest import check_required_gates
from formal.python.toe.observables.ovbr04a_bragg_lowk_slope_conditionA_record import (
    ovbr04a_bragg_lowk_slope_conditionA_record,
)
from formal.python.toe.observables.ovbr04b_bragg_lowk_slope_conditionB_record import (
    ovbr04b_bragg_lowk_slope_conditionB_record,
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


def _extract_record_fingerprint(md_text: str) -> str:
    m = re.search(r"Record fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise ValueError("Missing record fingerprint line")
    return m.group(1)


@dataclass(frozen=True)
class OVBR05BraggLowKSlopeSummaryRecord:
    schema: str
    date: str

    observable_id: str
    status: dict[str, Any]

    inputs: dict[str, Any]
    selection: dict[str, Any]
    rows: list[dict[str, Any]]

    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "status": dict(self.status),
            "inputs": dict(self.inputs),
            "selection": dict(self.selection),
            "rows": list(self.rows),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovbr05_bragg_lowk_slope_summary_record(*, date: str = "2026-01-25", admissibility_manifest_path: Path | None = None) -> OVBR05BraggLowKSlopeSummaryRecord:
    repo_root = _find_repo_root(Path(__file__))

    required_gates = ["CT01", "SYM01", "CAUS01"]
    gate_check = check_required_gates(repo_root=repo_root, required_gate_ids=required_gates, manifest_path=admissibility_manifest_path)
    debug = {
        "manifest_input_path": str(admissibility_manifest_path) if admissibility_manifest_path else None,
        "manifest_resolved_path": str(gate_check.manifest_path),
        "manifest_version": gate_check.manifest_version,
        "manifest_sha256": gate_check.manifest_sha256,
    }

    status: dict[str, Any] = {
        "blocked": bool(gate_check.blocked),
        "reasons": list(gate_check.reasons),
        "required_gates": list(required_gates),
        "admissibility_manifest": {
            "path": str(gate_check.manifest_path),
            "version": gate_check.manifest_version,
        },
        "debug": debug,
    }

    if gate_check.blocked:
        return OVBR05BraggLowKSlopeSummaryRecord(
            schema="OV-BR-05_bragg_lowk_slope_summary/v1",
            date=str(date),
            observable_id="OV-BR-05",
            status=status,
            inputs={},
            selection={},
            rows=[
                {
                    "condition_key": "condition_A",
                    "condition_semantic": "blocked_placeholder",
                    "c_mm_per_s": None,
                    "se_mm_per_s": None,
                },
                {
                    "condition_key": "condition_B",
                    "condition_semantic": "blocked_placeholder",
                    "c_mm_per_s": None,
                    "se_mm_per_s": None,
                },
            ],
            scope_limits=[
                "blocked_by_admissibility_manifest",
                "requires_CT01_SYM01_CAUS01",
                "structural_placeholder_only_when_blocked",
            ],
        )

    a = ovbr04a_bragg_lowk_slope_conditionA_record(date=str(date), admissibility_manifest_path=admissibility_manifest_path)
    b = ovbr04b_bragg_lowk_slope_conditionB_record(date=str(date), admissibility_manifest_path=admissibility_manifest_path)

    a_blocked = bool(getattr(a, "status", {}).get("blocked", False))
    b_blocked = bool(getattr(b, "status", {}).get("blocked", False))
    a_primary = getattr(a, "results", {}).get("primary") if isinstance(getattr(a, "results", None), dict) else None
    b_primary = getattr(b, "results", {}).get("primary") if isinstance(getattr(b, "results", None), dict) else None

    if a_blocked or b_blocked or not isinstance(a_primary, dict) or not isinstance(b_primary, dict):
        status_blocked = dict(status)
        status_blocked["blocked"] = True
        reasons = list(status_blocked.get("reasons", []))
        if a_blocked:
            reasons.append("input_OV-BR-04A_is_blocked")
        if b_blocked:
            reasons.append("input_OV-BR-04B_is_blocked")
        if not isinstance(a_primary, dict):
            reasons.append("input_OV-BR-04A_missing_results_primary")
        if not isinstance(b_primary, dict):
            reasons.append("input_OV-BR-04B_missing_results_primary")
        status_blocked["reasons"] = reasons

        return OVBR05BraggLowKSlopeSummaryRecord(
            schema="OV-BR-05_bragg_lowk_slope_summary/v1",
            date=str(date),
            observable_id="OV-BR-05",
            status=status_blocked,
            inputs={
                "condition_A": getattr(a, "results", {}),
                "condition_B": getattr(b, "results", {}),
            },
            selection={},
            rows=[
                {
                    "condition_key": "condition_A",
                    "condition_semantic": "blocked_placeholder",
                    "c_mm_per_s": None,
                    "se_mm_per_s": None,
                },
                {
                    "condition_key": "condition_B",
                    "condition_semantic": "blocked_placeholder",
                    "c_mm_per_s": None,
                    "se_mm_per_s": None,
                },
            ],
            scope_limits=[
                "blocked_by_upstream_input",
                "requires_CT01_SYM01_CAUS01",
                "structural_placeholder_only_when_blocked",
            ],
        )

    # Compose inputs, selection, and rows from a and b
    inputs = {
        "condition_A": getattr(a, "results", {}),
        "condition_B": getattr(b, "results", {}),
    }
    selection: dict[str, Any] = {}
    rows = [
        {
            "condition_key": str(a.condition_key),
            "condition_semantic": str(a.condition_semantic),
            **dict(a_primary),
        },
        {
            "condition_key": str(b.condition_key),
            "condition_semantic": str(b.condition_semantic),
            **dict(b_primary),
        },
    ]
    return OVBR05BraggLowKSlopeSummaryRecord(
        schema="OV-BR-05_bragg_lowk_slope_summary/v1",
        date=str(date),
        observable_id="OV-BR-05",
        status=status,
        inputs=inputs,
        selection=selection,
        rows=rows,
        scope_limits=[
            "summary_only",
            "derived_from_locked_records_only",
            "no_refitting",
            "bookkeeping_only_no_physics_claim",
        ],
    )


def render_ovbr05_lock_markdown(record: OVBR05BraggLowKSlopeSummaryRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-BR-05 — Bragg low-k slope summary (computed)\n\n"
        "Scope / limits\n"
        "- Summary-only table derived from locked OV-BR-04A/04B\n"
        "- Bookkeeping only; no physics claim\n"
        "- No refitting performed\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovbr05_lock(*, lock_path: Path | None = None, date: str = "2026-01-25", admissibility_manifest_path: Path | None = None) -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-BR-05_bragg_lowk_slope_summary.md"

    rec = ovbr05_bragg_lowk_slope_summary_record(date=str(date), admissibility_manifest_path=admissibility_manifest_path)

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbr05_lock_markdown(rec), encoding="utf-8")
    return out
