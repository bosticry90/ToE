"""OV-CV-BR-01: explicit CV01 v1 -> pruning bridge (summary-only lock).

Purpose
- Provide an explicit, deterministic bridge from CV01 v1 reason codes to pruning
  reason atoms.
- Keep coupling governed and non-implicit: BR pruning remains canonical; this lane
  adds an auditable CV01-attributed elimination surface.

Scope / limits
- Summary-only / eliminative-only bookkeeping.
- No numeric interpretation and no external truth claim.
- Blocked-by-default on missing policy source.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Literal

from formal.python.toe.comparators.cv01_bec_bragg_v1 import cv01_bec_bragg_v1_record
from formal.python.toe.observables.ovdrbr01_candidate_pruning_table_record import (
    ovdrbr01_candidate_pruning_table_record,
)


SurvivalStatus = Literal["true", "false", "unknown"]


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


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


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _validate_policy(doc: dict[str, Any]) -> tuple[bool, str]:
    if str(doc.get("schema")) != "OVCV01_v1_pruning_reason_policy/v1":
        return False, "schema_unexpected"

    if not isinstance(doc.get("version"), int):
        return False, "version_not_int"

    reason_code_to_atom = doc.get("reason_code_to_atom")
    if not isinstance(reason_code_to_atom, dict) or not reason_code_to_atom:
        return False, "reason_code_to_atom_invalid"

    for k, v in reason_code_to_atom.items():
        if not isinstance(k, str) or not k:
            return False, "reason_code_to_atom_key_invalid"
        if not isinstance(v, str) or not v:
            return False, "reason_code_to_atom_value_invalid"

    eliminative_atoms = doc.get("eliminative_atoms")
    if not isinstance(eliminative_atoms, list) or not all(isinstance(a, str) and a for a in eliminative_atoms):
        return False, "eliminative_atoms_invalid"

    candidate_rules = doc.get("candidate_rules")
    if not isinstance(candidate_rules, dict):
        return False, "candidate_rules_invalid"

    for cid, rule in candidate_rules.items():
        if not isinstance(cid, str) or not cid:
            return False, "candidate_rules_key_invalid"
        if not isinstance(rule, dict):
            return False, "candidate_rule_not_object"
        atoms = rule.get("eliminate_on_atoms")
        if not isinstance(atoms, list) or not all(isinstance(a, str) and a for a in atoms):
            return False, "candidate_rule_eliminate_on_atoms_invalid"

    return True, "ok"


@dataclass(frozen=True)
class OVCVBR01PruningBridgeRecord:
    schema: str
    date: str

    observable_id: str
    status: dict[str, Any]

    inputs: dict[str, Any]
    mapping_policy: dict[str, Any]
    active_reason_codes: list[str]
    active_reason_atoms: list[str]
    rows: list[dict[str, Any]]
    summary: dict[str, Any]

    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "status": dict(self.status),
            "inputs": dict(self.inputs),
            "mapping_policy": dict(self.mapping_policy),
            "active_reason_codes": list(self.active_reason_codes),
            "active_reason_atoms": list(self.active_reason_atoms),
            "rows": list(self.rows),
            "summary": dict(self.summary),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovcvbr01_cv01_v1_pruning_bridge_record(
    *,
    date: str = "2026-02-08",
    base_pruning_date: str = "2026-01-25",
    cv01_tolerance_profile: str = "pinned",
    cv01_artifact_dir: Path | None = None,
    policy_path: Path | None = None,
) -> OVCVBR01PruningBridgeRecord:
    repo_root = _find_repo_root(Path(__file__))

    default_policy = repo_root / "formal" / "python" / "toe" / "observables" / "cv01_v1_pruning_reason_policy.json"
    resolved_policy = (policy_path or default_policy).resolve()

    if not resolved_policy.exists():
        return OVCVBR01PruningBridgeRecord(
            schema="OV-CV-BR-01_cv01_v1_pruning_bridge/v1",
            date=str(date),
            observable_id="OV-CV-BR-01",
            status={
                "blocked": True,
                "reasons": ["missing_cv01_pruning_reason_policy"],
            },
            inputs={
                "policy": {
                    "expected_path": str(default_policy),
                    "path": str(resolved_policy),
                    "present": False,
                }
            },
            mapping_policy={},
            active_reason_codes=[],
            active_reason_atoms=[],
            rows=[],
            summary={
                "counts": {"true": 0, "false": 0, "unknown": 0},
                "candidates": {"true": [], "false": [], "unknown": []},
                "cv01_attributed_eliminations": [],
                "cv01_attributed_elimination_count": 0,
                "survivor_guard": False,
            },
            scope_limits=["blocked_by_missing_policy", "summary_only", "front_door_only"],
        )

    raw_policy = resolved_policy.read_text(encoding="utf-8")
    policy_sha = _sha256_text(raw_policy)
    policy_doc = _read_json(resolved_policy)

    ok, reason = _validate_policy(policy_doc)
    if not ok:
        return OVCVBR01PruningBridgeRecord(
            schema="OV-CV-BR-01_cv01_v1_pruning_bridge/v1",
            date=str(date),
            observable_id="OV-CV-BR-01",
            status={
                "blocked": True,
                "reasons": ["invalid_cv01_pruning_reason_policy:" + str(reason)],
            },
            inputs={
                "policy": {
                    "expected_path": str(default_policy),
                    "path": str(resolved_policy),
                    "present": True,
                    "raw_sha256": str(policy_sha),
                }
            },
            mapping_policy={},
            active_reason_codes=[],
            active_reason_atoms=[],
            rows=[],
            summary={
                "counts": {"true": 0, "false": 0, "unknown": 0},
                "candidates": {"true": [], "false": [], "unknown": []},
                "cv01_attributed_eliminations": [],
                "cv01_attributed_elimination_count": 0,
                "survivor_guard": False,
            },
            scope_limits=["blocked_by_invalid_policy", "summary_only", "front_door_only"],
        )

    reason_code_to_atom = {
        str(k): str(v) for (k, v) in dict(policy_doc.get("reason_code_to_atom") or {}).items()
    }
    eliminative_atoms = {str(a) for a in list(policy_doc.get("eliminative_atoms") or [])}
    candidate_rules = dict(policy_doc.get("candidate_rules") or {})

    base = ovdrbr01_candidate_pruning_table_record(date=str(base_pruning_date))
    cv01 = cv01_bec_bragg_v1_record(
        date=str(date),
        tolerance_profile=str(cv01_tolerance_profile),
        artifact_dir=cv01_artifact_dir,
    )

    active_reason_codes = [str(x) for x in list((cv01.cross_artifact or {}).get("reason_codes") or [])]
    active_reason_atoms = sorted({reason_code_to_atom[c] for c in active_reason_codes if c in reason_code_to_atom})

    rows: list[dict[str, Any]] = []
    for base_row in list(base.rows or []):
        cid = str(base_row.get("candidate_id"))
        base_status = str(base_row.get("survives_br01_constraints"))
        base_reasons = [str(x) for x in list(base_row.get("reason_codes") or [])]

        rule = dict(candidate_rules.get(cid) or {})
        rule_atoms = sorted({str(x) for x in list(rule.get("eliminate_on_atoms") or [])})
        triggered_atoms = sorted([a for a in active_reason_atoms if a in set(rule_atoms)])
        eliminative_hits = [a for a in triggered_atoms if a in eliminative_atoms]

        cv01_attributed_elimination = False
        if base_status == "false":
            combined: SurvivalStatus = "false"
            reason_codes = base_reasons + ["retained_base_pruning_elimination"]
        elif len(eliminative_hits) >= 1:
            combined = "false"
            cv01_attributed_elimination = True
            reason_codes = base_reasons + [f"eliminated_by_cv01_reason_atom:{a}" for a in eliminative_hits]
        elif base_status == "true":
            combined = "true"
            reason_codes = base_reasons
        else:
            combined = "unknown"
            reason_codes = base_reasons

        rows.append(
            {
                "candidate_id": cid,
                "base_survives_br01_constraints": base_status,
                "survives_cv01_bridge_constraints": combined,
                "cv01_reason_atoms_considered": rule_atoms,
                "cv01_reason_atoms_triggered": triggered_atoms,
                "cv01_attributed_elimination": bool(cv01_attributed_elimination),
                "reason_codes": reason_codes,
            }
        )

    by_status: dict[SurvivalStatus, list[str]] = {"true": [], "false": [], "unknown": []}
    attributed: list[str] = []
    for row in rows:
        s = row.get("survives_cv01_bridge_constraints")
        cid = row.get("candidate_id")
        if s in by_status and isinstance(cid, str):
            by_status[s].append(cid)
        if bool(row.get("cv01_attributed_elimination")) and isinstance(cid, str):
            attributed.append(cid)

    summary = {
        "counts": {k: int(len(v)) for k, v in by_status.items()},
        "candidates": {k: list(v) for k, v in by_status.items()},
        "cv01_attributed_eliminations": list(attributed),
        "cv01_attributed_elimination_count": int(len(attributed)),
        "survivor_guard": bool(len(by_status["true"]) >= 1),
    }

    status_reasons: list[str] = []
    if bool((base.status or {}).get("blocked")):
        status_reasons.append("base_pruning_status_blocked")
    if bool((cv01.status or {}).get("blocked")):
        status_reasons.append("cv01_record_blocked")

    return OVCVBR01PruningBridgeRecord(
        schema="OV-CV-BR-01_cv01_v1_pruning_bridge/v1",
        date=str(date),
        observable_id="OV-CV-BR-01",
        status={
            "blocked": bool(len(status_reasons) >= 1),
            "reasons": status_reasons,
            "cv01_tolerance_profile": str(cv01_tolerance_profile),
        },
        inputs={
            "policy": {
                "path": str(resolved_policy),
                "raw_sha256": str(policy_sha),
                "schema": str(policy_doc.get("schema")),
                "version": int(policy_doc.get("version")),
                "present": True,
            },
            "OV-DR-BR-01": {
                "schema": str(base.schema),
                "record_fingerprint": str(base.fingerprint()),
                "status_blocked": bool((base.status or {}).get("blocked")),
            },
            "OV-CV-01_v1": {
                "schema": str(cv01.schema),
                "record_fingerprint": str(cv01.fingerprint()),
                "status_blocked": bool((cv01.status or {}).get("blocked")),
                "artifact_dir": str((cv01.inputs or {}).get("artifact_dir", "")),
            },
        },
        mapping_policy={
            "schema": str(policy_doc.get("schema")),
            "version": int(policy_doc.get("version")),
            "eliminative_atoms": sorted(eliminative_atoms),
            "reason_code_to_atom": dict(reason_code_to_atom),
        },
        active_reason_codes=active_reason_codes,
        active_reason_atoms=active_reason_atoms,
        rows=rows,
        summary=summary,
        scope_limits=[
            "summary_only",
            "eliminative_only",
            "explicit_cv01_reason_atom_mapping",
            "no_implicit_coupling",
            "no_new_claims",
            "survivor_guard_required",
        ],
    )


def render_ovcvbr01_lock_markdown(record: OVCVBR01PruningBridgeRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-CV-BR-01 - CV01 v1 -> pruning bridge (summary-only)\n\n"
        "Scope / limits\n"
        "- Summary-only / eliminative-only bookkeeping\n"
        "- Explicit CV01 reason-code to reason-atom mapping only\n"
        "- No implicit coupling with BR-only pruning lanes\n"
        "- No numeric interpretation and no external truth claim\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovcvbr01_lock(
    *,
    lock_path: Path | None = None,
    date: str = "2026-02-08",
    base_pruning_date: str = "2026-01-25",
    cv01_tolerance_profile: str = "pinned",
    cv01_artifact_dir: Path | None = None,
    policy_path: Path | None = None,
) -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-CV-BR-01_cv01_v1_pruning_bridge.md"
        )

    rec = ovcvbr01_cv01_v1_pruning_bridge_record(
        date=str(date),
        base_pruning_date=str(base_pruning_date),
        cv01_tolerance_profile=str(cv01_tolerance_profile),
        cv01_artifact_dir=cv01_artifact_dir,
        policy_path=policy_path,
    )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovcvbr01_lock_markdown(rec), encoding="utf-8")
    return out
