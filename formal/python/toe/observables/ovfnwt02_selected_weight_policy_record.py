"""OV-FN-WT-02: selected FN-01 weight policy (computed selection).

Purpose
- Consume OV-FN-WT-01 (weight policy pruning table) and deterministically select
  the single surviving weight-policy candidate.
- If 0 or >1 policies survive, the record is BLOCKED with explicit reasons.

Scope / limits
- Bookkeeping / selection only; no physics claim.
- Deterministic and lock-derived.
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


def _extract_json_block(md_text: str) -> dict[str, Any]:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise ValueError("Missing JSON record block")
    return json.loads(m.group(1))


def _extract_record_fingerprint(md_text: str) -> str:
    m = re.search(r"Record fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise ValueError("Missing record fingerprint line")
    return m.group(1)


def _format_float_stable(x: float | None) -> str | None:
    if x is None:
        return None
    try:
        return format(float(x), ".12g")
    except Exception:  # noqa: BLE001
        return None


@dataclass(frozen=True)
class OVFNWT02SelectedWeightPolicyRecord:
    schema: str
    date: str

    observable_id: str
    status: dict[str, Any]

    inputs: dict[str, Any]
    selection: dict[str, Any]

    scope_limits: list[str]

    def fingerprint_payload(self) -> dict[str, Any]:
        """Stable payload for fingerprinting.

        Critical rule: the fingerprint must not depend on upstream lock paths or
        upstream lock fingerprints (those may include paths). It binds only to:
        - the selected policy id
        - the selected policy parameters (w_fn, max_score)
        - the selected policy's br_candidate_id
        - the selection outcome flags
        - admissibility manifest sha/version (not path)
        """

        status = dict(self.status)
        adm = dict(status.get("admissibility_manifest") or {})
        adm.pop("path", None)
        status["admissibility_manifest"] = adm

        selected_row = self.selection.get("selected_row")
        w_fn_s: str | None = None
        max_score_s: str | None = None
        br_candidate_id: str | None = None
        if isinstance(selected_row, dict):
            w_fn_s = _format_float_stable(selected_row.get("w_fn"))
            max_score_s = _format_float_stable(selected_row.get("max_score"))
            br_candidate_id = selected_row.get("br_candidate_id")

        survivors = self.selection.get("surviving_policy_ids")
        survivors_sorted = sorted([str(x) for x in survivors]) if isinstance(survivors, list) else []

        reasons = status.get("reasons")
        reasons_sorted = sorted([str(x) for x in reasons]) if isinstance(reasons, list) else []

        required = status.get("required_gates")
        required_sorted = sorted([str(x) for x in required]) if isinstance(required, list) else []

        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "blocked": bool(status.get("blocked")),
            "required_gates": required_sorted,
            "reasons": reasons_sorted,
            "admissibility_manifest": {
                "sha256": adm.get("sha256"),
                "version": adm.get("version"),
            },
            "selection": {
                "selected_policy_id": self.selection.get("selected_policy_id"),
                "selected_policy_parameters": {
                    "w_fn": w_fn_s,
                    "max_score": max_score_s,
                    "br_candidate_id": br_candidate_id,
                },
                "surviving_policy_ids": survivors_sorted,
                "computed_under_blocked_admissibility": bool(self.selection.get("computed_under_blocked_admissibility")),
            },
            "scope_limits": list(self.scope_limits),
        }

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "status": dict(self.status),
            "inputs": dict(self.inputs),
            "selection": dict(self.selection),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.fingerprint_payload())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovfnwt02_selected_weight_policy_record(
    *,
    date: str = "2026-01-25",
    pruning_lock_path: Path | None = None,
    admissibility_manifest_path: Path | None = None,
) -> OVFNWT02SelectedWeightPolicyRecord:
    repo_root = _find_repo_root(Path(__file__))

    default_pruning = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-FN-WT-01_fn01_weight_policy_pruning_table.md"
    )
    pruning_path = (pruning_lock_path or default_pruning).resolve()

    if not pruning_path.exists():
        status: dict[str, Any] = {
            "blocked": True,
            "reasons": ["missing_input_lock_OV-FN-WT-01"],
            "required_gates": ["CT01", "SYM01", "CAUS01"],
            "admissibility_manifest": {"path": None, "version": None, "skipped": True},
        }
        return OVFNWT02SelectedWeightPolicyRecord(
            schema="OV-FN-WT-02_selected_weight_policy/v1",
            date=str(date),
            observable_id="OV-FN-WT-02",
            status=status,
            inputs={
                "OV-FN-WT-01": {
                    "expected_path": str(default_pruning),
                    "path": str(pruning_path),
                    "present": False,
                }
            },
            selection={
                "selected_policy_id": None,
                "selected_row": None,
                "surviving_policy_ids": [],
                "computed_under_blocked_admissibility": True,
                "reason_codes": ["missing_input_lock"],
            },
            scope_limits=["blocked_by_missing_input_lock", "blocked_by_default"],
        )

    required_gates = ["CT01", "SYM01", "CAUS01"]
    gate_check = check_required_gates(
        repo_root=repo_root,
        required_gate_ids=required_gates,
        manifest_path=admissibility_manifest_path,
    )

    status: dict[str, Any] = {
        "blocked": bool(gate_check.blocked),
        "reasons": list(gate_check.reasons),
        "required_gates": list(required_gates),
        "admissibility_manifest": {
            "path": str(gate_check.manifest_path),
            "version": gate_check.manifest_version,
            "sha256": gate_check.manifest_sha256,
        },
    }

    pruning_text = pruning_path.read_text(encoding="utf-8")
    pruning_locked = _extract_json_block(pruning_text)
    pruning_fp = _extract_record_fingerprint(pruning_text)

    if bool((pruning_locked.get("status") or {}).get("blocked")):
        status["blocked"] = True
        status["reasons"].append("input_OV-FN-WT-01_is_blocked")

    rows = list(pruning_locked.get("rows") or [])
    survivors = [
        str(r.get("policy_id"))
        for r in rows
        if isinstance(r, dict) and r.get("survives_fn_weight_policy_constraints") == "true" and isinstance(r.get("policy_id"), str)
    ]
    survivors = sorted(set(survivors))

    reason_codes: list[str] = []
    selected_policy_id: str | None = None
    selected_row: dict[str, Any] | None = None

    if len(survivors) == 1:
        selected_policy_id = survivors[0]
        for r in rows:
            if isinstance(r, dict) and r.get("policy_id") == selected_policy_id:
                selected_row = dict(r)
                break
        reason_codes.append("unique_survivor_selected")
    elif len(survivors) == 0:
        status["blocked"] = True
        reason_codes.append("zero_survivors")
        status["reasons"].append("selection_zero_survivors")
    else:
        status["blocked"] = True
        reason_codes.append("multiple_survivors")
        status["reasons"].append("selection_multiple_survivors")

    computed_under_blocked_admissibility = bool(status.get("blocked"))
    if computed_under_blocked_admissibility and "computed_under_blocked_admissibility" not in reason_codes:
        reason_codes.append("computed_under_blocked_admissibility")

    inputs = {
        "OV-FN-WT-01": {
            "path": str(pruning_path),
            "schema": str(pruning_locked.get("schema")),
            "locked_fingerprint": str(pruning_fp),
            "record_fingerprint": str(pruning_locked.get("fingerprint")),
            "present": True,
        }
    }

    selection = {
        "selected_policy_id": selected_policy_id,
        "selected_row": selected_row,
        "surviving_policy_ids": survivors,
        "computed_under_blocked_admissibility": bool(computed_under_blocked_admissibility),
        "reason_codes": reason_codes,
    }

    scope_limits = [
        "selection_only",
        "lock_derived",
        "no_new_claims",
    ]

    return OVFNWT02SelectedWeightPolicyRecord(
        schema="OV-FN-WT-02_selected_weight_policy/v1",
        date=str(date),
        observable_id="OV-FN-WT-02",
        status=status,
        inputs=inputs,
        selection=selection,
        scope_limits=scope_limits,
    )


def render_ovfnwt02_lock_markdown(record: OVFNWT02SelectedWeightPolicyRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-FN-WT-02 - Selected FN weight policy (computed)\n\n"
        "Scope / limits\n"
        "- Selection-only bookkeeping; no physics claim\n"
        "- Deterministic; computed only from existing locks\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovfnwt02_lock(
    *,
    lock_path: Path | None = None,
    date: str = "2026-01-25",
    pruning_lock_path: Path | None = None,
    admissibility_manifest_path: Path | None = None,
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
            / "OV-FN-WT-02_selected_weight_policy.md"
        )

    rec = ovfnwt02_selected_weight_policy_record(
        date=str(date),
        pruning_lock_path=pruning_lock_path,
        admissibility_manifest_path=admissibility_manifest_path,
    )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovfnwt02_lock_markdown(rec), encoding="utf-8")
    return out
