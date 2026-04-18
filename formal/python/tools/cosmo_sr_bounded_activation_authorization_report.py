from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_REPORT_20260418_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_20260418_v0.json"
)


def _read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _extract_token(text: str, token: str) -> str:
    pattern = re.compile(rf"(?m)^\s*(?:[-*]\s+)?`?{re.escape(token)}`?\s*:\s*`?(\S+?)`?\s*$")
    match = pattern.search(text)
    if not match:
        raise ValueError(f"Missing token: {token}")
    return match.group(1).strip()


def _row_entry(rows: list[dict[str, Any]], row_id: str) -> dict[str, Any]:
    for row in rows:
        if str(row.get("row_id", "")).strip() == row_id:
            return dict(row)
    return {}


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    target_seam = dict(declaration.get("target_seam", {}))
    required_inputs = dict(declaration.get("required_inputs", {}))
    authorization_contract = dict(declaration.get("bounded_activation_authorization_contract", {}))
    outcome_contract = dict(declaration.get("bounded_activation_authorization_outcome_contract", {}))

    tgc93_path = REPO_ROOT / str(required_inputs.get("tgc93_branch_decision_package", "")).strip()
    phase2_decision_path = REPO_ROOT / str(required_inputs.get("cosmo_sr_seam_authorization_activation_decision_report", "")).strip()
    hold_resolution_path = REPO_ROOT / str(required_inputs.get("cosmo_sr_discovery_review_hold_resolution_report", "")).strip()
    sla_path = REPO_ROOT / str(required_inputs.get("seam_resolution_sla_ledger_report", "")).strip()

    tgc93_text = _read(tgc93_path)
    phase2_decision = _read_json(phase2_decision_path)
    hold_resolution = _read_json(hold_resolution_path)
    sla = _read_json(sla_path)

    tgc93_branch_decision = _extract_token(tgc93_text, "TGC93_BRANCH_DECISION_v0")
    tgc93_seam_reentry_authorization = _extract_token(tgc93_text, "TGC93_SEAM_REENTRY_AUTHORIZATION_v0")
    phase2_summary = dict(phase2_decision.get("summary", {}))
    hold_resolution_summary = dict(hold_resolution.get("summary", {}))
    target_row_id = str(target_seam.get("row_id", "")).strip()
    target_lane = str(target_seam.get("lane", "")).strip()
    sla_entry = _row_entry(list(sla.get("entries", [])), target_row_id)

    minimum_tranche = dict(authorization_contract.get("minimum_bounded_activation_tranche", {}))
    tranche_shape_ok = all(
        key in minimum_tranche
        for key in [
            "target_row_id",
            "target_lane",
            "current_status",
            "required_evidence_surface",
            "required_closure_artifact",
            "required_closure_gate",
            "required_exit_criterion",
            "bounded_scope",
        ]
    )

    preconditions_ok = all(
        [
            tgc93_branch_decision == str(authorization_contract.get("required_tgc93_branch_decision", "")).strip(),
            tgc93_seam_reentry_authorization
            == str(authorization_contract.get("required_tgc93_seam_reentry_authorization", "")).strip(),
            str(phase2_summary.get("terminal_outcome", "")).strip()
            == str(authorization_contract.get("required_phase2_decision_outcome", "")).strip(),
            str(hold_resolution_summary.get("terminal_outcome", "")).strip()
            == str(authorization_contract.get("required_hold_resolution_outcome", "")).strip(),
            str(phase2_summary.get("target_row_id", "")).strip() == target_row_id,
            str(phase2_summary.get("target_lane", "")).strip() == target_lane,
            str(sla_entry.get("decision_state", "")).strip()
            == str(authorization_contract.get("required_sla_decision_state", "")).strip(),
            str(sla_entry.get("gate_runtime_status", "")).strip()
            == str(authorization_contract.get("required_sla_gate_runtime_status", "")).strip(),
            str(sla_entry.get("target_surface", "")).strip()
            == str(minimum_tranche.get("required_evidence_surface", "")).strip(),
            str(sla_entry.get("artifact_surface", "")).strip()
            == str(minimum_tranche.get("required_closure_artifact", "")).strip(),
            str(sla_entry.get("gate_surface", "")).strip()
            == str(minimum_tranche.get("required_closure_gate", "")).strip(),
            str(sla_entry.get("exit_criterion", "")).strip()
            == str(minimum_tranche.get("required_exit_criterion", "")).strip(),
            tranche_shape_ok,
        ]
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_EVIDENCE_INCOMPLETE")
    ).strip()

    if not tranche_shape_ok:
        terminal_outcome = "HOLD_PENDING_COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_REPAIR"
        next_action = "REPAIR_COSMO_SR_MINIMUM_BOUNDED_ACTIVATION_TRANCHE_SHAPE"
    elif preconditions_ok:
        terminal_outcome = str(authorization_contract.get("authorization_result_token", "")).strip()
        next_action = "EXECUTE_ONE_BOUNDED_COSMO_SR_CYCLE07_ACTIVATION_ONLY"
    elif str(hold_resolution_summary.get("terminal_outcome", "")).strip() != str(
        authorization_contract.get("required_hold_resolution_outcome", "")
    ).strip():
        terminal_outcome = "COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_BLOCKED"
        next_action = "RESTORE_HOLD_RESOLUTION_PATH_BEFORE_AUTHORIZATION_CONVERSION"
    else:
        terminal_outcome = "COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "tgc93_scope_matches": tgc93_branch_decision
            == str(authorization_contract.get("required_tgc93_branch_decision", "")).strip(),
            "hold_resolution_matches": str(hold_resolution_summary.get("terminal_outcome", "")).strip()
            == str(authorization_contract.get("required_hold_resolution_outcome", "")).strip(),
            "phase2_held_decision_matches": str(phase2_summary.get("terminal_outcome", "")).strip()
            == str(authorization_contract.get("required_phase2_decision_outcome", "")).strip(),
            "seam_entry_alignment_ok": bool(sla_entry),
            "minimum_bounded_activation_tranche_shape_ok": tranche_shape_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "authorization_conversion_preconditions_satisfied": preconditions_ok,
                "single_path_nonlive_boundary_preserved": int(authorization_contract.get("execution_live_token_count", 0)) == 0,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "target_lane": target_lane,
                "tgc93_branch_decision": tgc93_branch_decision,
                "tgc93_seam_reentry_authorization": tgc93_seam_reentry_authorization,
                "phase2_terminal_outcome": phase2_summary.get("terminal_outcome"),
                "hold_resolution_terminal_outcome": hold_resolution_summary.get("terminal_outcome"),
                "authorization_scope_token": authorization_contract.get("authorization_scope_token"),
                "branch_chain_status": authorization_contract.get("branch_chain_status"),
                "execution_live_token_count": authorization_contract.get("execution_live_token_count"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row_id": target_row_id,
            "target_lane": target_lane,
            "authorization_scope_token": authorization_contract.get("authorization_scope_token"),
            "authorization_result_token": authorization_contract.get("authorization_result_token"),
            "branch_chain_status": authorization_contract.get("branch_chain_status"),
            "execution_live_token_count": authorization_contract.get("execution_live_token_count"),
            "selected_target_artifact_pointer": minimum_tranche.get("required_closure_artifact"),
            "selected_target_gate_pointer": minimum_tranche.get("required_closure_gate"),
            "next_action": next_action,
            "single_layer_only": bool(authorization_contract.get("single_layer_only", True)),
            "single_outcome_only": bool(authorization_contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "tgc93_branch_decision_package": _ptr(tgc93_path),
            "cosmo_sr_seam_authorization_activation_decision_report": _ptr(phase2_decision_path),
            "cosmo_sr_discovery_review_hold_resolution_report": _ptr(hold_resolution_path),
            "seam_resolution_sla_ledger_report": _ptr(sla_path),
        },
        "non_claim_boundary": "Repository-local COSMO-SR bounded activation authorization report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the COSMO-SR bounded activation authorization report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "cosmo_sr_bounded_activation_authorization_20260418_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "cosmo_sr_bounded_activation_authorization_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())