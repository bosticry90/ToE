from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recordation_execution_20260419_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _maybe_text(raw: Any) -> str:
    return str(raw).strip() if raw is not None else ""


def _all_blank(values: list[str]) -> bool:
    return all(not value.strip() for value in values)


def _all_present(values: list[str]) -> bool:
    return all(value.strip() for value in values)


def _valid_utc_timestamp(value: str) -> bool:
    if not value.strip():
        return False
    try:
        datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ")
        return True
    except ValueError:
        return False


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("approval_recordation_execution_policy", {}))
    contract = dict(declaration.get("approval_recordation_execution_contract", {}))

    approval_record_path = REPO_ROOT / _maybe_text(required_inputs.get("bridge_policy_standard_approval_record_report"))
    recording_procedure_path = REPO_ROOT / _maybe_text(
        required_inputs.get("bridge_policy_standard_approval_recording_procedure_report")
    )
    readiness_dossier_path = REPO_ROOT / _maybe_text(
        required_inputs.get("qm_stat_seam_authorization_readiness_dossier_report")
    )
    note_path = REPO_ROOT / _maybe_text(required_inputs.get("policy_standard_approval_recordation_execution_note"))

    approval_record = _read_json(approval_record_path)
    recording_procedure = _read_json(recording_procedure_path)
    readiness_dossier = _read_json(readiness_dossier_path)
    note_text = _read_text(note_path)

    approval_record_summary = dict(approval_record.get("summary", {}))
    recording_procedure_summary = dict(recording_procedure.get("summary", {}))
    readiness_dossier_summary = dict(readiness_dossier.get("summary", {}))

    approval_record_outcome = _maybe_text(approval_record_summary.get("terminal_outcome"))
    recording_procedure_outcome = _maybe_text(recording_procedure_summary.get("terminal_outcome"))
    readiness_dossier_outcome = _maybe_text(readiness_dossier_summary.get("terminal_outcome"))
    current_restart_blocker = _maybe_text(readiness_dossier_summary.get("current_restart_blocker"))

    required_note_tokens = list(policy.get("required_note_tokens", []))
    required_execution_fields = list(policy.get("required_execution_fields", []))

    approval_decision_id = _maybe_text(policy.get("approval_decision_id"))
    approval_decision_timestamp_utc = _maybe_text(policy.get("approval_decision_timestamp_utc"))
    approval_authority_id = _maybe_text(policy.get("approval_authority_id"))
    approval_attestation_reference = _maybe_text(policy.get("approval_attestation_reference"))

    field_values = [
        approval_decision_id,
        approval_decision_timestamp_utc,
        approval_authority_id,
        approval_attestation_reference,
    ]

    note_tokens_present = all(token in note_text for token in required_note_tokens)
    approval_recordation_execution_defined = bool(policy.get("approval_recordation_execution_defined", False))
    approval_recordation_executed = bool(policy.get("approval_recordation_executed", False))
    policy_standard_approval_recorded = bool(policy.get("policy_standard_approval_recorded", False))
    require_restart_rerun_after_recordation = bool(policy.get("require_restart_rerun_after_recordation", False))

    prerequisites_ok = (
        approval_record_outcome
        == _maybe_text(policy.get("required_policy_standard_approval_record_outcome"))
        and recording_procedure_outcome
        == _maybe_text(policy.get("required_policy_standard_approval_recording_procedure_outcome"))
        and readiness_dossier_outcome
        == _maybe_text(policy.get("required_qm_stat_readiness_dossier_outcome"))
        and current_restart_blocker == _maybe_text(policy.get("required_current_restart_blocker"))
        and note_tokens_present
        and approval_recordation_execution_defined
        and bool(required_execution_fields)
    )

    fields_all_blank = _all_blank(field_values)
    fields_all_present = _all_present(field_values)
    timestamp_valid = _valid_utc_timestamp(approval_decision_timestamp_utc) if fields_all_present else False

    contract_violation = False
    if fields_all_blank:
        contract_violation = approval_recordation_executed or policy_standard_approval_recorded
    else:
        contract_violation = not all(
            [
                fields_all_present,
                timestamp_valid,
                approval_recordation_executed,
                policy_standard_approval_recorded,
                require_restart_rerun_after_recordation,
            ]
        )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = _maybe_text(contract.get("default_outcome"))

    if not prerequisites_ok:
        terminal_outcome = "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_RL10_APPROVAL_RECORDATION_EXECUTION_PRECONDITIONS_AND_RERUN"
    elif contract_violation:
        terminal_outcome = "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_CONTRACT_VIOLATION"
        next_action = "REPAIR_RL10_APPROVAL_RECORDATION_EXECUTION_FIELDS_AND_FLAGS_BEFORE_RESTART_RERUN"
    elif fields_all_present:
        terminal_outcome = "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_RECORDED"
        next_action = "RERUN_QM_STAT_AUTHORIZATION_READINESS_DOSSIER_AND_RESTART_CHAIN_WITHOUT_AUTO_EXECUTION_AUTHORIZATION"
    else:
        terminal_outcome = "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_READY_BUT_UNRECORDED"
        next_action = "WAIT_FOR_REAL_POLICY_STANDARD_APPROVAL_THEN_WRITE_FULL_RECORD_AND_RERUN_RESTART_CHAIN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "policy_standard_approval_record_outcome_match": approval_record_outcome
            == _maybe_text(policy.get("required_policy_standard_approval_record_outcome")),
            "policy_standard_approval_recording_procedure_outcome_match": recording_procedure_outcome
            == _maybe_text(policy.get("required_policy_standard_approval_recording_procedure_outcome")),
            "qm_stat_readiness_dossier_outcome_match": readiness_dossier_outcome
            == _maybe_text(policy.get("required_qm_stat_readiness_dossier_outcome")),
            "current_restart_blocker_match": current_restart_blocker
            == _maybe_text(policy.get("required_current_restart_blocker")),
            "note_tokens_present": note_tokens_present,
            "approval_recordation_execution_defined": approval_recordation_execution_defined,
            "all_execution_fields_blank": fields_all_blank,
            "all_execution_fields_present": fields_all_present,
            "approval_decision_timestamp_valid_utc": timestamp_valid,
            "single_terminal_outcome_rule_declared": _maybe_text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_OUTCOME",
            "no_loop_rule_declared": _maybe_text(contract.get("no_loop_rule"))
            == "ONE_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "recordation_requires_all_required_fields": (
                    terminal_outcome != "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_RECORDED"
                )
                or all([fields_all_present, timestamp_valid]),
                "recordation_does_not_itself_authorize_restart": require_restart_rerun_after_recordation,
            },
            "inputs": {
                "approval_record_outcome": approval_record_outcome,
                "recording_procedure_outcome": recording_procedure_outcome,
                "readiness_dossier_outcome": readiness_dossier_outcome,
                "current_restart_blocker": current_restart_blocker,
                "required_execution_fields": required_execution_fields,
                "approval_recordation_executed": approval_recordation_executed,
                "policy_standard_approval_recorded": policy_standard_approval_recorded,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "current_restart_blocker": current_restart_blocker,
            "approval_recordation_execution_defined": approval_recordation_execution_defined,
            "approval_recordation_executed": approval_recordation_executed,
            "policy_standard_approval_recorded": policy_standard_approval_recorded,
            "approval_decision_id": approval_decision_id or None,
            "approval_decision_timestamp_utc": approval_decision_timestamp_utc or None,
            "approval_authority_id": approval_authority_id or None,
            "approval_attestation_reference": approval_attestation_reference or None,
            "next_action": next_action,
            "single_layer_only": bool(policy.get("single_layer_only", True)),
            "single_outcome_only": bool(policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_policy_standard_approval_record_report": _ptr(approval_record_path),
            "bridge_policy_standard_approval_recording_procedure_report": _ptr(recording_procedure_path),
            "qm_stat_seam_authorization_readiness_dossier_report": _ptr(readiness_dossier_path),
            "policy_standard_approval_recordation_execution_note": _ptr(note_path),
        },
        "non_claim_boundary": "Repository-local RL10 bridge policy standard approval-recordation execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the RL10 bridge policy standard approval-recordation execution report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
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
        "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recordation_execution_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())