from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_REPORT_20260414_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_20260414_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("policy_standard_approval_recording_procedure_policy", {}))
    contract = dict(declaration.get("policy_standard_approval_recording_procedure_contract", {}))

    bridge_formalization_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_validation_policy_standard_formalization_report", "")
    ).strip()
    approval_record_path = REPO_ROOT / str(
        required_inputs.get("bridge_policy_standard_approval_record_report", "")
    ).strip()
    restart_trigger_path = REPO_ROOT / str(
        required_inputs.get("science_restart_trigger_contract_report", "")
    ).strip()
    note_path = REPO_ROOT / str(
        required_inputs.get("policy_standard_approval_recording_procedure_note", "")
    ).strip()

    bridge_formalization = _read_json(bridge_formalization_path)
    approval_record = _read_json(approval_record_path)
    restart_trigger = _read_json(restart_trigger_path)
    note_text = _read_text(note_path)

    bridge_formalization_summary = dict(bridge_formalization.get("summary", {}))
    approval_record_summary = dict(approval_record.get("summary", {}))
    restart_trigger_summary = dict(restart_trigger.get("summary", {}))

    bridge_formalization_outcome = str(
        bridge_formalization_summary.get("terminal_outcome", "")
    ).strip()
    approval_record_outcome = str(approval_record_summary.get("terminal_outcome", "")).strip()
    restart_terminal_outcome = str(
        restart_trigger_summary.get(
            "restart_terminal_outcome", restart_trigger_summary.get("terminal_outcome", "")
        )
    ).strip()

    required_bridge_formalization_outcome = str(
        policy.get("required_bridge_external_validation_policy_standard_formalization_outcome", "")
    ).strip()
    required_approval_record_outcome = str(
        policy.get("required_policy_standard_approval_record_outcome", "")
    ).strip()
    required_current_restart_blocker = str(
        policy.get("required_current_restart_blocker", "")
    ).strip()
    required_restart_terminal_outcome = str(
        policy.get("required_restart_terminal_outcome", "")
    ).strip()
    required_note_tokens = list(policy.get("required_note_tokens", []))
    required_execution_fields = list(policy.get("required_execution_fields", []))

    current_restart_blockers = list(
        bridge_formalization_summary.get("remaining_blockers_to_authorization", [])
    )
    record_required_fields = list(approval_record_summary.get("required_approval_record_fields", []))
    policy_standard_approval_recorded = bool(
        approval_record_summary.get("policy_standard_approval_recorded", False)
    )
    approval_record_fields_present = bool(
        approval_record_summary.get("approval_record_fields_present", False)
    )
    approval_recording_procedure_defined = bool(
        policy.get("approval_recording_procedure_defined", False)
    )
    approval_recording_procedure_executed = bool(
        policy.get("approval_recording_procedure_executed", False)
    )
    require_restart_authorization_distinct_from_approval_recording = bool(
        policy.get("require_restart_authorization_distinct_from_approval_recording", False)
    )

    note_tokens_present = all(token in note_text for token in required_note_tokens)
    procedure_shape_ok = all(
        key in policy
        for key in [
            "required_bridge_external_validation_policy_standard_formalization_outcome",
            "required_policy_standard_approval_record_outcome",
            "required_current_restart_blocker",
            "required_restart_terminal_outcome",
            "required_note_tokens",
            "approval_recording_procedure_defined",
            "required_execution_fields",
            "approval_recording_procedure_executed",
            "policy_standard_approval_recorded",
            "require_restart_authorization_distinct_from_approval_recording",
            "single_layer_only",
            "single_outcome_only",
        ]
    )

    preconditions_ok = (
        bridge_formalization_outcome == required_bridge_formalization_outcome
        and approval_record_outcome == required_approval_record_outcome
        and required_current_restart_blocker in current_restart_blockers
        and restart_terminal_outcome == required_restart_terminal_outcome
        and note_tokens_present
        and approval_recording_procedure_defined
        and bool(required_execution_fields)
        and required_execution_fields == record_required_fields
        and not approval_recording_procedure_executed
        and not approval_record_fields_present
        and not policy_standard_approval_recorded
        and require_restart_authorization_distinct_from_approval_recording
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = str(
        contract.get(
            "default_outcome",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_EVIDENCE_INCOMPLETE",
        )
    ).strip()

    if not procedure_shape_ok:
        terminal_outcome = "HOLD_PENDING_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_REPAIR"
        next_action = "REPAIR_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_DEFINED"
        next_action = "IF_HIGHER_LEVEL_POLICY_APPROVAL_IS_ACTUALLY_GRANTED_WRITE_A_VALID_APPROVAL_RECORD_THEN_RERUN_THE_RESTART_CHAIN"
    else:
        terminal_outcome = "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "bridge_external_validation_policy_standard_formalization_outcome_match": bridge_formalization_outcome
            == required_bridge_formalization_outcome,
            "policy_standard_approval_record_outcome_match": approval_record_outcome
            == required_approval_record_outcome,
            "current_restart_blocker_match": required_current_restart_blocker in current_restart_blockers,
            "restart_terminal_outcome_match": restart_terminal_outcome
            == required_restart_terminal_outcome,
            "note_tokens_present": note_tokens_present,
            "approval_recording_procedure_defined": approval_recording_procedure_defined,
            "required_execution_fields_match": required_execution_fields == record_required_fields,
            "approval_recording_procedure_executed": approval_recording_procedure_executed,
            "approval_record_fields_present": approval_record_fields_present,
            "policy_standard_approval_recorded": policy_standard_approval_recorded,
            "restart_authorization_distinct_from_approval_recording": require_restart_authorization_distinct_from_approval_recording,
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "approval_recording_procedure_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "bridge_external_validation_policy_standard_formalization_outcome": bridge_formalization_outcome,
                "policy_standard_approval_record_outcome": approval_record_outcome,
                "current_restart_blockers": current_restart_blockers,
                "restart_terminal_outcome": restart_terminal_outcome,
                "required_execution_fields": required_execution_fields,
                "record_required_fields": record_required_fields,
                "approval_record_fields_present": approval_record_fields_present,
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
            "current_restart_blocker": required_current_restart_blocker,
            "required_execution_fields": required_execution_fields,
            "approval_recording_procedure_defined": approval_recording_procedure_defined,
            "approval_recording_procedure_executed": approval_recording_procedure_executed,
            "policy_standard_approval_recorded": policy_standard_approval_recorded,
            "restart_terminal_outcome": restart_terminal_outcome,
            "next_action": next_action,
            "single_layer_only": bool(policy.get("single_layer_only", True)),
            "single_outcome_only": bool(policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_external_validation_policy_standard_formalization_report": _ptr(bridge_formalization_path),
            "bridge_policy_standard_approval_record_report": _ptr(approval_record_path),
            "science_restart_trigger_contract_report": _ptr(restart_trigger_path),
            "policy_standard_approval_recording_procedure_note": _ptr(note_path),
        },
        "non_claim_boundary": "Repository-local RL10 bridge policy standard approval-recording procedure report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the RL10 bridge policy standard approval-recording procedure report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recording_procedure_20260414_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recording_procedure_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())