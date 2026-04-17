from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recording_procedure_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path, *, include_full_shape: bool = True) -> None:
    policy = {
        "required_bridge_external_validation_policy_standard_formalization_outcome": "EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALLY_DEFINED_BUT_NOT_APPROVED",
        "required_policy_standard_approval_record_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_DECLARED",
        "required_current_restart_blocker": "policy_standard_approval_not_recorded",
        "required_restart_terminal_outcome": "REMAIN_IN_GOVERNED_STOP_STATE",
        "required_note_tokens": [
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_ID_v0: RL10_BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_SCOPE_v0: ONE_DECLARED_REPOSITORY_LOCAL_APPROVAL_RECORDATION_PATH_ONLY",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_PRECONDITION_v0: BRIDGE_POLICY_STANDARD_FORMALIZATION_DEFINED_PLUS_APPROVAL_RECORD_OBJECT_DECLARED_PLUS_RESTART_STOP_STATE_ACTIVE",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_REQUIRED_FIELDS_v0: APPROVAL_DECISION_ID_PLUS_APPROVAL_DECISION_TIMESTAMP_UTC_PLUS_APPROVAL_AUTHORITY_ID_PLUS_APPROVAL_ATTESTATION_REFERENCE",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_NON_EQUIVALENCE_RULE_v0: RECORDING_APPROVAL_DOES_NOT_ITSELF_AUTHORIZE_RESTART_OR_OPEN_QM_STAT_EXECUTION",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_FAIL_CLOSED_RULE_v0: IF_ANY_REQUIRED_FIELD_OR_ATTESTATION_IS_MISSING_APPROVAL_REMAINS_UNRECORDED_AND_RESTART_STAYS_CLOSED",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_STATUS_v0: PROCEDURE_DEFINED_BUT_NOT_EXECUTED",
        ],
        "approval_recording_procedure_defined": True,
        "required_execution_fields": [
            "approval_decision_id",
            "approval_decision_timestamp_utc",
            "approval_authority_id",
            "approval_attestation_reference",
        ],
        "approval_recording_procedure_executed": False,
        "policy_standard_approval_recorded": False,
        "require_restart_authorization_distinct_from_approval_recording": True,
        "single_layer_only": True,
        "single_outcome_only": True,
    }
    if not include_full_shape:
        policy.pop("require_restart_authorization_distinct_from_approval_recording")

    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_external_validation_policy_standard_formalization_report": "formal/output/reports/bridge_external_validation_policy_standard_formalization_20260413_v0.json",
                "bridge_policy_standard_approval_record_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_record_20260414_v0.json",
                "science_restart_trigger_contract_report": "formal/output/reports/science_restart_trigger_contract_20260412_v0.json",
                "policy_standard_approval_recording_procedure_note": "formal/docs/paper/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_v0.md",
            },
            "policy_standard_approval_recording_procedure_policy": policy,
            "policy_standard_approval_recording_procedure_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_OUTCOME",
                "no_loop_rule": "ONE_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_LAYER_ONLY",
                "allowed_outcomes": [
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_DEFINED",
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_REPAIR",
                ],
                "default_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    include_restart_blocker: bool = True,
    bridge_formalization_outcome: str = "EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALLY_DEFINED_BUT_NOT_APPROVED",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_standard_formalization_20260413_v0.json",
        {
            "summary": {
                "terminal_outcome": bridge_formalization_outcome,
                "remaining_blockers_to_authorization": ["policy_standard_approval_not_recorded"]
                if include_restart_blocker
                else [],
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_record_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_DECLARED",
                "required_approval_record_fields": [
                    "approval_decision_id",
                    "approval_decision_timestamp_utc",
                    "approval_authority_id",
                    "approval_attestation_reference",
                ],
                "approval_record_fields_present": False,
                "policy_standard_approval_recorded": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_restart_trigger_contract_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "REMAIN_IN_GOVERNED_STOP_STATE",
                "restart_terminal_outcome": "REMAIN_IN_GOVERNED_STOP_STATE",
            }
        },
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_v0.md",
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_ID_v0: RL10_BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_SCOPE_v0: ONE_DECLARED_REPOSITORY_LOCAL_APPROVAL_RECORDATION_PATH_ONLY\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_PRECONDITION_v0: BRIDGE_POLICY_STANDARD_FORMALIZATION_DEFINED_PLUS_APPROVAL_RECORD_OBJECT_DECLARED_PLUS_RESTART_STOP_STATE_ACTIVE\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_REQUIRED_FIELDS_v0: APPROVAL_DECISION_ID_PLUS_APPROVAL_DECISION_TIMESTAMP_UTC_PLUS_APPROVAL_AUTHORITY_ID_PLUS_APPROVAL_ATTESTATION_REFERENCE\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_NON_EQUIVALENCE_RULE_v0: RECORDING_APPROVAL_DOES_NOT_ITSELF_AUTHORIZE_RESTART_OR_OPEN_QM_STAT_EXECUTION\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_FAIL_CLOSED_RULE_v0: IF_ANY_REQUIRED_FIELD_OR_ATTESTATION_IS_MISSING_APPROVAL_REMAINS_UNRECORDED_AND_RESTART_STAYS_CLOSED\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_STATUS_v0: PROCEDURE_DEFINED_BUT_NOT_EXECUTED\n",
    )


def test_reports_policy_standard_approval_recording_procedure_defined(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_DEFINED"
    assert report["summary"]["policy_standard_approval_recorded"] is False


def test_reports_policy_standard_approval_recording_procedure_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, include_restart_blocker=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_policy_standard_approval_recording_procedure_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_20260414_v0.json"
    _write_declaration(declaration_path, include_full_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_REPAIR"