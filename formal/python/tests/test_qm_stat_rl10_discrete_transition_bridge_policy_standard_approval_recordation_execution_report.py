from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recordation_execution_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    approval_decision_id: str = "",
    approval_decision_timestamp_utc: str = "",
    approval_authority_id: str = "",
    approval_attestation_reference: str = "",
    approval_recordation_executed: bool = False,
    policy_standard_approval_recorded: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_policy_standard_approval_record_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_record_20260414_v0.json",
                "bridge_policy_standard_approval_recording_procedure_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recording_procedure_20260414_v0.json",
                "qm_stat_seam_authorization_readiness_dossier_report": "formal/output/reports/qm_stat_seam_authorization_readiness_dossier_20260414_v0.json",
                "policy_standard_approval_recordation_execution_note": "formal/docs/paper/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_v0.md",
            },
            "approval_recordation_execution_policy": {
                "required_policy_standard_approval_record_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_DECLARED",
                "required_policy_standard_approval_recording_procedure_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_DEFINED",
                "required_qm_stat_readiness_dossier_outcome": "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_READY_FOR_BOUNDED_PRE_SCREENING",
                "required_current_restart_blocker": "",
                "required_note_tokens": [
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_ID_v0: RL10_BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION",
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_SCOPE_v0: ONE_REPOSITORY_LOCAL_APPROVAL_RECORD_WRITE_PATH_ONLY",
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_REQUIRED_FIELDS_v0: APPROVAL_DECISION_ID_PLUS_APPROVAL_DECISION_TIMESTAMP_UTC_PLUS_APPROVAL_AUTHORITY_ID_PLUS_APPROVAL_ATTESTATION_REFERENCE",
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_NON_EQUIVALENCE_RULE_v0: RECORDING_APPROVAL_DOES_NOT_ITSELF_AUTHORIZE_RESTART_OR_OPEN_QM_STAT_EXECUTION",
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_FAIL_CLOSED_RULE_v0: IF_ANY_REQUIRED_FIELD_IS_MISSING_OR_PARTIAL_APPROVAL_REMAINS_UNRECORDED",
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_STATUS_v0: EXECUTION_SURFACE_DECLARED_DEFAULT_UNRECORDED",
                ],
                "required_execution_fields": [
                    "approval_decision_id",
                    "approval_decision_timestamp_utc",
                    "approval_authority_id",
                    "approval_attestation_reference",
                ],
                "approval_recordation_execution_defined": True,
                "approval_decision_id": approval_decision_id,
                "approval_decision_timestamp_utc": approval_decision_timestamp_utc,
                "approval_authority_id": approval_authority_id,
                "approval_attestation_reference": approval_attestation_reference,
                "approval_recordation_executed": approval_recordation_executed,
                "policy_standard_approval_recorded": policy_standard_approval_recorded,
                "require_restart_rerun_after_recordation": True,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "approval_recordation_execution_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_OUTCOME",
                "no_loop_rule": "ONE_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_LAYER_ONLY",
                "allowed_outcomes": [
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_READY_BUT_UNRECORDED",
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_RECORDED",
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_CONTRACT_VIOLATION",
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_EVIDENCE_INCOMPLETE",
                ],
                "default_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_record_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_DECLARED",
            }
        },
    )
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recording_procedure_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_DEFINED",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_seam_authorization_readiness_dossier_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_READY_FOR_BOUNDED_PRE_SCREENING",
                "current_restart_blocker": "",
            }
        },
    )
    _write_text(
        root
        / "formal"
        / "docs"
        / "paper"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_v0.md",
        "\n".join(
            [
                "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_ID_v0: RL10_BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION",
                "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_SCOPE_v0: ONE_REPOSITORY_LOCAL_APPROVAL_RECORD_WRITE_PATH_ONLY",
                "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_REQUIRED_FIELDS_v0: APPROVAL_DECISION_ID_PLUS_APPROVAL_DECISION_TIMESTAMP_UTC_PLUS_APPROVAL_AUTHORITY_ID_PLUS_APPROVAL_ATTESTATION_REFERENCE",
                "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_NON_EQUIVALENCE_RULE_v0: RECORDING_APPROVAL_DOES_NOT_ITSELF_AUTHORIZE_RESTART_OR_OPEN_QM_STAT_EXECUTION",
                "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_FAIL_CLOSED_RULE_v0: IF_ANY_REQUIRED_FIELD_IS_MISSING_OR_PARTIAL_APPROVAL_REMAINS_UNRECORDED",
                "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_STATUS_v0: EXECUTION_SURFACE_DECLARED_DEFAULT_UNRECORDED",
            ]
        ),
    )


def test_recordation_execution_ready_but_unrecorded_by_default(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_20260419_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["terminal_outcome"]
        == "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_READY_BUT_UNRECORDED"
    )


def test_recordation_execution_records_when_all_fields_are_present(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_20260419_v0.json"
    )
    _write_declaration(
        declaration_path,
        approval_decision_id="RL10-POLICY-APPROVAL-001",
        approval_decision_timestamp_utc="2026-04-19T16:30:00Z",
        approval_authority_id="QM_STAT_POLICY_AUTHORITY",
        approval_attestation_reference="formal/docs/release/RL10_POLICY_STANDARD_APPROVAL_ATTESTATION_20260419_v0.md",
        approval_recordation_executed=True,
        policy_standard_approval_recorded=True,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["terminal_outcome"]
        == "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_RECORDED"
    )


def test_recordation_execution_rejects_partial_fields(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_20260419_v0.json"
    )
    _write_declaration(
        declaration_path,
        approval_decision_id="RL10-POLICY-APPROVAL-001",
        approval_decision_timestamp_utc="",
        approval_authority_id="QM_STAT_POLICY_AUTHORITY",
        approval_attestation_reference="",
        approval_recordation_executed=True,
        policy_standard_approval_recorded=False,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["terminal_outcome"]
        == "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_CONTRACT_VIOLATION"
    )


def test_live_recordation_execution_registered_in_mirrors() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_20260419_v0.json",
        "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recordation_execution_20260419_v0.json",
        "formal/python/tools/qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recordation_execution_report.py",
        "formal/python/tests/test_qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recordation_execution_report.py",
    ]

    for ref in required_refs:
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recordation_execution_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_RECORDED"