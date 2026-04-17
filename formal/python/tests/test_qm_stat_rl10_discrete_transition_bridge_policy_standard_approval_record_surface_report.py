from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_record_surface_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path, *, include_full_shape: bool = True) -> None:
    policy = {
        "required_policy_standard_approval_criteria_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_DECLARED",
        "required_note_tokens": [
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_ID_v0: RL10_BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVAL_RECORD_SURFACE",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_LOCATION_v0: BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_REPORT_SUMMARY",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_TOKEN_v0: policy_standard_approval_recorded",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_PRECONDITION_v0: RECORDING_REQUIRES_A_DECLARED_APPROVAL_CRITERIA_OBJECT",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_FAIL_CLOSED_RULE_v0: IF_NO_EXPLICIT_REPOSITORY_LOCAL_RECORD_EXISTS_THEN_APPROVAL_REMAINS_UNRECORDED",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_STATUS_v0: SURFACE_DECLARED_BUT_APPROVAL_NOT_RECORDED",
        ],
        "policy_standard_approval_record_surface_defined": True,
        "policy_standard_approval_recorded": False,
        "single_layer_only": True,
        "single_outcome_only": True,
    }
    if not include_full_shape:
        policy.pop("policy_standard_approval_recorded")

    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_policy_standard_approval_criteria_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_criteria_20260414_v0.json",
                "policy_standard_approval_record_surface_note": "formal/docs/paper/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_v0.md",
            },
            "policy_standard_approval_record_surface_policy": policy,
            "policy_standard_approval_record_surface_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_OUTCOME",
                "no_loop_rule": "ONE_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_LAYER_ONLY",
                "allowed_outcomes": [
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_DECLARED",
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_REPAIR",
                ],
                "default_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    approval_criteria_outcome: str = "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_DECLARED",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_criteria_20260414_v0.json",
        {"summary": {"terminal_outcome": approval_criteria_outcome}},
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_v0.md",
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_ID_v0: RL10_BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVAL_RECORD_SURFACE\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_LOCATION_v0: BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_REPORT_SUMMARY\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_TOKEN_v0: policy_standard_approval_recorded\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_PRECONDITION_v0: RECORDING_REQUIRES_A_DECLARED_APPROVAL_CRITERIA_OBJECT\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_FAIL_CLOSED_RULE_v0: IF_NO_EXPLICIT_REPOSITORY_LOCAL_RECORD_EXISTS_THEN_APPROVAL_REMAINS_UNRECORDED\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_STATUS_v0: SURFACE_DECLARED_BUT_APPROVAL_NOT_RECORDED\n",
    )


def test_reports_policy_standard_approval_record_surface_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_DECLARED"
    assert report["summary"]["policy_standard_approval_recorded"] is False


def test_reports_policy_standard_approval_record_surface_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, approval_criteria_outcome="RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_policy_standard_approval_record_surface_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_20260414_v0.json"
    _write_declaration(declaration_path, include_full_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_REPAIR"