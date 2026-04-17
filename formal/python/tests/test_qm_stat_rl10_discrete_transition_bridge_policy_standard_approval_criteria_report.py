from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_criteria_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path, *, include_full_shape: bool = True) -> None:
    policy = {
        "required_named_repeatability_check_outcome": "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_DECLARED",
        "required_minimum_second_cycle_evidence_object_outcome": "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_DECLARED",
        "required_note_tokens": [
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_ID_v0: RL10_BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVAL_CRITERIA",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_ATTESTATION_SURFACES_v0: BRIDGE_EXTERNAL_VALIDATION_POLICY_REVIEW_REPORT_AND_BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_REPORT",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_MINIMUM_EVIDENCE_RULE_v0: MATERIAL_SECOND_CYCLE_EVIDENCE_SATISFACTION_REQUIRED_BEFORE_APPROVAL",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_RULE_v0: APPROVAL_REQUIRES_EXPLICIT_REPOSITORY_LOCAL_ATTESTATION_ON_DECLARED_SURFACES",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_BOUNDARY_RULE_v0: APPROVAL_CRITERIA_MUST_NOT_EXPAND_SCOPE_BEYOND_ONE_DECLARED_BOUNDED_CHECK_FAMILY_WITHOUT_NEW_DECLARATION",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_FAIL_CLOSED_RULE_v0: IF_ATTESTATION_SURFACES_OR_MINIMUM_EVIDENCE_REQUIREMENT_ARE_UNCLEAR_APPROVAL_REMAINS_UNAVAILABLE",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_STATUS_v0: CRITERIA_DECLARED_BUT_APPROVAL_NOT_RECORDED",
        ],
        "policy_standard_approval_criteria_defined": True,
        "approval_attestation_surfaces_declared": True,
        "approval_minimum_evidence_requirement_defined": True,
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
                "bridge_first_named_repeatability_check_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_20260414_v0.json",
                "bridge_minimum_second_cycle_evidence_object_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_20260414_v0.json",
                "policy_standard_approval_criteria_note": "formal/docs/paper/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_v0.md",
            },
            "policy_standard_approval_criteria_policy": policy,
            "policy_standard_approval_criteria_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_OUTCOME",
                "no_loop_rule": "ONE_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_LAYER_ONLY",
                "allowed_outcomes": [
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_DECLARED",
                    "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_REPAIR",
                ],
                "default_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    named_check_outcome: str = "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_DECLARED",
    named_check_admissible: bool = True,
    minimum_evidence_outcome: str = "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_DECLARED",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": named_check_outcome,
                "named_check_admissible": named_check_admissible,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_20260414_v0.json",
        {"summary": {"terminal_outcome": minimum_evidence_outcome}},
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_v0.md",
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_ID_v0: RL10_BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVAL_CRITERIA\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_ATTESTATION_SURFACES_v0: BRIDGE_EXTERNAL_VALIDATION_POLICY_REVIEW_REPORT_AND_BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_REPORT\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_MINIMUM_EVIDENCE_RULE_v0: MATERIAL_SECOND_CYCLE_EVIDENCE_SATISFACTION_REQUIRED_BEFORE_APPROVAL\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_RULE_v0: APPROVAL_REQUIRES_EXPLICIT_REPOSITORY_LOCAL_ATTESTATION_ON_DECLARED_SURFACES\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_BOUNDARY_RULE_v0: APPROVAL_CRITERIA_MUST_NOT_EXPAND_SCOPE_BEYOND_ONE_DECLARED_BOUNDED_CHECK_FAMILY_WITHOUT_NEW_DECLARATION\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_FAIL_CLOSED_RULE_v0: IF_ATTESTATION_SURFACES_OR_MINIMUM_EVIDENCE_REQUIREMENT_ARE_UNCLEAR_APPROVAL_REMAINS_UNAVAILABLE\n"
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_STATUS_v0: CRITERIA_DECLARED_BUT_APPROVAL_NOT_RECORDED\n",
    )


def test_reports_policy_standard_approval_criteria_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_DECLARED"
    assert report["summary"]["policy_standard_approval_recorded"] is False


def test_reports_policy_standard_approval_criteria_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, minimum_evidence_outcome="RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_policy_standard_approval_criteria_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_20260414_v0.json"
    _write_declaration(declaration_path, include_full_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_REPAIR"