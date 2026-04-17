from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_approval_eligible_policy_review_outcome_report as tool,
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
        "required_material_repeatability_admissibility_criteria_outcome": "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_DECLARED",
        "required_policy_standard_approval_criteria_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_DECLARED",
        "required_note_tokens": [
            "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_ID_v0: RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME",
            "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_SCOPE_v0: ONE_NAMED_REPEATABILITY_PATH_ONLY",
            "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_REQUIRED_SURFACES_v0: NAMED_REPEATABILITY_CHECK_PLUS_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_PLUS_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_PLUS_POLICY_STANDARD_APPROVAL_CRITERIA",
            "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_ELIGIBILITY_RULE_v0: REVIEW_ELIGIBILITY_REQUIRES_DECLARED_SURFACES_AND_A_NAMED_ADMISSIBLE_REPEATABILITY_CHECK",
            "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_PROHIBITION_RULE_v0: ELIGIBILITY_MUST_NOT_RECORD_APPROVAL_OR_AUTHORIZE_RESTART",
            "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_DISTINCTION_RULE_v0: ELIGIBILITY_ONLY_PERMITS_POLICY_REVIEW_TO_EMIT_AN_APPROVAL_ELIGIBLE_OUTCOME_APPROVAL_REMAINS_SEPARATELY_RECORDED",
            "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_STATUS_v0: ELIGIBILITY_SURFACE_DECLARED_BUT_APPROVAL_STILL_UNRECORDED",
        ],
        "approval_eligible_repeatability_review_outcome_defined": True,
        "require_named_bounded_repeatability_check_only": True,
        "require_material_repeatability_admissibility_criteria_defined": True,
        "require_minimum_second_cycle_evidence_object_declared": True,
        "require_policy_standard_approval_criteria_defined": True,
        "require_approval_record_distinct_from_review_eligibility": True,
        "single_layer_only": True,
        "single_outcome_only": True,
    }
    if not include_full_shape:
        policy.pop("require_approval_record_distinct_from_review_eligibility")

    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_first_named_repeatability_check_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_20260414_v0.json",
                "bridge_minimum_second_cycle_evidence_object_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_20260414_v0.json",
                "bridge_material_repeatability_admissibility_criteria_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_material_repeatability_admissibility_criteria_20260414_v0.json",
                "bridge_policy_standard_approval_criteria_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_criteria_20260414_v0.json",
                "approval_eligible_policy_review_outcome_note": "formal/docs/paper/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_v0.md",
            },
            "approval_eligible_policy_review_outcome_policy": policy,
            "approval_eligible_policy_review_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME",
                "no_loop_rule": "ONE_RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_LAYER_ONLY",
                "allowed_outcomes": [
                    "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_DECLARED",
                    "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_REPAIR",
                ],
                "default_outcome": "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    named_check_admissible: bool = True,
    minimum_second_cycle_evidence_defined: bool = True,
    policy_standard_approval_recorded: bool = False,
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_DECLARED",
                "named_check_admissible": named_check_admissible,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_DECLARED",
                "second_cycle_minimum_evidence_defined": minimum_second_cycle_evidence_defined,
                "second_cycle_minimum_evidence_satisfied": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_material_repeatability_admissibility_criteria_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_DECLARED",
                "repeatability_admissibility_criteria_defined": True,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_criteria_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_DECLARED",
                "policy_standard_approval_criteria_defined": True,
                "approval_attestation_surfaces_declared": True,
                "approval_minimum_evidence_requirement_defined": True,
                "policy_standard_approval_recorded": policy_standard_approval_recorded,
            }
        },
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_v0.md",
        "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_ID_v0: RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME\n"
        "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_SCOPE_v0: ONE_NAMED_REPEATABILITY_PATH_ONLY\n"
        "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_REQUIRED_SURFACES_v0: NAMED_REPEATABILITY_CHECK_PLUS_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_PLUS_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_PLUS_POLICY_STANDARD_APPROVAL_CRITERIA\n"
        "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_ELIGIBILITY_RULE_v0: REVIEW_ELIGIBILITY_REQUIRES_DECLARED_SURFACES_AND_A_NAMED_ADMISSIBLE_REPEATABILITY_CHECK\n"
        "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_PROHIBITION_RULE_v0: ELIGIBILITY_MUST_NOT_RECORD_APPROVAL_OR_AUTHORIZE_RESTART\n"
        "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_DISTINCTION_RULE_v0: ELIGIBILITY_ONLY_PERMITS_POLICY_REVIEW_TO_EMIT_AN_APPROVAL_ELIGIBLE_OUTCOME_APPROVAL_REMAINS_SEPARATELY_RECORDED\n"
        "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_STATUS_v0: ELIGIBILITY_SURFACE_DECLARED_BUT_APPROVAL_STILL_UNRECORDED\n",
    )


def test_reports_approval_eligible_policy_review_outcome_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_DECLARED"
    assert report["summary"]["policy_standard_approval_recorded"] is False


def test_reports_approval_eligible_policy_review_outcome_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, named_check_admissible=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_approval_eligible_policy_review_outcome_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_20260414_v0.json"
    _write_declaration(declaration_path, include_full_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_REPAIR"