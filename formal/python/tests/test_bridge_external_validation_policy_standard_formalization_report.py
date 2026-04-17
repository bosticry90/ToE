from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import bridge_external_validation_policy_standard_formalization_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path, *, include_full_contract_shape: bool = True) -> None:
    contract = {
        "required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
        "allowed_review_outcomes_for_approval": [
            "ADMISSIBLE_REPEATABILITY_STANDARD_DEFINED",
            "ADMISSIBLE_CROSS_PROBE_STANDARD_DEFINED",
        ],
        "allowed_naming_outcomes_for_standard": [
            "BOUNDED_REPEATABILITY_CHECK_NAMED",
            "BOUNDED_CROSS_PROBE_CHECK_NAMED",
        ],
        "require_declaration_standard_defined": True,
        "require_bounded_check_families_defined": True,
        "require_external_validation_policy_surface": True,
        "require_one_admissible_bounded_check_named": True,
        "require_second_cycle_minimum_evidence_defined": True,
        "require_policy_approval_criteria_defined_for_approval": True,
        "require_approval_attestation_surfaces_declared_for_approval": True,
        "require_approval_minimum_evidence_requirement_defined_for_approval": True,
        "require_policy_standard_approval_record_surface_defined_for_approval": True,
        "require_policy_standard_approval_record_defined_for_approval": True,
        "require_policy_standard_approval_record_for_approval": True,
        "single_layer_only": True,
        "single_outcome_only": True,
    }
    if not include_full_contract_shape:
        contract.pop("require_policy_standard_approval_record_for_approval")

    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
                "bridge_admissibility_standard_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_admissibility_standard_review_20260412_v0.json",
                "bridge_repeatability_check_naming_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json",
                "bridge_bounded_check_family_standard_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_bounded_check_family_standard_20260414_v0.json",
                "bridge_policy_standard_approval_criteria_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_criteria_20260414_v0.json",
                "bridge_policy_standard_approval_record_surface_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_record_surface_20260414_v0.json",
                "bridge_policy_standard_approval_record_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_record_20260414_v0.json",
            },
            "policy_standard_contract": contract,
            "policy_standard_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_OUTCOME",
                "no_loop_rule": "ONE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_LAYER_ONLY",
                "allowed_outcomes": [
                    "EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVED_AND_TRIGGER_AUTHORIZED",
                    "EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALLY_DEFINED_BUT_NOT_APPROVED",
                    "EXTERNAL_VALIDATION_POLICY_STANDARD_INCOMPLETE_HOLD",
                    "HOLD_PENDING_EXTERNAL_VALIDATION_POLICY_STANDARD_REPAIR",
                ],
                "default_outcome": "EXTERNAL_VALIDATION_POLICY_STANDARD_INCOMPLETE_HOLD",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    review_outcome: str = "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
    declaration_standard_defined: bool = False,
    bounded_check_families_defined: bool = False,
    external_validation_policy_surface_defined: bool = False,
    naming_outcome: str = "NO_SPECIFIC_CHECK_JUSTIFIED_YET",
    named_check_admissible: bool = False,
    bounded_scope_declared: bool = False,
    not_disguised_second_full_cycle_declared: bool = False,
    second_cycle_minimum_evidence_defined: bool = False,
    repeatability_defined: bool = False,
    cross_probe_defined: bool = False,
    bounded_check_family_terminal_outcome: str = "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_EVIDENCE_INCOMPLETE",
    bounded_check_family_declaration_standard_defined: bool = False,
    bounded_check_family_surface_defined: bool = False,
    bounded_check_family_families_defined: bool = False,
    policy_approval_criteria_defined: bool = True,
    approval_attestation_surfaces_declared: bool = True,
    approval_minimum_evidence_requirement_defined: bool = True,
    policy_standard_approval_record_surface_defined: bool = True,
    policy_standard_approval_record_defined: bool = True,
    policy_standard_approval_recorded: bool = False,
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_review_20260412_v0.json",
        {
            "summary": {"review_outcome": review_outcome},
            "objective_quality": {
                "inputs": {
                    "second_cycle_minimum_evidence_defined": second_cycle_minimum_evidence_defined,
                    "repeatability_admissibility_criteria_defined": repeatability_defined,
                    "cross_probe_admissibility_criteria_defined": cross_probe_defined,
                }
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_admissibility_standard_review_20260412_v0.json",
        {
            "summary": {"review_outcome": "LIMITED_HOLD_RETAINED"},
            "objective_quality": {
                "inputs": {
                    "declaration_standard_defined": declaration_standard_defined,
                    "bounded_check_families_defined": bounded_check_families_defined,
                    "external_validation_policy_surface_defined": external_validation_policy_surface_defined,
                }
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json",
        {
            "summary": {"review_outcome": naming_outcome},
            "objective_quality": {
                "inputs": {
                    "named_check_admissible": named_check_admissible,
                    "bounded_scope_declared": bounded_scope_declared,
                    "not_disguised_second_full_cycle_declared": not_disguised_second_full_cycle_declared,
                }
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_bounded_check_family_standard_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": bounded_check_family_terminal_outcome,
                "declaration_standard_defined": bounded_check_family_declaration_standard_defined,
                "bounded_check_families_defined": bounded_check_family_families_defined,
                "external_validation_policy_surface_defined": bounded_check_family_surface_defined,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_criteria_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_DECLARED",
                "policy_standard_approval_criteria_defined": policy_approval_criteria_defined,
                "approval_attestation_surfaces_declared": approval_attestation_surfaces_declared,
                "approval_minimum_evidence_requirement_defined": approval_minimum_evidence_requirement_defined,
                "policy_standard_approval_recorded": policy_standard_approval_recorded,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_record_surface_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_DECLARED",
                "policy_standard_approval_record_surface_defined": policy_standard_approval_record_surface_defined,
                "policy_standard_approval_recorded": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_record_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_DECLARED",
                "policy_standard_approval_record_defined": policy_standard_approval_record_defined,
                "policy_standard_approval_recorded": policy_standard_approval_recorded,
            }
        },
    )


def test_reports_policy_standard_incomplete_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_20260413_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EXTERNAL_VALIDATION_POLICY_STANDARD_INCOMPLETE_HOLD"


def test_reports_policy_standard_formally_defined_but_not_approved(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_20260413_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        bounded_check_family_terminal_outcome="RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED",
        bounded_check_family_declaration_standard_defined=True,
        bounded_check_family_families_defined=True,
        bounded_check_family_surface_defined=True,
        naming_outcome="BOUNDED_REPEATABILITY_CHECK_NAMED",
        named_check_admissible=True,
        bounded_scope_declared=True,
        not_disguised_second_full_cycle_declared=True,
        second_cycle_minimum_evidence_defined=True,
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert (
        report["summary"]["terminal_outcome"]
        == "EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALLY_DEFINED_BUT_NOT_APPROVED"
    )
    assert "policy_standard_approval_not_recorded" in report["summary"]["approval_criteria_missing"]


def test_reports_policy_standard_with_approval_eligible_review_outcome_only_missing_recorded_approval(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_20260413_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        review_outcome="ADMISSIBLE_REPEATABILITY_STANDARD_DEFINED",
        bounded_check_family_terminal_outcome="RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED",
        bounded_check_family_declaration_standard_defined=True,
        bounded_check_family_families_defined=True,
        bounded_check_family_surface_defined=True,
        naming_outcome="BOUNDED_REPEATABILITY_CHECK_NAMED",
        named_check_admissible=True,
        bounded_scope_declared=True,
        not_disguised_second_full_cycle_declared=True,
        second_cycle_minimum_evidence_defined=True,
        repeatability_defined=True,
        policy_standard_approval_recorded=False,
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert (
        report["summary"]["terminal_outcome"]
        == "EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALLY_DEFINED_BUT_NOT_APPROVED"
    )
    assert report["summary"]["remaining_blockers_to_authorization"] == [
        "policy_standard_approval_not_recorded"
    ]


def test_reports_policy_standard_shows_missing_approval_record_object_when_absent(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_20260413_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        review_outcome="ADMISSIBLE_REPEATABILITY_STANDARD_DEFINED",
        bounded_check_family_terminal_outcome="RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED",
        bounded_check_family_declaration_standard_defined=True,
        bounded_check_family_families_defined=True,
        bounded_check_family_surface_defined=True,
        naming_outcome="BOUNDED_REPEATABILITY_CHECK_NAMED",
        named_check_admissible=True,
        bounded_scope_declared=True,
        not_disguised_second_full_cycle_declared=True,
        second_cycle_minimum_evidence_defined=True,
        repeatability_defined=True,
        policy_standard_approval_record_defined=False,
        policy_standard_approval_recorded=False,
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert "policy_standard_approval_record_not_declared" in report["summary"]["remaining_blockers_to_authorization"]


def test_reports_policy_standard_approved_and_trigger_authorized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_20260413_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        review_outcome="ADMISSIBLE_REPEATABILITY_STANDARD_DEFINED",
        bounded_check_family_terminal_outcome="RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED",
        bounded_check_family_declaration_standard_defined=True,
        bounded_check_family_families_defined=True,
        bounded_check_family_surface_defined=True,
        naming_outcome="BOUNDED_REPEATABILITY_CHECK_NAMED",
        named_check_admissible=True,
        bounded_scope_declared=True,
        not_disguised_second_full_cycle_declared=True,
        second_cycle_minimum_evidence_defined=True,
        repeatability_defined=True,
        policy_standard_approval_recorded=True,
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert (
        report["summary"]["terminal_outcome"]
        == "EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVED_AND_TRIGGER_AUTHORIZED"
    )


def test_reports_policy_standard_defined_when_named_check_admissible_is_only_in_summary(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_20260413_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        bounded_check_family_terminal_outcome="RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED",
        bounded_check_family_declaration_standard_defined=True,
        bounded_check_family_families_defined=True,
        bounded_check_family_surface_defined=True,
        naming_outcome="BOUNDED_REPEATABILITY_CHECK_NAMED",
        named_check_admissible=False,
        bounded_scope_declared=True,
        not_disguised_second_full_cycle_declared=True,
        second_cycle_minimum_evidence_defined=True,
    )
    naming_path = (
        tmp_path
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json"
    )
    _write_json(
        naming_path,
        {
            "summary": {
                "review_outcome": "BOUNDED_REPEATABILITY_CHECK_NAMED",
                "named_check_admissible": True,
            },
            "criteria": {"named_check_admissible": True},
            "objective_quality": {
                "inputs": {
                    "bounded_scope_declared": True,
                    "not_disguised_second_full_cycle_declared": True,
                }
            },
        },
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert (
        report["summary"]["terminal_outcome"]
        == "EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALLY_DEFINED_BUT_NOT_APPROVED"
    )


def test_reports_hold_pending_policy_standard_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_20260413_v0.json"
    )
    _write_declaration(declaration_path, include_full_contract_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_EXTERNAL_VALIDATION_POLICY_STANDARD_REPAIR"