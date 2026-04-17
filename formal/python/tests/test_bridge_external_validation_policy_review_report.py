from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import bridge_external_validation_policy_review_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    repeatability_criteria_defined: bool = False,
    cross_probe_criteria_defined: bool = False,
    second_cycle_minimum_evidence_defined: bool = False,
    second_cycle_minimum_evidence_satisfied: bool = False,
    no_further_path_triggered: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_admissibility_standard_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_admissibility_standard_review_20260412_v0.json",
                "bridge_repeatability_check_naming_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json",
                "bridge_minimum_second_cycle_evidence_object_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_20260414_v0.json",
                "bridge_material_repeatability_admissibility_criteria_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_material_repeatability_admissibility_criteria_20260414_v0.json",
                "bridge_approval_eligible_policy_review_outcome_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_approval_eligible_policy_review_outcome_20260414_v0.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "external_validation_policy": {
                "approval_eligible_repeatability_review_outcome_defined": False,
                "repeatability_admissibility_criteria_defined": repeatability_criteria_defined,
                "cross_probe_admissibility_criteria_defined": cross_probe_criteria_defined,
                "second_cycle_minimum_evidence_defined": second_cycle_minimum_evidence_defined,
                "second_cycle_minimum_evidence_satisfied": second_cycle_minimum_evidence_satisfied,
                "no_further_external_validation_path_triggered": no_further_path_triggered,
            },
            "review_contract": {
                "allowed_outcomes": [
                    "ADMISSIBLE_REPEATABILITY_STANDARD_DEFINED",
                    "ADMISSIBLE_CROSS_PROBE_STANDARD_DEFINED",
                    "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                    "NO_FURTHER_EXTERNAL_VALIDATION_PATH_JUSTIFIED_YET",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_EXTERNAL_VALIDATION_POLICY_REVIEW_OUTCOME",
                "no_loop_rule": "ONE_EXTERNAL_VALIDATION_POLICY_REVIEW_ONLY",
                "default_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    admissibility_outcome: str = "LIMITED_HOLD_RETAINED",
    naming_outcome: str = "NO_SPECIFIC_CHECK_JUSTIFIED_YET",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
    repeatability_criteria_defined: bool = False,
    approval_eligible_repeatability_review_outcome_defined: bool = False,
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_admissibility_standard_review_20260412_v0.json",
        {
            "summary": {"review_outcome": admissibility_outcome},
            "objective_quality": {
                "inputs": {
                    "observed_comparator_id": comparator_id,
                    "observed_quantity_id": quantity_id,
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
                    "observed_comparator_id": comparator_id,
                    "observed_quantity_id": quantity_id,
                }
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_EVIDENCE_INCOMPLETE",
                "second_cycle_minimum_evidence_defined": False,
                "second_cycle_minimum_evidence_satisfied": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_material_repeatability_admissibility_criteria_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_DECLARED",
                "repeatability_admissibility_criteria_defined": repeatability_criteria_defined,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_approval_eligible_policy_review_outcome_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": (
                    "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_DECLARED"
                    if approval_eligible_repeatability_review_outcome_defined
                    else "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_EVIDENCE_INCOMPLETE"
                ),
                "approval_eligible_repeatability_review_outcome_defined": approval_eligible_repeatability_review_outcome_defined,
            }
        },
    )


def test_external_validation_policy_reports_incomplete_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "BRIDGE_EXTERNAL_VALIDATION_POLICY_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"


def test_external_validation_policy_reports_repeatability_standard_defined(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "BRIDGE_EXTERNAL_VALIDATION_POLICY_REVIEW_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        repeatability_criteria_defined=True,
    )
    _seed_inputs(
        tmp_path,
        naming_outcome="BOUNDED_REPEATABILITY_CHECK_NAMED",
        approval_eligible_repeatability_review_outcome_defined=True,
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_DECLARED",
                "second_cycle_minimum_evidence_defined": True,
                "second_cycle_minimum_evidence_satisfied": False,
            }
        },
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "ADMISSIBLE_REPEATABILITY_STANDARD_DEFINED"


def test_external_validation_policy_reports_cross_probe_standard_defined(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "BRIDGE_EXTERNAL_VALIDATION_POLICY_REVIEW_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        cross_probe_criteria_defined=True,
    )
    _seed_inputs(tmp_path, naming_outcome="BOUNDED_CROSS_PROBE_CHECK_NAMED")
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_DECLARED",
                "second_cycle_minimum_evidence_defined": True,
                "second_cycle_minimum_evidence_satisfied": True,
            }
        },
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "ADMISSIBLE_CROSS_PROBE_STANDARD_DEFINED"


def test_external_validation_policy_uses_minimum_evidence_object_defined_but_unsatisfied(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "BRIDGE_EXTERNAL_VALIDATION_POLICY_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path, repeatability_criteria_defined=True)
    _seed_inputs(tmp_path, naming_outcome="BOUNDED_REPEATABILITY_CHECK_NAMED")
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_DECLARED",
                "second_cycle_minimum_evidence_defined": True,
                "second_cycle_minimum_evidence_satisfied": False,
            }
        },
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"


def test_external_validation_policy_uses_material_repeatability_criteria_package(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "BRIDGE_EXTERNAL_VALIDATION_POLICY_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path, repeatability_criteria_defined=False)
    _seed_inputs(
        tmp_path,
        naming_outcome="BOUNDED_REPEATABILITY_CHECK_NAMED",
        approval_eligible_repeatability_review_outcome_defined=False,
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_DECLARED",
                "second_cycle_minimum_evidence_defined": True,
                "second_cycle_minimum_evidence_satisfied": False,
            }
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_material_repeatability_admissibility_criteria_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_DECLARED",
                "repeatability_admissibility_criteria_defined": True,
            }
        },
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["objective_quality"]["inputs"]["repeatability_admissibility_criteria_defined"] is True
    assert report["summary"]["review_outcome"] == "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"


def test_external_validation_policy_uses_approval_eligible_review_outcome_package(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "BRIDGE_EXTERNAL_VALIDATION_POLICY_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path, repeatability_criteria_defined=True)
    _seed_inputs(
        tmp_path,
        naming_outcome="BOUNDED_REPEATABILITY_CHECK_NAMED",
        approval_eligible_repeatability_review_outcome_defined=True,
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_DECLARED",
                "second_cycle_minimum_evidence_defined": True,
                "second_cycle_minimum_evidence_satisfied": False,
            }
        },
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["objective_quality"]["inputs"]["approval_eligible_repeatability_review_outcome_defined"] is True
    assert report["summary"]["review_outcome"] == "ADMISSIBLE_REPEATABILITY_STANDARD_DEFINED"


def test_external_validation_policy_reports_no_further_path(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "BRIDGE_EXTERNAL_VALIDATION_POLICY_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path, no_further_path_triggered=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "NO_FURTHER_EXTERNAL_VALIDATION_PATH_JUSTIFIED_YET"
