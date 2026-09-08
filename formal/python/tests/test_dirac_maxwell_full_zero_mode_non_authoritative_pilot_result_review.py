from __future__ import annotations

import pytest

from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot_result_review as review


@pytest.fixture(scope="module")
def report() -> dict:
    return review.build_review_report()


def test_review_artifact_is_current(report: dict) -> None:
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_preparation_commit_and_every_input_are_immutable(report: dict) -> None:
    custody = report["preparation_custody"]
    assert custody["passed"] is True
    assert custody["commit"] == review.PREPARATION_COMMIT
    assert custody["parent"] == review.PREPARATION_PARENT


def test_independent_reproduction_and_numerical_audits_pass(report: dict) -> None:
    reproduction = report["independent_clean_reproduction"]
    assert reproduction["execution_count"] == 2
    assert reproduction["byte_identical"] is True
    assert reproduction["payloads_equal"] is True
    assert len(set(reproduction["execution_sha256"])) == 1
    assert report["independent_array_audit"]["reported_maxima_match_arrays"] is True
    assert report["independent_array_audit"]["threshold_rule_matches"] is True
    assert report["independent_dispersion_audit"]["all_row_formulas_match"] is True
    assert report["independent_refinement_audit"]["second_order_floor_met"] is True
    assert report["independent_refinement_audit"]["solver_hierarchy_met"] is True


def test_review_blocks_only_the_duplicate_run_identity_defect(report: dict) -> None:
    assert report["accepted"] is False
    assert report["verdict"] == "B-BLOCKED_IMPLEMENTATION_DEFECT"
    assert report["passed_decision_count"] == report["decision_count"] - 1 == 21
    assert report["failed_decision_ids"] == ["all_registered_per_run_series_are_complete"]
    assert report["blocker_diagnostics"] == ["REGISTERED_RUN_IDENTITIES_NOT_UNIQUE"]
    assert report["independent_array_audit"]["all_required_series_complete"] is True
    assert report["independent_array_audit"]["run_ids_unique"] is False


def test_only_versioned_implementation_repair_is_selected(report: dict) -> None:
    assert report["selected_next_target"] == review.BLOCKED_TARGET
    rotation = report["authority_rotation"]
    assert rotation["pilot_engineering_evidence_accepted"] is False
    assert rotation["canonical_parameter_freeze_preparation_authorized"] is False
    assert rotation["candidate_parameters_accepted_as_canonical"] is False
    assert rotation["canonical_execution_authorized"] is False
    assert rotation["scientific_numerical_result_claimed"] is False


def test_prompt_is_preserved() -> None:
    assert review.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
