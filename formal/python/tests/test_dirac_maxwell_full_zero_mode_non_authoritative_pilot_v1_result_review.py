from __future__ import annotations

import pytest

from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1_result_review as review


@pytest.fixture(scope="module")
def report() -> dict:
    return review.build_review_report()


def test_pilot_v1_review_artifact_is_current(report: dict) -> None:
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_preparation_custody_and_clean_reproduction_pass(report: dict) -> None:
    assert report["preparation_custody"]["passed"] is True
    reproduction = report["independent_clean_reproduction"]
    assert reproduction["execution_count"] == 2
    assert reproduction["byte_identical"] is True
    assert reproduction["payloads_equal"] is True
    assert len(set(reproduction["execution_sha256"])) == 1


def test_identity_repair_is_complete_and_values_match_v0(report: dict) -> None:
    audit = report["independent_identity_and_value_audit"]
    assert audit["run_record_count"] == audit["unique_run_record_count"] == audit["unique_role_count"] == 13
    assert audit["ids_match_independent_recomputation"] is True
    assert len(audit["shared_execution_ids"]) == 2
    assert audit["all_numerical_series_equal_v0"] is True


def test_all_independent_numerical_audits_pass(report: dict) -> None:
    arrays = report["independent_array_audit"]
    dispersion = report["independent_dispersion_audit"]
    refinement = report["independent_refinement_audit"]
    assert arrays["all_required_series_complete"] is True
    assert arrays["run_ids_unique"] is True
    assert arrays["reported_maxima_match_arrays"] is True
    assert arrays["threshold_rule_matches"] is True
    assert dispersion["all_row_formulas_match"] is True
    assert dispersion["reported_order_matches"] is True
    assert dispersion["doubler_branch_monotonically_separated"] is True
    assert refinement["reported_orders_match"] is True
    assert refinement["second_order_floor_met"] is True
    assert refinement["solver_hierarchy_met"] is True
    assert refinement["energy_bounded_and_refines"] is True


def test_review_accepts_engineering_evidence_only(report: dict) -> None:
    assert report["accepted"] is True
    assert report["verdict"] == "ACCEPT_ENGINEERING_READY"
    assert report["passed_decision_count"] == report["decision_count"] == 22
    assert report["failed_decision_ids"] == []
    assert report["selected_next_target"] == review.ACCEPTED_TARGET
    rotation = report["authority_rotation"]
    assert rotation["pilot_v1_engineering_evidence_accepted"] is True
    assert rotation["canonical_parameter_freeze_preparation_authorized"] is True
    assert rotation["candidate_parameters_accepted_as_canonical"] is False
    assert rotation["canonical_thresholds_accepted"] is False
    assert rotation["canonical_execution_authorized"] is False
    assert rotation["scientific_numerical_result_claimed"] is False


def test_prompt_is_preserved() -> None:
    assert review.sha256_path(review.REPO_ROOT / review.PROMPT_RELATIVE_PATH) == review.PROMPT_SHA256
