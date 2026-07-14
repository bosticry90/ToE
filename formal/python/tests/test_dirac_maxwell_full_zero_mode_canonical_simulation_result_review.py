from __future__ import annotations

import pytest

from formal.python.tools import dirac_maxwell_full_zero_mode_canonical_simulation_result_review as review


@pytest.fixture(scope="module")
def report() -> dict:
    return review.build_review_report()


def test_result_review_artifact_is_current(report: dict) -> None:
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_execution_commit_and_all_fifty_outputs_have_exact_custody(report: dict) -> None:
    custody = report["execution_custody"]
    assert custody["passed"] is True
    assert custody["commit"] == review.EXECUTION_COMMIT
    assert custody["parent"] == review.EXECUTION_PARENT
    assert len(custody["run_output_checks"]) == 50
    assert all(item["passed"] for item in custody["run_output_checks"])


def test_complete_matrix_is_independently_reproduced(report: dict) -> None:
    reproduction = report["independent_reproduction"]
    assert reproduction["all_fifty_records_reproduced"] is True
    assert len(reproduction["rows"]) == 50
    assert all(item["matched"] for item in reproduction["rows"])
    assert reproduction["simulation_count"] == 15
    assert reproduction["deterministic_duplicates_match"] is True


def test_all_controls_and_residual_thresholds_pass(report: dict) -> None:
    reproduction = report["independent_reproduction"]
    assert len(reproduction["positive_controls"]) == 12
    assert all(item["passed"] for item in reproduction["positive_controls"])
    assert len(reproduction["negative_controls"]) == 27
    assert all(item["passed"] for item in reproduction["negative_controls"])
    assert reproduction["all_thresholds_pass"] is True
    assert all(item["passed"] for item in reproduction["threshold_evaluations"])


def test_all_frozen_scientific_numerical_gates_pass(report: dict) -> None:
    metrics = report["result_metrics"]
    assert metrics["spatial_phi2_order"] >= 0.8
    assert metrics["temporal_phi2_order"] >= 1.5
    assert metrics["temporal_energy_order"] >= 1.5
    assert metrics["Wilson_continuum_order"] >= 0.8
    assert metrics["exchange_ratio"] >= 100
    assert metrics["transverse_signal"] >= 3e-8
    assert metrics["maximum_total_energy_drift"] <= 2e-10


def test_review_accepts_only_the_bounded_E_REPRO_claim(report: dict) -> None:
    assert report["accepted"] is True
    assert report["verdict"] == "ACCEPT_BOUNDED_SCIENTIFIC_RESULT"
    assert report["outcome_class"] == "ACCEPTED_BOUNDED_SCIENTIFIC_RESULT"
    assert report["passed_decision_count"] == report["decision_count"] == 24
    assert report["failed_decision_ids"] == []
    assert report["accepted_claim_label"] == "E-REPRO"
    assert report["maximum_accepted_claim"] == review.MAXIMUM_CLAIM
    assert report["selected_next_target"] == review.ACCEPTED_TARGET


def test_all_stronger_promotions_remain_unauthorized(report: dict) -> None:
    rotation = report["authority_rotation"]
    assert rotation["canonical_execution_accepted"] is True
    assert rotation["bounded_scientific_result_accepted"] is True
    assert rotation["E_REPRO_authorized"] is True
    assert rotation["pillar_completion_authorized"] is False
    assert rotation["seam_admissibility_or_closure_authorized"] is False
    assert rotation["empirical_adequacy_authorized"] is False
    assert rotation["C_k_dynamics_authorized"] is False
    assert rotation["CCFT_validation_authorized"] is False
    assert rotation["master_action_promotion_authorized"] is False


def test_prompt_is_preserved() -> None:
    assert review.sha256_path(review.REPO_ROOT / review.PROMPT_RELATIVE_PATH) == review.PROMPT_SHA256
