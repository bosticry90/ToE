from __future__ import annotations

import pytest

from formal.python.tools import dirac_maxwell_full_zero_mode_canonical_parameter_freeze_result_review as review


@pytest.fixture(scope="module")
def report() -> dict:
    return review.build_review_report()


def test_freeze_review_artifact_is_current(report: dict) -> None:
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_preparation_custody_is_exact(report: dict) -> None:
    custody = report["preparation_custody"]
    assert custody["passed"] is True
    assert custody["commit"] == review.PREPARATION_COMMIT
    assert custody["parent"] == review.PREPARATION_PARENT


def test_run_matrix_is_independently_complete(report: dict) -> None:
    audit = report["independent_matrix_audit"]
    assert audit["record_count"] == audit["unique_run_id_count"] == 50
    assert audit["reported_counts_match"] is True
    assert audit["role_counts_complete"] is True
    assert audit["all_required_fields_present"] is True
    assert audit["all_output_paths_are_preregistered"] is True
    assert audit["deterministic_duplicates_match"] is True
    assert audit["positive_control_inventory_matches"] is True
    assert audit["negative_control_inventory_matches"] is True


def test_parameters_and_twenty_thresholds_are_reconstructed(report: dict) -> None:
    freeze = report["accepted_canonical_freeze"]
    assert freeze["parameters"] == {"N": 32, "dt": 0.0015625, "duration": 0.05, "max_iterations": 80, "solver_tolerance": 1e-12}
    audit = report["independent_threshold_audit"]
    assert audit["threshold_count"] == 20
    assert audit["threshold_ids_complete"] is True
    assert audit["all_reconstructed"] is True
    assert len(freeze["thresholds"]) == 20


def test_exchange_gates_are_recomputed_and_material(report: dict) -> None:
    audit = report["independent_exchange_audit"]
    assert audit["row_ids_match"] is True
    assert audit["prepared_gates_match"] is True
    assert audit["recomputed_ratio_gate"] == 100
    assert audit["recomputed_transverse_signal_gate"] == 3e-8
    assert audit["separation_is_material"] is True


def test_environment_and_all_freeze_decisions_pass(report: dict) -> None:
    assert all(report["independent_environment_audit"].values())
    assert report["accepted"] is True
    assert report["verdict"] == "ACCEPT_FREEZE"
    assert report["passed_decision_count"] == report["decision_count"] == 22
    assert report["failed_decision_ids"] == []


def test_authority_rotates_only_to_canonical_execution(report: dict) -> None:
    assert report["selected_next_target"] == review.ACCEPTED_TARGET
    rotation = report["authority_rotation"]
    assert rotation["canonical_parameter_freeze_accepted"] is True
    assert rotation["canonical_parameters_frozen"] is True
    assert rotation["canonical_thresholds_frozen"] is True
    assert rotation["canonical_run_matrix_frozen"] is True
    assert rotation["canonical_simulation_execution_authorized"] is True
    assert rotation["canonical_simulation_executed"] is False
    assert rotation["scientific_numerical_result_claimed"] is False
    assert report["blocked_review_policy"]["threshold_relaxation_allowed"] is False


def test_prompt_is_preserved() -> None:
    assert review.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
