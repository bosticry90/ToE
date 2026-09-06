from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_execution_result_review_v1
    as review,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, Any]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _reproduction() -> dict[str, Any]:
    return _report()["independent_reproduction"]


def test_review_regenerates_exactly_and_freezes_execution_custody() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["review_disposition"] == review.REVIEW_DISPOSITION
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_execution_artifacts"]
    } == review.EXECUTION_HASHES
    assert len(report["authority"]["verified_output_artifacts"]) == 10


def test_all_eleven_independent_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 11
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_principal_kernel_failure_is_reproduced_exactly() -> None:
    row = _reproduction()["benchmark_reproduction"]
    assert row["benchmark_group_count"] == 4
    assert row["benchmark_group_pass_count"] == 3
    assert row["principal_outcome_reproduced"] is True
    assert row["uniform_sphere_production_vs_order24_error"] == 6.867902041407599e-2
    assert row["uniform_sphere_order16_vs_order24_error"] == 4.202776018628042e-1
    assert row["required_tolerance"] == 1e-6
    assert row["order24_converged_reference"] is False


def test_relative_error_denominators_are_independently_nonzero() -> None:
    row = _reproduction()["relative_error_denominators"]
    assert row["all_independent_denominators_above_floor"] is True
    energies = [item["absolute_denominator_J"] for item in row["independent_closed_form_rows"]]
    assert energies == [
        3.225227314649147e-24,
        2.274618571751374e-16,
        1.2700907357438663e-14,
    ]
    assert all(item["denominator_floor_J"] == 1e-300 for item in row["independent_closed_form_rows"])


def test_all_four_cubature_dimensions_and_volume_weights_are_present() -> None:
    audit = _reproduction()["static_path_audit"]
    assert audit["production_tokens_present"] is True
    assert audit["executor_tokens_present"] is True
    assert audit["all_cubature_dimensions_and_weights_present"] is True
    assert all(audit["cubature_dimension_checks"].values())
    assert audit["review_imports_or_calls_production_module"] is False


def test_newtonian_and_yukawa_components_remain_separate_but_unaccepted() -> None:
    row = _reproduction()["separate_components"]
    assert row["newtonian_row_count"] == 150
    assert row["reference_total_row_count"] == 150
    assert row["yukawa_row_count"] == 3750
    assert row["newtonian_classes"] == ["NEWTONIAN"]
    assert row["reference_classes"] == ["TOTAL"]
    assert row["yukawa_classes"] == ["YUKAWA"]
    assert row["passed"] is True
    assert _report()["scope"]["scientific_real_150_vector_accepted"] is False


def test_dft_and_density_convergence_failures_are_exact() -> None:
    row = _reproduction()["convergence_reproduction"]
    assert row["control_count"] == 6
    assert row["pass_count"] == 4
    assert row["failed_control_ids"] == [
        "ANGULAR_DFT_256_VS_512",
        "DENSITY_CUBATURE_16_VS_24",
    ]
    assert row["angular_dft_error"] == 1.481612456806414e-6
    assert row["angular_dft_tolerance"] == 1e-8


def test_structural_controls_pass_without_claiming_accuracy() -> None:
    row = _reproduction()["structural_controls"]
    assert row == {
        "mutation_count": 5,
        "mutation_pass_count": 5,
        "symmetry_count": 6,
        "symmetry_pass_count": 6,
    }


def test_identifiability_firewall_is_preserved() -> None:
    row = _reproduction()["firewall"]
    assert row["passed"] is True
    assert row["jacobian_rows"] == [
        {"status": "NOT_COMPUTED_EARLY_PHYSICAL_CONTROL_BLOCK"}
    ]
    assert row["jacobian_computed"] is False
    assert row["singular_values_computed"] is False
    assert row["eta_lambda_computed"] is False
    assert row["physical_identifiability_evaluated"] is False


def test_launch_recovery_is_qualified_and_not_hidden() -> None:
    row = _reproduction()["launch_custody"]
    assert row["launch_attempt_count"] == 3
    assert row["production_compute_pass_count_across_all_attempts"] == 3
    assert row["completed_canonical_execution_count"] == 1
    assert row["canonical_output_written_by_attempts"] == [3]
    assert row["technical_relaunch_disclosed"] is True
    assert row["scientific_retry_or_silent_replacement"] is False
    assert row["changed_scientific_parameter_or_threshold"] is False
    assert row["changed_production_kernel_or_geometry"] is False
    assert "not represented as a pristine single process launch" in row["qualification"]


def test_scope_authorizes_only_a_fresh_response_selector() -> None:
    report = _report()
    scope = report["scope"]
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["fresh_selector_options"] == [
        "NUMERICAL_KERNEL_DIAGNOSIS",
        "REPLACE_PRODUCTION_INTEGRATION_METHOD",
        "SIMPLIFY_OR_REDESIGN_APPARATUS",
        "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
    ]
    assert scope["scientific_response_selection_authorized"] is True
    assert scope["scientific_response_selection_executed"] is False
    for key in (
        "deterministic_forward_model_validated",
        "jacobian_computed",
        "physical_identifiability_evaluated",
        "stage_b_eligible",
        "stage_b_authorized",
        "automatic_v2_authorized",
        "additional_deterministic_execution_authorized",
        "numerical_kernel_diagnosis_authorized",
        "production_integration_replacement_authorized",
        "apparatus_redesign_authorized",
        "torsion_balance_lane_closure_authorized",
        "sensitivity_forecast_produced",
    ):
        assert scope[key] is False, key


def test_human_review_records_result_qualification_and_stop() -> None:
    text = (ROOT / review.HUMAN_REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "11 / 11 GATES PASSED",
        review.VERDICT,
        "Order 24 is not accepted as a converged oracle",
        "not represented as a pristine single process launch",
        "NOT COMPUTED EARLY PHYSICAL CONTROL BLOCK".replace(" ", "_"),
        review.SELECTED_NEXT_TARGET,
        "automatic V2",
        "NOT AUTHORIZED",
    ):
        assert token in text
