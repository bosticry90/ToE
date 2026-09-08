from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_review_v1
    as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_and_freezes_exact_v1_packet_custody() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_packet_artifacts"]
    } == review.PACKET_HASHES


def test_review_accepts_contract_without_claiming_physical_result() -> None:
    report = _report()
    assert report["principal_packet_review_outcome"] == (
        "DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY"
    )
    posture = report["current_posture"]
    assert posture["deterministic_executions_authorized"] == 1
    assert posture["deterministic_executions_performed"] == 0
    assert posture["forward_vector"] == "NOT_PRODUCED"
    assert posture["jacobian_svd_eta"] == "NOT_COMPUTED"
    assert posture["physical_identifiability"] == "NOT_DETERMINED"


def test_twenty_gate_evidence_and_thirteen_surfaces_are_independently_verified() -> None:
    frozen = _report()["frozen_surface_review"]
    assert frozen["accepted_gate_count"] == 20
    assert frozen["accepted_gate_evidence_count"] == 20
    assert frozen["surface_count"] == 13
    assert frozen["semantic_equality_count"] == 13
    assert frozen["canonical_hash_reproduction_count"] == 13
    assert frozen["repairable_gates"] == list(review.EXPECTED_REPAIRABLE_GATES)
    assert frozen["forbidden_surface_drift_detected"] is False
    assert frozen["complete"] is True


def test_finite_difference_review_reproduces_scales_partition_and_stencil_validity() -> None:
    finite = _report()["finite_difference_review"]
    assert finite["parameter_count"] == 17
    assert finite["nuisance_scale_count"] == 16
    assert finite["finite_difference_column_count"] == 7
    assert finite["exact_linear_column_count"] == 10
    assert finite["dimensionless_scales_reproduced"] is True
    assert finite["column_partition_complete"] is True
    assert finite["production_step_ladder"] == [0.01, 0.003, 0.001]
    assert finite["log_lambda_centered_stencil_valid_at_all_registered_points"] is True
    assert finite["nuisance_centered_stencil_valid_at_nominal"] is True
    assert finite["adaptive_selection_forbidden"] is True
    assert finite["complete"] is True


def test_rank_deficient_projector_review_is_complete_and_fail_closed() -> None:
    projector = _report()["rank_deficient_projector_review"]
    assert projector["thin_svd_only"] is True
    assert projector["central_rank_threshold"] == 1e-10
    assert projector["probe_rank_thresholds"] == [1e-9, 1e-11]
    for key in (
        "zero_column_behavior_complete",
        "all_zero_behavior_complete",
        "duplicate_behavior_complete",
        "near_degeneracy_behavior_complete",
        "pseudoinverse_complete",
        "orthogonal_projector_complete",
        "eta_path_unique",
        "near_threshold_unresolved",
        "complete",
    ):
        assert projector[key] is True, key


def test_transition_domain_is_mechanical_registered_and_immutable() -> None:
    transition = _report()["transition_domain_review"]
    assert transition["decision_index_count"] == 17
    assert transition["decision_indices_zero_based"] == list(range(4, 21))
    assert transition["sentinel_count"] == 5
    assert transition["registration_sha256_reproduced"] is True
    assert transition["post_result_selection_forbidden"] is True
    assert transition["complete"] is True


def test_refinement_review_controls_every_decision_bearing_metric() -> None:
    refinement = _report()["refinement_stability_review"]
    assert refinement["level_count"] == 2
    for key in (
        "levels_use_accepted_v0_values",
        "retained_rank_rule_complete",
        "singular_value_rule_complete",
        "principal_angle_rule_complete",
        "correlation_rule_complete",
        "eta_rule_complete",
        "degeneracy_and_classification_rules_complete",
        "threshold_probe_rule_complete",
        "forward_convergence_override_forbidden",
        "complete",
    ):
        assert refinement[key] is True, key


def test_ten_controls_share_real_production_route_and_none_was_executed() -> None:
    controls = _report()["production_control_review"]
    assert controls["control_count"] == 10
    assert controls["production_component_count"] == 5
    assert controls["all_controls_use_same_production_components"] is True
    assert controls["production_test_doubles_forbidden"] is True
    assert controls["controls_executed_during_review"] == 0
    assert controls["complete"] is True


def test_all_thirty_independent_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 30
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])
    assert _report()["diagnostics"] == []


def test_acceptance_authorizes_exactly_one_execution_and_mandatory_result_review() -> None:
    authorization = _report()["execution_authorization"]
    assert authorization["status"] == "AUTHORIZED_NOT_STARTED"
    assert authorization["execution_count_authorized"] == 1
    assert authorization["execution_count_performed"] == 0
    assert authorization["execution_target"] == review.SELECTED_NEXT_TARGET
    assert authorization["required_post_execution_target"] == (
        review.REQUIRED_POST_EXECUTION_TARGET
    )
    assert authorization["result_classes"] == list(review.EXPECTED_EXECUTION_RESULTS)
    assert authorization["stage_b_eligibility_on_validated_result"] == (
        "FRESH_SCIENTIFIC_DECISION_REQUIRED"
    )
    assert authorization["stage_b_authorized"] is False
    assert authorization["automatic_v2_authorized"] is False


def test_scope_authorizes_only_review_and_one_future_deterministic_execution() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "independent_packet_review_executed",
        "v0_custody_verified",
        "twenty_accepted_gate_evidence_coverage_verified",
        "thirteen_v0_surfaces_verified_unchanged",
        "four_identifiability_repairs_verified_executable",
        "ten_production_control_routes_verified",
        "deterministic_identifiability_contract_ready",
        "one_deterministic_execution_authorized",
        "deterministic_execution_authorized",
    }
    assert scope["authorized_execution_count"] == 1
    for key, value in scope.items():
        if key == "authorized_execution_count":
            continue
        assert value is (key in allowed_true), key


def test_stage_b_empirical_theory_and_v2_firewalls_remain_closed() -> None:
    scope = _report()["scope"]
    for key in (
        "stochastic_packet_preparation_authorized",
        "stage_b_authorized",
        "gaussian_noise_used",
        "covariance_used",
        "monte_carlo_executed",
        "profile_likelihood_executed",
        "sensitivity_forecast_produced",
        "synthetic_dataset_generated",
        "measured_evidence_used",
        "empirical_constraint_claimed",
        "numerical_lambda_bound_computed",
        "numerical_alpha_bound_computed",
        "scalar_branch_adopted",
        "automatic_v2_repair_authorized",
    ):
        assert scope[key] is False, key


def test_human_review_records_contract_acceptance_ceiling_and_next_authority() -> None:
    text = (REPO_ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "G18 review — pass",
        "G20 review — pass",
        "G21 review — pass",
        "G22 review — pass",
        "Production-control review — pass",
        "authorized execution count:",
        "automatic V2:",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text

