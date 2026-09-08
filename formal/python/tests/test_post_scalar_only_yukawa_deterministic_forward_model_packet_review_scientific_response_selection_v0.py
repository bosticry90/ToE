from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    post_scalar_only_yukawa_deterministic_forward_model_packet_review_scientific_response_selection_v0
    as selection,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / selection.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selection_regenerates_and_freezes_review_authority() -> None:
    assert selection.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["verdict"] == selection.VERDICT
    assert report["selected_route"] == selection.SELECTED_ROUTE
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_packet_review_artifacts"]
    } == selection.AUTHORITY_HASHES


def test_review_is_interpreted_as_contract_block_not_physical_result() -> None:
    interpretation = _report()["review_interpretation"]
    assert interpretation == {
        "review_verdict": "BLOCKED_PARAMETER_IDENTIFIABILITY",
        "physical_unidentifiability_established": False,
        "deterministic_forward_model_failure_established": False,
        "identifiability_decision_contract_complete": False,
        "deterministic_execution": "NOT_PERFORMED",
        "forward_vector": "NOT_PRODUCED",
        "jacobian": "NOT_COMPUTED",
    }


def test_five_routes_and_eight_criteria_select_final_narrow_repair() -> None:
    report = _report()
    policy = report["selection_policy"]
    ranking = report["ranking"]
    assert policy["candidate_count"] == 5
    assert policy["criterion_count"] == 8
    assert ranking["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
    assert ranking["selected_score"] == 165
    assert ranking["runner_up_candidate_id"] == (
        "SMALLER_EXPLORATORY_DETERMINISTIC_CALCULATION"
    )
    assert ranking["runner_up_score"] == 129
    assert ranking["winning_margin"] == 36
    assert [row["weighted_score"] for row in ranking["rows"]] == [
        165, 129, 121, 120, 80
    ]


def test_selected_route_is_stable_in_all_twenty_four_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 24
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0


def test_exactly_twenty_gates_are_frozen_and_only_four_are_repairable() -> None:
    freeze = _report()["accepted_gate_freeze"]
    assert freeze["accepted_gate_count"] == 20
    assert freeze["mutable_gate_count"] == 4
    assert freeze["accepted_gates"] == list(selection.ACCEPTED_V0_GATES)
    assert freeze["repairable_gates"] == list(selection.REPAIRABLE_V0_GATES)
    assert set(freeze["accepted_gates"]).isdisjoint(freeze["repairable_gates"])


def test_dimensionless_scales_and_finite_difference_plateau_are_numeric() -> None:
    repair = _report()["v1_repair_contract"]
    coordinates = repair["dimensionless_parameterization"]
    finite = repair["finite_difference"]
    assert coordinates["lambda_coordinate"] == "q_lambda=log(lambda/1e-3_m)"
    assert len(coordinates["nuisance_scales"]) == 16
    assert coordinates["post_result_scaling_forbidden"] is True
    assert finite["dimensionless_step_ladder"] == [0.01, 0.003, 0.001]
    assert finite["plateau_steps"] == [0.003, 0.001]
    assert finite["absolute_tolerance"] == 1e-10
    assert finite["relative_tolerance"] == 5e-3
    assert finite["oversized_mutation_step"] == 0.3
    assert finite["undersized_mutation_step"] == 1e-8
    assert finite["result_dependent_adaptation"] == "FORBIDDEN"


def test_rank_deficient_svd_projector_and_eta_bands_are_exact() -> None:
    projector = _report()["v1_repair_contract"]["rank_deficient_projector"]
    assert projector["central_relative_rank_threshold"] == 1e-10
    assert projector["probe_relative_rank_thresholds"] == [1e-9, 1e-11]
    assert projector["projector"] == "P_perp=I-U_r*U_r^T"
    assert projector["exact_duplicate_behavior"] == "REDUCE_RANK_WITHOUT_CRASH"
    assert projector["near_degenerate_absolute_correlation_threshold"] == 0.999
    assert projector["near_degenerate_condition_number_threshold"] == 1e8
    assert projector["indistinguishable_eta_max"] == 1e-6
    assert projector["identifiable_eta_min"] == 1e-3
    assert projector["intermediate_eta_classification"] == (
        "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED"
    )


def test_transition_domain_and_sentinels_are_predeclared() -> None:
    transition = _report()["v1_repair_contract"]["transition_domain"]
    assert transition["decision_bearing_indices_zero_based"] == list(range(4, 21))
    assert transition["decision_bearing_index_count"] == 17
    assert transition["regime_sentinel_formula"] == [
        "d_min/3", "d_min", "sqrt(d_min*d_max)", "d_max", "3*d_max"
    ]
    assert transition["regime_sentinel_values_m"] == [
        1e-4 / 3.0, 1e-4, 1e-3, 1e-2, 3e-2
    ]
    assert transition["minimum_contiguous_identifiable_grid_points"] == 5
    assert transition["post_result_point_selection"] == "FORBIDDEN"
    assert len(transition["required_metrics_at_every_grid_and_sentinel_point"]) == 6
    assert transition["sentinel_role"].endswith("NOT_CONTIGUITY_SUBSTITUTE")
    classification = transition["domain_classification"]
    assert classification["identifiable_outcome"] == (
        "DETERMINISTIC_PARAMETER_IDENTIFIABLE"
    )
    assert classification["unidentifiable_outcome"] == (
        "BLOCKED_PARAMETER_IDENTIFIABILITY"
    )
    assert classification["otherwise"] == (
        "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED"
    )


def test_refinement_and_threshold_stability_rules_are_quantitative() -> None:
    stability = _report()["v1_repair_contract"]["refinement_stability"]
    assert stability["retained_rank"] == "IDENTICAL"
    assert stability["eta_absolute_change_max"] == 0.02
    assert stability["eta_relative_change_max"] == 0.05
    assert stability["maximum_column_correlation_absolute_change_max"] == 0.02
    assert stability["largest_principal_angle_degrees_max"] == 1.0
    assert stability["decision_bearing_log10_singular_value_change_decades_max"] == 0.05
    assert stability["threshold_probe_rank_and_classification"] == "IDENTICAL"
    assert stability["threshold_probe_eta_spread_max"] == 0.02
    assert stability["forward_convergence_override"] == "FORBIDDEN"


def test_ten_controls_use_the_complete_production_path() -> None:
    repair = _report()["v1_repair_contract"]
    assert repair["mandatory_control_count"] == 10
    assert len(repair["mandatory_controls"]) == 10
    assert repair["control_path"] == (
        "PRODUCTION_FORWARD_MODEL_JACOBIAN_BUILDER_SCALER_PROJECTOR_"
        "REFINEMENT_ADJUDICATOR"
    )
    assert "SCALAR_PROPORTIONAL_TO_CALIBRATION_YIELDS_ETA_ZERO" in repair[
        "mandatory_controls"
    ]
    assert "NUISANCE_ORTHOGONAL_SCALAR_YIELDS_ETA_ONE" in repair[
        "mandatory_controls"
    ]


def test_review_outcomes_and_last_automatic_repair_boundary_are_exact() -> None:
    report = _report()
    assert report["v1_repair_contract"]["review_outcomes"] == list(
        selection.REVIEW_OUTCOMES
    )
    boundary = report["anti_rabbit_hole_boundary"]
    assert boundary["v1_is_last_automatic_stage_a_repair"] is True
    assert boundary["automatic_v2_authorized"] is False
    assert boundary["new_foundational_defect_requires_new_selector"] is True
    assert len(boundary["required_future_choices"]) == 4


def test_all_twenty_selection_gates_pass() -> None:
    gates = _report()["selection_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 20
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_authorizes_packet_preparation_only() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "scientific_response_selection_executed",
        "accepted_v0_gates_frozen",
        "v1_repair_packet_preparation_authorized",
        "final_automatic_repair_boundary_frozen",
    }
    for key, value in scope.items():
        assert value is (key in allowed_true), key


def test_human_selection_records_exact_route_and_next_authority() -> None:
    text = (REPO_ROOT / selection.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        selection.VERDICT,
        selection.SELECTED_ROUTE,
        "20 / 24 FROZEN",
        "h = [1e-2, 3e-3, 1e-3]",
        "i=4,...,20",
        "V1 is the last automatic Stage A contract repair",
        selection.SELECTED_NEXT_TARGET,
    ):
        assert token in text
