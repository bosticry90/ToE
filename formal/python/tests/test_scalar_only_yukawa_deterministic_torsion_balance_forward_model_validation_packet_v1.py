from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v1
    as packet,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _v0() -> dict[str, object]:
    value = json.loads(
        (REPO_ROOT / packet.V0_PACKET_RELATIVE_PATH).read_text(encoding="utf-8")
    )
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_and_consumes_exact_selector_authority() -> None:
    assert packet.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_selector_artifacts"]
    } == packet.SELECTOR_HASHES
    assert report["authority"]["consumed_selector_route"] == (
        "REPAIR_DETERMINISTIC_IDENTIFIABILITY_EXECUTION_CONTRACT"
    )


def test_all_thirteen_accepted_v0_surfaces_are_embedded_unchanged() -> None:
    frozen = _report()["frozen_v0_contract"]
    v0 = _v0()
    assert frozen["surface_count"] == len(packet.FROZEN_V0_SURFACE_KEYS) == 13
    assert set(frozen["surfaces"]) == set(packet.FROZEN_V0_SURFACE_KEYS)
    for key in packet.FROZEN_V0_SURFACE_KEYS:
        assert frozen["surfaces"][key] == v0[key], key
    assert all(
        row["semantic_status"] == "FROZEN_FROM_V0_WITHOUT_CHANGE"
        for row in frozen["surface_rows"]
    )


def test_only_four_review_failed_gates_are_repairable() -> None:
    authority = _report()["repair_authority"]
    assert authority["accepted_v0_gate_count"] == 20
    assert authority["accepted_v0_gates"] == list(packet.ACCEPTED_GATE_EVIDENCE)
    assert [row["gate_id"] for row in authority["accepted_gate_evidence"]] == list(
        packet.ACCEPTED_GATE_EVIDENCE
    )
    assert all(row["frozen_evidence"] for row in authority["accepted_gate_evidence"])
    assert authority["repairable_gate_count"] == 4
    assert authority["repairable_gates"] == list(packet.REPAIRABLE_GATES)
    assert authority["all_other_gates"] == "FROZEN_NO_SEMANTIC_CHANGE"
    assert authority["automatic_v2"] == "NOT_AUTHORIZED"


def test_accepted_jacobian_order_scaling_and_eta_bands_are_retained() -> None:
    retained = _report()["frozen_v0_contract"]["retained_jacobian_fields"]
    assert retained["row_count"] == 150
    assert retained["column_count"] == 17
    assert retained["parameter_order"] == list(packet.PARAMETER_ORDER)
    assert retained["column_standardization"] == "FROZEN_TEST_SCALE"
    assert retained["rank_relative_singular_value_threshold"] == 1e-10
    assert retained["near_degenerate_absolute_correlation_threshold"] == 0.999
    assert retained["identifiable_eta_threshold"] == 1e-3
    assert retained["indistinguishable_eta_threshold"] == 1e-6
    assert retained["minimum_contiguous_identifiable_lambda_points"] == 5


def test_g18_dimensionless_coordinates_columns_stencils_and_plateau_are_executable() -> None:
    repair = _report()["identifiability_repair_contract"]
    coordinates = repair["parameterization"]
    finite = repair["g18_finite_difference"]
    assert coordinates["lambda_coordinate"] == "q_lambda=log(lambda/1e-3_m)"
    assert len(coordinates["nuisance_scales"]) == 16
    assert coordinates["result_dependent_scaling"] == "FORBIDDEN"
    assert finite["finite_difference_columns"] == list(packet.FINITE_DIFFERENCE_COLUMNS)
    assert finite["exact_linear_columns"] == list(packet.EXACT_LINEAR_COLUMNS)
    assert len(finite["finite_difference_columns"]) == 7
    assert len(finite["exact_linear_columns"]) == 10
    assert set(finite["finite_difference_columns"]).isdisjoint(
        finite["exact_linear_columns"]
    )
    assert finite["dimensionless_step_ladder"] == [0.01, 0.003, 0.001]
    assert finite["plateau_absolute_tolerance"] == 1e-10
    assert finite["plateau_relative_tolerance"] == 5e-3
    assert finite["required_evaluation_shape"] == [150]
    assert finite["failed_plateau_outcome"] == "BLOCKED_FINITE_DIFFERENCE_PLATEAU"
    assert finite["adaptive_step_selection"] == "FORBIDDEN"


def test_g20_svd_projector_pseudoinverse_and_degeneracy_rules_are_exact() -> None:
    projector = _report()["identifiability_repair_contract"][
        "g20_rank_deficient_projector"
    ]
    assert projector["factorization"] == "THIN_SVD_N_TILDE=U_SIGMA_VT"
    assert projector["normal_equation_projector"] == "FORBIDDEN"
    assert projector["all_nuisance_columns_zero_behavior"] == (
        "USE_EMPTY_U_R_RANK_0_ZERO_PSEUDOINVERSE_AND_P_PERP_IDENTITY"
    )
    assert projector["central_relative_rank_threshold"] == 1e-10
    assert projector["probe_relative_rank_thresholds"] == [1e-9, 1e-11]
    assert projector["pseudoinverse"] == "V_r*diag(1/sigma_i)*U_r^T"
    assert projector["projector"] == "P_perp=I-U_r*U_r^T"
    assert projector["orthonormality_tolerance"] == 1e-12
    assert projector["reconstruction_tolerance"] == 1e-9
    assert projector["exact_duplicate_behavior"] == "REDUCE_RANK_WITHOUT_EXCEPTION"
    assert len(projector["near_degeneracy_triggers"]) == 3
    assert projector["eta_lambda"] == "norm2(P_perp*j_lambda)/norm2(j_lambda)"
    assert projector["intermediate_point_rule"] == (
        "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED"
    )


def test_g21_transition_grid_indices_values_sentinels_and_hash_are_frozen() -> None:
    transition = _report()["identifiability_repair_contract"]["g21_transition_domain"]
    registration = transition["registration"]
    assert registration["decision_indices_zero_based"] == list(range(4, 21))
    assert registration["decision_values_m"] == list(packet.TRANSITION_VALUES_M)
    assert registration["sentinel_values_m"] == list(packet.REGIME_SENTINEL_VALUES_M)
    assert transition["registration_canonical_sha256"] == packet._canonical_sha256(
        registration
    )
    assert transition["registration_time"].endswith("BEFORE_SCIENTIFIC_OUTPUT")
    assert len(transition["required_metrics_at_all_decision_and_sentinel_points"]) == 7
    assert transition["post_result_selection_or_reordering"] == (
        "BLOCKED_TRANSITION_DOMAIN_CONTRACT"
    )


def test_domain_classification_is_fail_closed_and_not_single_point_selected() -> None:
    transition = _report()["identifiability_repair_contract"]["g21_transition_domain"]
    assert transition["identifiable_domain_rule"] == (
        "AT_LEAST_5_CONTIGUOUS_DECISION_POINTS_WITH_ETA_LAMBDA_GE_1E-3"
    )
    assert transition["identifiable_domain_outcome"] == (
        "DETERMINISTIC_PARAMETER_IDENTIFIABLE"
    )
    assert transition["unidentifiable_domain_rule"] == (
        "ALL_17_DECISION_POINTS_WITH_ETA_LAMBDA_LE_1E-6"
    )
    assert transition["unidentifiable_domain_outcome"] == (
        "BLOCKED_PARAMETER_IDENTIFIABILITY"
    )
    assert transition["otherwise"] == "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED"


def test_g22_refinement_levels_and_all_quantitative_rules_are_frozen() -> None:
    refinement = _report()["identifiability_repair_contract"][
        "g22_refinement_stability"
    ]
    assert refinement["levels"] == [
        {
            "refinement_id": "IDENT_R_MEDIUM",
            "angular_samples": 256,
            "density_cubature_order": 16,
            "energy_derivative_check_step_rad": 2.5e-4,
        },
        {
            "refinement_id": "IDENT_R_FINE",
            "angular_samples": 512,
            "density_cubature_order": 24,
            "energy_derivative_check_step_rad": 1.25e-4,
        },
    ]
    assert refinement["retained_rank"] == "IDENTICAL"
    assert refinement["eta_absolute_change_max"] == 0.02
    assert refinement["eta_relative_change_max"] == 0.05
    assert refinement["maximum_scalar_nuisance_correlation_absolute_change_max"] == 0.02
    assert refinement["largest_principal_angle_degrees_max"] == 1.0
    assert refinement["decision_bearing_log10_singular_value_change_decades_max"] == 0.05
    assert refinement["threshold_probe_eta_spread_max"] == 0.02
    assert refinement["forward_vector_convergence_override"] == "FORBIDDEN"


def test_all_ten_controls_use_every_real_production_component() -> None:
    controls = _report()["production_path_controls"]
    assert controls["control_count"] == 10
    assert controls["production_component_count"] == 5
    assert controls["production_components"] == list(packet.PRODUCTION_COMPONENTS)
    assert controls["test_doubles_for_production_components"] == "FORBIDDEN"
    assert [row["control_id"] for row in controls["rows"]] == [
        row[0] for row in packet.CONTROL_ROWS
    ]
    for row in controls["rows"]:
        assert row["production_components"] == list(packet.PRODUCTION_COMPONENTS)
        assert row["test_double_policy"] == "FORBIDDEN_FOR_PRODUCTION_COMPONENTS"
        assert row["status"] == "NOT_EXECUTED"


def test_independent_review_burden_outcomes_and_single_execution_limit_are_exact() -> None:
    review = _report()["independent_review_contract"]
    assert review["review_burden_count"] == 10
    assert review["review_burden"] == list(packet.REVIEW_BURDEN)
    assert review["outcome_count"] == 5
    assert review["outcomes"] == list(packet.REVIEW_OUTCOMES)
    assert review["ready_outcome"] == "DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY"
    assert review["ready_authority"] == packet.READY_EXECUTION_TARGET
    assert review["ready_execution_limit"] == 1
    assert review["blocked_outcome_automatic_v2"] == "FORBIDDEN"
    assert review["review_itself_may_execute"] is False
    execution = _report()["future_single_execution_contract"]
    assert execution["status"] == "NOT_AUTHORIZED_PENDING_INDEPENDENT_REVIEW"
    assert execution["maximum_execution_count_after_ready_review"] == 1
    assert "DETERMINISTIC_FORWARD_MODEL_VALIDATED" in execution["result_classes"]
    assert "BLOCKED_PARAMETER_IDENTIFIABILITY" in execution["result_classes"]
    assert execution["stage_b"] == "NOT_AUTHORIZED"


def test_all_twenty_six_preparation_gates_pass() -> None:
    gates = _report()["preparation_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 26
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_records_contract_only_and_no_scientific_execution() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "packet_preparation_executed",
        "v0_frozen_surfaces_embedded",
        "finite_difference_contract_frozen",
        "rank_deficient_projector_contract_frozen",
        "transition_domain_contract_frozen",
        "identifiability_refinement_contract_frozen",
        "ten_production_control_contract_frozen",
        "final_attempt_boundary_frozen",
    }
    for key, value in scope.items():
        assert value is (key in allowed_true), key


def test_human_packet_records_repairs_controls_review_and_next_authority() -> None:
    text = (REPO_ROOT / packet.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        packet.VERDICT,
        "G18 — executable numerical derivative construction",
        "G20 — executable rank-deficient nuisance projector",
        "G21 — exact preregistered transition domain",
        "G22 — executable refinement stability",
        "Ten production-path controls",
        "Independent review contract",
        "automatic v2:",
        packet.SELECTED_NEXT_TARGET,
    ):
        assert token in text
