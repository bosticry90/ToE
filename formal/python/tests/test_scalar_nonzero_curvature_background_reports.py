from __future__ import annotations

import math

import pytest

from formal.python.tests.strict_physics_state_helpers import (
    active_workstream,
    current_target_state,
    loop_registry,
    workstream,
)
from formal.python.tools.scalar_nonzero_curvature_background_reports import (
    CALCULATION_MANIFEST_PATH,
    CALCULATION_OUTPUT_PATH,
    CALCULATION_SCRIPT_PATH,
    EQUATION_ID,
    EXECUTION_OUTCOME,
    EXECUTION_REPORT_PATH,
    EXECUTION_STRICT_OUTCOME,
    EXECUTION_TARGET,
    EXECUTION_TARGET_KIND,
    EXPECTED_GUARDRAIL_SHA256,
    GUARDRAIL_OUTCOME,
    GUARDRAIL_REPORT_PATH,
    GUARDRAIL_STRICT_OUTCOME,
    GUARDRAIL_TARGET,
    HIGHER_DIMENSIONAL_CURVED_BACKGROUND_GUARDRAIL_TARGET,
    PACKET_ID,
    PACKET_SCHEMA_ID,
    REVIEW_TARGET,
    REVIEW_TARGET_KIND,
    THRESHOLD_REPAIR_TARGET,
    build_execution_report,
    build_guardrail_payload,
    canonical_json_bytes,
    report_json_bytes,
    sha256_path,
    validate_guardrail_payload,
)


def test_guardrail_freezes_lifecycle_and_level_three_scope() -> None:
    payload = build_guardrail_payload()
    validate_guardrail_payload(payload)
    assert payload["schema_id"] == PACKET_SCHEMA_ID
    assert payload["packet_id"] == PACKET_ID
    assert payload["consumed_target"] == GUARDRAIL_TARGET
    assert payload["selected_next_target"] == EXECUTION_TARGET
    assert payload["selected_next_target_kind"] == EXECUTION_TARGET_KIND
    assert payload["packet_result"] == GUARDRAIL_OUTCOME
    assert payload["strict_packet_result"] == GUARDRAIL_STRICT_OUTCOME
    assert payload["claim_ceiling"]["claim_ladder_level"] == 3
    assert all(
        payload["claim_ceiling"][key] is True
        for key in (
            "not_general_curved_spacetime_theorem",
            "not_gravity_dynamics",
            "not_source_admissibility",
            "not_bianchi_compatibility",
            "not_seam_admissibility",
        )
    )


def test_guardrail_freezes_de_sitter_patch_and_conventions() -> None:
    payload = build_guardrail_payload()
    inputs = payload["inputs"]
    geometry = payload["background_geometry"]
    conventions = payload["connection_and_curvature_conventions"]
    assert inputs["coordinate_domain"] == {
        "eta": "eta in [0,1]",
        "x": "x in [0,2*pi), periodic",
    }
    assert inputs["time_slices_eta"] == [0.0, 0.37, 0.91]
    assert inputs["spatial_resolutions_N"] == [64, 128, 256, 512]
    assert inputs["conformal_hubble_parameter_H"] == 0.2
    assert inputs["scale_factor"] == "a(eta) = (1 - H*eta)^(-1)"
    assert geometry["metric"] == "g_mu_nu = a(eta)^2 * diag(-1,+1)"
    assert geometry["metric_signature"] == "(-,+)"
    assert geometry["scalar_curvature"] == 0.08
    assert set(conventions["nonzero_christoffels"].values()) == {"q(eta)"}
    assert conventions["ricci_contraction"] == (
        "R_{sigma nu} = R^rho_{sigma rho nu}"
    )


def test_two_independent_curvature_routes_are_mandatory() -> None:
    payload = build_guardrail_payload()
    curvature = payload["curvature_verification"]
    component = curvature["independent_component_route"]
    assert curvature["analytic_conformal_route"]["expected_value"] == 0.08
    assert component["route"] == [
        "metric",
        "inverse_metric",
        "metric_derivatives",
        "Christoffel_symbols",
        "Riemann_tensor",
        "Ricci_tensor",
        "scalar_contraction",
    ]
    assert component["expected_value"] == 0.08
    assert curvature["maximum_route_agreement_absolute_error"] == 1e-12
    assert curvature["minimum_absolute_scalar_curvature"] == 0.05
    assert payload["required_controls"]["analytic_curvature_route"] is True
    assert payload["required_controls"][
        "independent_component_curvature_route"
    ] is True


def test_source_free_on_shell_and_exact_off_shell_controls_are_frozen() -> None:
    payload = build_guardrail_payload()
    inputs = payload["inputs"]
    controls = payload["solution_controls"]
    assert inputs["amplitude_A"] == 0.2
    assert inputs["wave_number_k"] == inputs["omega_on"] == 2.0
    assert inputs["omega_off"] == 2.2
    assert inputs["omega_off"] ** 2 - inputs["wave_number_k"] ** 2 == (
        pytest.approx(0.84)
    )
    assert controls["on_shell_positive_control"] == {
        "omega": 2.0,
        "classification": "exact_source_free_solution",
        "forced_or_manufactured": False,
        "exact_residual": "E_phi = 0",
    }
    assert controls["off_shell_control"]["forced_or_manufactured"] is False
    assert controls["off_shell_control"]["exact_residual"] == (
        "E_phi = 0.84 * a(eta)^(-2) * phi"
    )


def test_action_identity_norms_and_existing_equation_surface_are_frozen() -> None:
    payload = build_guardrail_payload()
    equations = payload["equation_surfaces"]
    method = payload["numerical_method"]
    assert equations["identity"] == (
        "nabla_mu T^{mu nu} = E_phi nabla^nu phi"
    )
    assert "V(phi)=0" in equations["scalar_action"]
    assert "a(eta)^(-2)" in equations["covariant_dalembertian"]
    assert equations["existing_equation_id_reused"] == EQUATION_ID
    assert equations["equation_surface_upgraded"] is False
    assert method["spatial_derivatives"] == (
        "second-order centered periodic finite differences"
    )
    assert method["component_rms_norm_at_each_time"] == (
        "sqrt(mean_x(v_nu^2))"
    )
    assert "H=0" in method["flat_limit_comparison"]


def test_three_negative_controls_and_thresholds_are_frozen() -> None:
    payload = build_guardrail_payload()
    negative = payload["negative_controls"]
    thresholds = payload["success_criteria"]
    assert negative["naive_partial_divergence"]["minimum_error_ratio"] == 100.0
    assert negative["curvature_derivative_omission"][
        "expected_bad_scalar_curvature"
    ] == 0.0
    assert negative["curvature_derivative_omission"][
        "minimum_absolute_discrepancy_from_reference"
    ] == 0.04
    assert negative["inconsistent_frozen_connection"][
        "minimum_error_ratio"
    ] == 50.0
    expected = {
        "minimum_convergence_order_two_finest_pairs": 1.8,
        "maximum_finest_combined_off_shell_relative_error": 0.02,
        "maximum_exact_coefficient_absolute_error": 1e-12,
        "minimum_finest_off_to_on_divergence_norm_ratio": 100.0,
        "maximum_metric_compatibility_absolute_error": 1e-12,
        "maximum_flat_limit_absolute_discrepancy": 1e-12,
        "maximum_curvature_route_absolute_discrepancy": 1e-12,
        "minimum_absolute_scalar_curvature": 0.05,
        "minimum_naive_partial_divergence_identity_error_ratio": 100.0,
        "minimum_curvature_omission_absolute_discrepancy": 0.04,
        "minimum_inconsistent_frozen_connection_identity_error_ratio": 50.0,
        "all_thresholds_required": True,
    }
    assert thresholds == expected


def test_failure_route_outputs_and_no_execution_flags_are_frozen() -> None:
    payload = build_guardrail_payload()
    failure = payload["failure_criteria"]
    assert failure["primary_claim_label"] == "B-BLOCKED"
    assert failure["selected_repair_target"] == THRESHOLD_REPAIR_TARGET
    assert failure["failed_artifacts_preserved"] is True
    assert failure["threshold_changes_require_new_versioned_guardrail"] is True
    assert set(payload["outputs"]) == {"result", "manifest", "execution_report"}
    assert payload["calculation_executed"] is False
    assert payload["e_repro_claimed"] is False
    assert payload["equation_compendium_row_added"] is False


def test_predecessor_and_readiness_hashes_are_exact() -> None:
    payload = build_guardrail_payload()
    assert payload["accepted_predecessor"]["sha256"] == (
        "752c4f92521e55ca125024ea0b5956838ac32230dcee5356f6e2a5ed2176c0df"
    )
    assert payload["readiness_authority"]["sha256"] == (
        "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1"
    )


def test_release_artifact_matches_deterministic_builder_bytes() -> None:
    payload = build_guardrail_payload()
    assert GUARDRAIL_REPORT_PATH.read_bytes() == report_json_bytes(payload)


def test_canonical_contract_rejects_nonfinite_numbers() -> None:
    payload = build_guardrail_payload()
    assert canonical_json_bytes(payload).endswith(b"\n")
    payload["inputs"]["conformal_hubble_parameter_H"] = math.inf
    with pytest.raises(ValueError):
        canonical_json_bytes(payload)


def test_execution_report_verifies_hashes_and_selects_separate_review() -> None:
    payload = build_execution_report()
    assert payload["status"] == "executed_pending_result_review"
    assert payload["consumed_target"] == EXECUTION_TARGET
    assert payload["consumed_target_kind"] == EXECUTION_TARGET_KIND
    assert payload["selected_next_target"] == REVIEW_TARGET
    assert payload["selected_next_target_kind"] == REVIEW_TARGET_KIND
    assert payload["packet_result"] == EXECUTION_OUTCOME
    assert payload["strict_packet_result"] == EXECUTION_STRICT_OUTCOME
    assert payload["guardrail_sha256"] == EXPECTED_GUARDRAIL_SHA256
    assert payload["calculation_output_sha256"] == (
        "4d0d04421c8b0d310f0caa73c4da3755f2afa91a4043bab9f96011c9b03ecf4f"
    )
    assert payload["calculation_manifest_sha256"] == (
        "46e752fd0a8571fd06dd0f1f9a7046f12a43413761ea39a3cb904b959a4a6827"
    )
    assert payload["calculation_script_sha256"] == (
        "253632cc6773d242a76db26befde13dc2578a2950c097a8c628b8e061ffdbd03"
    )
    assert payload["calculation_output_sha256"] == sha256_path(
        CALCULATION_OUTPUT_PATH
    )
    assert payload["calculation_manifest_sha256"] == sha256_path(
        CALCULATION_MANIFEST_PATH
    )
    assert payload["calculation_script_sha256"] == sha256_path(
        CALCULATION_SCRIPT_PATH
    )


def test_execution_report_records_curvature_patch_and_three_controls() -> None:
    payload = build_execution_report()
    assert payload["background_geometry_classification"] == (
        "fixed_nonzero_curvature_1plus1_de_sitter_patch"
    )
    assert payload["guardrail_geometry_classification"] == (
        "fixed_1_plus_1_de_sitter_conformal_patch"
    )
    assert payload["scalar_curvature_expected"] == 0.08
    assert payload["scalar_curvature_measured"] == 0.08
    curvature = payload["curvature_verification"]
    assert curvature["maximum_route_agreement_absolute_error"] <= 1e-12
    assert curvature["minimum_absolute_measured_scalar_curvature"] >= 0.05
    assert curvature["ricci_relation_max_absolute_error"] <= 1e-12
    patch = payload["patch_domain_safety"]
    assert patch["eta_domain"] == [0.0, 1.0]
    assert patch["minimum_one_minus_H_eta_over_domain"] == 0.8
    assert patch["maximum_scale_factor_over_domain"] == 1.25
    assert patch[
        "minimum_coordinate_distance_to_patch_singularity_over_domain"
    ] == 4.0
    assert patch["coordinate_patch_singularity_eta"] == 5.0
    assert patch["strictly_inside_coordinate_patch"] is True
    assert patch["derived_invariant_not_additional_guardrail_threshold"] is True
    assert set(payload["negative_controls"]) == {
        "naive_partial_divergence",
        "inconsistent_frozen_connection",
        "curvature_derivative_omission",
    }
    assert all(
        control["failure_detected"] is True
        for control in payload["negative_controls"].values()
    )


def test_execution_report_records_all_thresholds_and_2d_gravity_boundary() -> None:
    payload = build_execution_report()
    assert payload["control_counts"] == {
        "curvature_verification_route_count": 2,
        "negative_control_count": 3,
        "frozen_threshold_count": 11,
        "on_shell_time_resolution_rows": 12,
        "off_shell_time_resolution_rows": 12,
        "time_slice_count": 3,
        "resolution_count": 4,
        "divergence_component_count": 2,
    }
    assert len(payload["threshold_checks"]) == 11
    assert all(payload["threshold_checks"].values())
    assert payload["all_thresholds_passed"] is True
    assert payload["claim"] == {
        "primary_label": "E-REPRO",
        "claim_status": "generated_pending_result_review",
        "claim_ceiling_level": 3,
        "claim_scope": (
            "scoped E-REPRO pending review for the scalar covariant "
            "stress-energy divergence identity on one fixed 1+1 de Sitter "
            "background"
        ),
    }
    boundary = payload["boundary"]
    assert payload["gravity_evolved"] is False
    assert payload["einstein_tensor_source_tested"] is False
    assert payload["two_dimensional_einstein_gravity_degenerate"] is True
    assert payload["covariant_matter_identity_tested"] is True
    assert boundary["einstein_tensor_identically_zero_in_two_dimensions"] is True
    assert boundary["ordinary_einstein_scalar_dynamics_claimed"] is False
    assert boundary["source_admissibility_claimed"] is False
    assert boundary["bianchi_compatibility_claimed"] is False
    assert boundary["qft_gr_seam_admissibility_claimed"] is False
    assert boundary["master_action_promoted"] is False


def test_execution_release_artifact_matches_deterministic_builder_bytes() -> None:
    payload = build_execution_report()
    assert EXECUTION_REPORT_PATH.read_bytes() == report_json_bytes(payload)


def test_execution_and_review_are_preserved_after_review_rotation() -> None:
    registry = loop_registry()
    state = current_target_state(registry)
    active = active_workstream(registry)
    execution = workstream(EXECUTION_TARGET, registry)
    review = workstream(REVIEW_TARGET, registry)
    higher_dimensional_guardrail = workstream(
        HIGHER_DIMENSIONAL_CURVED_BACKGROUND_GUARDRAIL_TARGET,
        registry,
    )
    assert execution["status"] == "paused"
    assert execution["selected_next_target"] == REVIEW_TARGET
    assert review["status"] == "paused"
    assert review["selected_next_target"] == (
        HIGHER_DIMENSIONAL_CURVED_BACKGROUND_GUARDRAIL_TARGET
    )
    assert review["report_sha256"] == (
        "21068eaff2b509401afb635e4f7bce4eb409edb8a5cff6dfe4bea7dfe7a3d2c8"
    )
    assert review["calculation_output_sha256"] == (
        "4d0d04421c8b0d310f0caa73c4da3755f2afa91a4043bab9f96011c9b03ecf4f"
    )
    assert review["calculation_manifest_sha256"] == (
        "46e752fd0a8571fd06dd0f1f9a7046f12a43413761ea39a3cb904b959a4a6827"
    )
    assert review["frozen_threshold_count"] == 11
    assert len(review["threshold_checks"]) == 11
    assert all(review["threshold_checks"].values())
    assert review["two_dimensional_einstein_gravity_degenerate"] == "yes"
    assert review["einstein_tensor_source_tested"] == "no"
    assert higher_dimensional_guardrail["status"] == "paused"
    assert higher_dimensional_guardrail["selected_next_target"] == (
        "execute_calc_scalar_stress_energy_covariant_divergence_identity_"
        "higher_dimensional_curved_background_v0"
    )
    assert state["previous_live_next_target"] == (
        HIGHER_DIMENSIONAL_CURVED_BACKGROUND_GUARDRAIL_TARGET
    )
    assert state["live_next_target"] == (
        "execute_calc_scalar_stress_energy_covariant_divergence_identity_"
        "higher_dimensional_curved_background_v0"
    )
    assert active["workstream_id"] == state["live_next_target"]
    assert active["calculation_executed"] == "no"
    assert active["report_sha256"] == (
        "e6ce9dfb08364e3fa3a0a3895a3d1b16635348ab2fc7b0490f0b3b6e04db6b96"
    )
