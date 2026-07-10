from __future__ import annotations

import math

import pytest

from formal.python.tools.scalar_nonzero_curvature_background_reports import (
    EQUATION_ID,
    EXECUTION_TARGET,
    EXECUTION_TARGET_KIND,
    GUARDRAIL_OUTCOME,
    GUARDRAIL_REPORT_PATH,
    GUARDRAIL_STRICT_OUTCOME,
    GUARDRAIL_TARGET,
    PACKET_ID,
    PACKET_SCHEMA_ID,
    THRESHOLD_REPAIR_TARGET,
    build_guardrail_payload,
    canonical_json_bytes,
    report_json_bytes,
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
