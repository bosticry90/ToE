from __future__ import annotations

import copy
import json
import math
from pathlib import Path

import pytest

from formal.python.tools.scalar_higher_dimensional_curved_background_reports import (
    BACKGROUND_GEOMETRY_CLASSIFICATION,
    EQUATION_ID,
    EXECUTION_TARGET,
    EXECUTION_TARGET_KIND,
    EXPECTED_GUARDRAIL_SHA256,
    EXPECTED_PREDECESSOR_REVIEW_SHA256,
    EXPECTED_READINESS_SHA256,
    GUARDRAIL_OUTCOME,
    GUARDRAIL_REPORT_PATH,
    GUARDRAIL_STRICT_OUTCOME,
    GUARDRAIL_TARGET,
    NEGATIVE_CONTROL_IDS,
    PACKET_ID,
    PACKET_SCHEMA_ID,
    SPATIAL_RESOLUTIONS,
    THRESHOLD_IDS,
    TIME_SLICES,
    build_guardrail_payload,
    canonical_json_bytes,
    guardrail_main,
    report_json_bytes,
    sha256_path,
    validate_guardrail_payload,
)


def test_guardrail_freezes_lifecycle_and_accepted_predecessor() -> None:
    payload = build_guardrail_payload()
    validate_guardrail_payload(payload)
    assert payload["schema_id"] == PACKET_SCHEMA_ID
    assert payload["packet_id"] == PACKET_ID
    assert payload["consumed_target"] == GUARDRAIL_TARGET
    assert payload["selected_next_target"] == EXECUTION_TARGET
    assert payload["selected_next_target_kind"] == EXECUTION_TARGET_KIND
    assert payload["packet_result"] == GUARDRAIL_OUTCOME
    assert payload["strict_packet_result"] == GUARDRAIL_STRICT_OUTCOME
    assert payload["accepted_predecessor"]["sha256"] == (
        EXPECTED_PREDECESSOR_REVIEW_SHA256
    )
    assert payload["readiness_authority"]["sha256"] == EXPECTED_READINESS_SHA256


def test_metric_inverse_determinant_volume_and_domain_are_frozen() -> None:
    payload = build_guardrail_payload()
    inputs = payload["inputs"]
    geometry = payload["background_geometry"]
    assert inputs["coordinates"] == ["t", "x", "y"]
    assert inputs["coordinate_indices"] == {"t": 0, "x": 1, "y": 2}
    assert inputs["spacetime_dimension"] == 3
    assert inputs["dimension_label"] == "2+1"
    assert inputs["coordinate_domain"] == {
        "t": "frozen evaluation slices in [0,1]",
        "x": "x in [0,2*pi), periodic",
        "y": "y in [0,2*pi), periodic",
    }
    assert inputs["warp_amplitude_epsilon"] == 0.2
    assert inputs["warp_factor_minimum"] == 0.8
    assert inputs["warp_factor_maximum"] == 1.2
    assert geometry["classification"] == BACKGROUND_GEOMETRY_CLASSIFICATION
    assert geometry["metric"] == "g_mu_nu = diag(-1, 1, f(x)^2)"
    assert geometry["inverse_metric"] == (
        "g^mu_nu = diag(-1, 1, f(x)^(-2))"
    )
    assert geometry["determinant"] == "det(g_mu_nu) = -f(x)^2"
    assert geometry["volume_density"] == (
        "sqrt(-g) = f(x), because f(x) >= 0.8"
    )


def test_christoffels_curvature_conventions_and_two_routes_are_frozen() -> None:
    payload = build_guardrail_payload()
    conventions = payload["connection_and_curvature_conventions"]
    curvature = payload["curvature_verification"]
    assert conventions["nonzero_christoffels"] == {
        "Gamma^x_{y y}": "-f(x)*f'(x)",
        "Gamma^y_{x y}": "f'(x)/f(x)",
        "Gamma^y_{y x}": "f'(x)/f(x)",
    }
    assert conventions["expected_ricci_components"] == {
        "R_t t": "0",
        "R_x x": "-f''(x)/f(x)",
        "R_y y": "-f(x)*f''(x)",
    }
    assert conventions["einstein_tensor_not_identically_zero"] is True
    assert conventions["einstein_tensor_source_tested"] is False
    assert set(curvature) >= {
        "analytic_warped_product_route",
        "independent_generic_tensor_route",
    }
    assert curvature["independent_generic_tensor_route"]["route"] == [
        "metric",
        "inverse_metric",
        "metric_derivatives",
        "Christoffel_symbols",
        "Riemann_tensor",
        "Ricci_tensor",
        "scalar_contraction",
    ]
    assert "do not call" in curvature["independent_generic_tensor_route"][
        "implementation_independence"
    ]


@pytest.mark.parametrize("x", [0.0, 0.31, math.pi / 2, math.pi, 5.2])
def test_independent_component_reconstruction_matches_frozen_curvature(
    x: float,
) -> None:
    epsilon = 0.2
    f = 1.0 + epsilon * math.cos(x)
    f_prime = -epsilon * math.sin(x)
    f_double_prime = -epsilon * math.cos(x)

    gamma_x_yy = -f * f_prime
    gamma_y_xy = f_prime / f
    derivative_gamma_y_xy = (f_double_prime * f - f_prime**2) / f**2
    derivative_gamma_x_yy = -(f_prime**2 + f * f_double_prime)

    ricci_xx = -derivative_gamma_y_xy - gamma_y_xy**2
    ricci_yy = (
        derivative_gamma_x_yy
        + gamma_y_xy * gamma_x_yy
        - 2.0 * gamma_x_yy * gamma_y_xy
    )
    reconstructed_scalar = ricci_xx + ricci_yy / f**2
    analytic_scalar = 2.0 * epsilon * math.cos(x) / f
    assert ricci_xx == pytest.approx(-f_double_prime / f, abs=1e-15)
    assert ricci_yy == pytest.approx(-f * f_double_prime, abs=1e-15)
    assert reconstructed_scalar == pytest.approx(analytic_scalar, abs=1e-15)


def test_curvature_crosses_zero_but_has_frozen_range_and_variation() -> None:
    payload = build_guardrail_payload()
    geometry = payload["background_geometry"]
    curvature = payload["curvature_verification"]
    assert geometry["curvature_zero_crossings_allowed"] is True
    assert geometry["scalar_curvature_minimum"] == -0.5
    assert geometry["scalar_curvature_maximum"] == pytest.approx(1.0 / 3.0)
    assert geometry["scalar_curvature_peak_to_peak"] == pytest.approx(5.0 / 6.0)
    assert curvature["minimum_peak_absolute_scalar_curvature"] == 0.49
    assert curvature["minimum_peak_to_peak_scalar_curvature"] == 0.8
    assert "minimum pointwise" not in json.dumps(curvature)


def test_action_dalembertian_identity_and_three_components_are_frozen() -> None:
    equations = build_guardrail_payload()["equation_surfaces"]
    assert equations["potential"] == "V(phi) = 1/2 m^2 phi^2"
    assert equations["field_residual"] == "E_phi = Box_g phi - m^2 phi"
    assert equations["covariant_dalembertian"] == (
        "Box_g phi = -partial_t^2 phi + partial_x^2 phi + "
        "[f'(x)/f(x)] partial_x phi + f(x)^(-2) partial_y^2 phi"
    )
    assert equations["identity"] == (
        "nabla_mu T^{mu nu} = E_phi nabla^nu phi"
    )
    assert equations["divergence_components_required"] == [0, 1, 2]
    assert equations["divergence_component_labels"] == [
        "nu=t",
        "nu=x",
        "nu=y",
    ]


def test_on_shell_and_two_distinct_off_shell_profiles_are_frozen() -> None:
    controls = build_guardrail_payload()["solution_controls"]
    assert set(controls) == {
        "on_shell_temporal_mode",
        "off_shell_y_mode",
        "off_shell_x_mode",
    }
    assert controls["on_shell_temporal_mode"]["exact_residual"] == "E_phi = 0"
    assert controls["on_shell_temporal_mode"]["forced_or_manufactured"] is False
    assert controls["off_shell_y_mode"]["parameters"] == {
        "A": 0.2,
        "omega_y": 1.5,
        "ell": 2,
    }
    assert controls["off_shell_y_mode"]["exact_residual"] == (
        "E_phi = [omega_y^2-m^2-ell^2/f(x)^2]*phi_y"
    )
    assert controls["off_shell_x_mode"]["parameters"] == {
        "A": 0.2,
        "omega_x": 1.7,
        "k": 2,
    }
    assert controls["off_shell_x_mode"]["exact_residual"] == (
        "E_phi = (omega_x^2-m^2-k^2)*phi_x - "
        "A*k*[f'(x)/f(x)]*cos(omega_x*t)*sin(k*x)"
    )


def test_periodic_refinement_norms_and_determinism_are_frozen() -> None:
    payload = build_guardrail_payload()
    method = payload["numerical_method"]
    assert payload["inputs"]["time_slices"] == TIME_SLICES
    assert payload["inputs"]["spatial_resolutions_Nx_equals_Ny"] == (
        SPATIAL_RESOLUTIONS
    )
    assert method["refinement_schedule"] == {
        "Nx_equals_Ny": [32, 64, 128, 256],
        "delta_x_equals_delta_y": "2*pi/N",
        "refinement_ratio": 2,
    }
    assert method["convergence_profiles"] == [
        "off_shell_y_mode",
        "off_shell_x_mode",
    ]
    assert "for each nu" in method["component_rms_norm_at_each_time"]
    assert "sum_{nu=0}^2" in method["combined_rms_norm_at_each_time"]
    assert "two fresh-process" in method["determinism"]


def test_positive_flat_limit_is_distinct_from_five_negative_controls() -> None:
    payload = build_guardrail_payload()
    flat = payload["flat_limit_control"]
    negative = payload["negative_controls"]
    assert flat["positive_control"]["substitution"] == "epsilon -> 0, hence f -> 1"
    assert flat["positive_control"]["expected_metric"] == "diag(-1,1,1)"
    assert flat["positive_control"]["expected_scalar_curvature"] == 0.0
    assert "changes both geometry and analytic reference" in flat[
        "distinct_from_negative_control"
    ]
    assert set(negative) == NEGATIVE_CONTROL_IDS
    assert len(negative) == 5
    assert "retaining the epsilon=0.2 curved analytic identity reference" in (
        negative["curved_case_flat_geometry_substitution"]["operation"]
    )
    assert "f(x)^(-2)" in negative["incorrect_y_inverse_metric_factor"][
        "operation"
    ]
    assert "correct epsilon=0.2 curved analytic residual" in negative[
        "incorrect_y_inverse_metric_factor"
    ]["comparison_reference"]
    assert "minimum of the two profile-specific ratios" in negative[
        "naive_partial_divergence"
    ]["evaluation"]
    assert "max(space-time combined RMS correct covariant identity error,1e-14)" in (
        negative["naive_partial_divergence"]["ratio_definition"]
    )
    for control in (
        "omitted_tensor_index_connection_term",
        "omitted_volume_trace_connection_term",
    ):
        assert "max(correct on-shell combined absolute divergence error,1e-14)" in (
            negative[control]["ratio_definition"]
        )
    assert "minimum profile-specific normalized discrepancy" in negative[
        "curved_case_flat_geometry_substitution"
    ]["evaluation"]
    assert "1e-14" in negative["curved_case_flat_geometry_substitution"][
        "normalized_discrepancy_definition"
    ]
    assert "1e-14" in negative["incorrect_y_inverse_metric_factor"][
        "normalized_discrepancy_definition"
    ]


def test_sixteen_frozen_thresholds_cannot_be_aggregated_away() -> None:
    payload = build_guardrail_payload()
    criteria = payload["success_criteria"]
    assert set(criteria) == THRESHOLD_IDS | {"all_thresholds_required"}
    assert len(THRESHOLD_IDS) == 16
    assert criteria["all_thresholds_required"] is True
    assert criteria["minimum_two_finest_y_mode_convergence_order"] == 1.8
    assert criteria["minimum_two_finest_x_mode_convergence_order"] == 1.8
    assert criteria["maximum_curvature_route_absolute_discrepancy"] == 1e-12
    assert criteria["minimum_naive_partial_divergence_error_ratio"] == 10.0
    assert payload["failure_criteria"][
        "control_aggregation_cannot_hide_individual_failure"
    ] is True
    assert "not a finite-difference Box_g residual" in payload[
        "success_criteria_definitions"
    ]["maximum_exact_residual_absolute_error"]
    assert payload["success_criteria_definitions"][
        "negative_control_resolution_adjudication"
    ] == (
        "report every frozen resolution; adjudicate each negative-control "
        "threshold on the finest frozen grid N=256"
    )


def test_level_three_equation_reuse_and_nonclaims_are_frozen() -> None:
    payload = build_guardrail_payload()
    equations = payload["equation_surfaces"]
    claim = payload["claim_ceiling"]
    boundary = payload["boundary"]
    assert equations["existing_equation_id_reused"] == EQUATION_ID
    assert equations["existing_equation_status"] == (
        "ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO"
    )
    assert equations["new_equation_identity_created"] is False
    assert equations["equation_surface_upgraded"] is False
    assert equations["equation_compendium_edited"] is False
    assert claim["claim_ladder_level"] == 3
    assert all(
        claim[key] is True
        for key in claim
        if key.startswith("not_")
    )
    assert boundary["einstein_tensor_can_be_nonzero"] is True
    assert boundary["einstein_tensor_source_tested"] is False
    assert boundary["gravity_evolved"] is False
    assert boundary["bianchi_compatibility_claimed"] is False
    assert boundary["qft_gr_seam_admissibility_claimed"] is False
    assert payload["calculation_executed"] is False
    assert payload["e_repro_claimed_by_guardrail"] is False


def test_release_artifact_matches_deterministic_builder_bytes() -> None:
    payload = build_guardrail_payload()
    assert GUARDRAIL_REPORT_PATH.read_bytes() == report_json_bytes(payload)
    assert sha256_path(GUARDRAIL_REPORT_PATH) == EXPECTED_GUARDRAIL_SHA256


def test_wrapper_writes_exact_bytes_and_summary(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    output = tmp_path / "guardrail.json"
    assert guardrail_main(["--out", str(output)]) == 0
    assert output.read_bytes() == report_json_bytes(build_guardrail_payload())
    summary = json.loads(capsys.readouterr().out)
    assert summary["outcome"] == GUARDRAIL_OUTCOME
    assert summary["selected_next_target"] == EXECUTION_TARGET
    assert summary["negative_control_count"] == 5
    assert summary["threshold_count"] == 16


def test_canonical_contract_rejects_nonfinite_numbers() -> None:
    payload = build_guardrail_payload()
    assert canonical_json_bytes(payload).endswith(b"\n")
    payload["inputs"]["warp_amplitude_epsilon"] = math.inf
    with pytest.raises(ValueError):
        canonical_json_bytes(payload)


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        (
            lambda p: p.__setitem__("selected_next_target", "execute_wrong"),
            "lifecycle",
        ),
        (
            lambda p: p["accepted_predecessor"].__setitem__("sha256", "0" * 64),
            "predecessor",
        ),
        (
            lambda p: p["readiness_authority"].__setitem__("sha256", "0" * 64),
            "readiness-authority",
        ),
        (
            lambda p: p["inputs"].__setitem__("warp_amplitude_epsilon", 0.3),
            "inputs",
        ),
        (
            lambda p: p["background_geometry"].__setitem__(
                "metric", "diag(-1,1,1)"
            ),
            "geometry",
        ),
        (
            lambda p: p["connection_and_curvature_conventions"][
                "nonzero_christoffels"
            ].__setitem__("Gamma^x_{y y}", "+f(x)*f'(x)"),
            "Christoffel",
        ),
        (
            lambda p: p["equation_surfaces"].__setitem__(
                "equation_surface_upgraded", True
            ),
            "equation-surface",
        ),
        (
            lambda p: p["solution_controls"].pop("off_shell_y_mode"),
            "field-profile",
        ),
        (
            lambda p: p["solution_controls"]["off_shell_x_mode"].__setitem__(
                "exact_residual",
                "E_phi = (omega_x^2-m^2-k^2)*phi_x + "
                "A*k*[f'(x)/f(x)]*cos(omega_x*t)*sin(k*x)",
            ),
            "analytic field residual",
        ),
        (
            lambda p: p["negative_controls"].pop(
                "omitted_volume_trace_connection_term"
            ),
            "five frozen negative controls",
        ),
        (
            lambda p: p["negative_controls"]["naive_partial_divergence"].__setitem__(
                "ratio_definition", "pooled ratio with no denominator floor"
            ),
            "norm or adjudication policy",
        ),
        (
            lambda p: p["success_criteria"].pop(
                "maximum_flat_limit_absolute_discrepancy"
            ),
            "threshold set or value",
        ),
        (
            lambda p: p["success_criteria"].__setitem__(
                "minimum_naive_partial_divergence_error_ratio", 0.0
            ),
            "threshold set or value",
        ),
        (
            lambda p: p["required_controls"].__setitem__(
                "flat_limit_recovery", False
            ),
            "required control",
        ),
        (
            lambda p: p["claim_ceiling"].__setitem__(
                "not_bianchi_compatibility", False
            ),
            "nonclaim",
        ),
        (
            lambda p: p["boundary"].__setitem__(
                "einstein_tensor_source_tested", True
            ),
            "overclaims",
        ),
        (
            lambda p: p.__setitem__("calculation_executed", True),
            "premature execution",
        ),
    ],
)
def test_adversarial_mutations_are_rejected(mutation: object, message: str) -> None:
    payload = copy.deepcopy(build_guardrail_payload())
    mutation(payload)  # type: ignore[operator]
    with pytest.raises(ValueError, match=message):
        validate_guardrail_payload(payload)


@pytest.mark.parametrize(
    "mutation",
    [
        lambda p: p["inputs"]["coordinate_domain"].__setitem__(
            "x", "x in [0,pi), not the frozen periodic domain"
        ),
        lambda p: p["connection_and_curvature_conventions"].__setitem__(
            "riemann_sign", "opposite sign convention"
        ),
        lambda p: p["connection_and_curvature_conventions"].__setitem__(
            "expected_ricci_components", {"R_t t": "wrong"}
        ),
        lambda p: p["equation_surfaces"].__setitem__(
            "covariant_dalembertian", "wrong Box_g"
        ),
        lambda p: p["equation_surfaces"].__setitem__(
            "stress_energy", "wrong stress tensor"
        ),
        lambda p: p["equation_surfaces"].__setitem__(
            "identity", "wrong identity"
        ),
        lambda p: p["numerical_method"].__setitem__(
            "periodic_boundary_handling", "nonperiodic"
        ),
        lambda p: p["numerical_method"].__setitem__(
            "temporal_derivatives", "finite differences"
        ),
        lambda p: p["numerical_method"].__setitem__(
            "component_rms_norm_at_each_time", "signed Lorentzian norm"
        ),
        lambda p: p["negative_controls"]["naive_partial_divergence"].__setitem__(
            "operation", "keep all connection terms"
        ),
        lambda p: p["claim_ceiling"].__setitem__(
            "e_repro_status", "accepted"
        ),
        lambda p: p["boundary"].__setitem__(
            "general_covariant_conservation_claimed", True
        ),
    ],
)
def test_every_frozen_science_contract_is_exact(mutation: object) -> None:
    payload = copy.deepcopy(build_guardrail_payload())
    mutation(payload)  # type: ignore[operator]
    with pytest.raises(ValueError, match="exact frozen contract"):
        validate_guardrail_payload(payload)
