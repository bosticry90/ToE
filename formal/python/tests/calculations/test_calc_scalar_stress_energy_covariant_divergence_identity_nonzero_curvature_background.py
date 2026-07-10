from __future__ import annotations

import hashlib
import json

import pytest

from formal.python.toe.calculations.calc_scalar_stress_energy_covariant_divergence_identity_nonzero_curvature_background import (
    BACKGROUND_GEOMETRY_CLASSIFICATION,
    CALCULATION_ID,
    EXPECTED_SCALAR_CURVATURE,
    HUBBLE_PARAMETER,
    MANIFEST_RELATIVE_PATH,
    OMEGA_OFF,
    OMEGA_ON,
    OUTPUT_RELATIVE_PATH,
    REPO_ROOT,
    RESOLUTIONS,
    RESULT_REVIEW_TARGET,
    TIME_SLICES,
    analytic_scalar_curvature,
    build_result,
    canonical_json_bytes,
    evaluate_time_slice,
    metric_compatibility_max_error,
    patch_domain_safety,
    reconstruct_curvature,
    write_artifacts,
)


def test_independent_curvature_reconstruction_matches_analytic_route() -> None:
    for time in TIME_SLICES:
        analytic = analytic_scalar_curvature(time=time)
        component = reconstruct_curvature(time=time)
        assert analytic == pytest.approx(EXPECTED_SCALAR_CURVATURE, abs=1e-15)
        assert component["scalar_curvature"] == pytest.approx(
            EXPECTED_SCALAR_CURVATURE, abs=1e-15
        )
        assert component["ricci_relation_max_absolute_error"] <= 1e-15
        assert component["nonzero_connection_component_count"] == 4
        assert metric_compatibility_max_error(time=time) <= 1e-15


def test_curvature_derivative_omission_is_a_real_negative_control() -> None:
    for time in TIME_SLICES:
        correct = reconstruct_curvature(time=time)["scalar_curvature"]
        omitted = reconstruct_curvature(
            time=time,
            omit_connection_derivatives=True,
        )["scalar_curvature"]
        assert omitted == pytest.approx(0.0, abs=1e-15)
        assert abs(correct - omitted) >= 0.04


def test_patch_domain_safety_uses_full_domain_not_only_sample_slices() -> None:
    safety = patch_domain_safety()
    assert safety["eta_domain"] == [0.0, 1.0]
    assert safety["coordinate_patch_singularity_eta"] == 5.0
    assert safety["minimum_one_minus_H_eta_over_domain"] == 0.8
    assert safety["maximum_scale_factor_over_domain"] == 1.25
    assert (
        safety["minimum_coordinate_distance_to_patch_singularity_over_domain"]
        == 4.0
    )
    assert safety["sampled_minimum_one_minus_H_eta"] == 0.818
    assert safety["sampled_maximum_scale_factor"] == pytest.approx(
        1.2224938875305624
    )
    assert safety["sampled_minimum_coordinate_distance_to_patch_singularity"] == (
        4.09
    )
    assert safety["strictly_inside_coordinate_patch"] is True
    assert safety["coordinate_patch_boundary_is_physical_curvature_singularity"] is (
        False
    )
    assert safety["derived_invariant_not_additional_guardrail_threshold"] is True


def test_exact_source_free_and_off_shell_residual_controls() -> None:
    on_shell = evaluate_time_slice(
        resolution=RESOLUTIONS[-1],
        time=TIME_SLICES[-1],
        omega=OMEGA_ON,
    )
    off_shell = evaluate_time_slice(
        resolution=RESOLUTIONS[-1],
        time=TIME_SLICES[-1],
        omega=OMEGA_OFF,
    )
    assert on_shell["exact_residual_reference"][
        "computed_coefficient_before_a_inverse_squared"
    ] == 0.0
    assert on_shell["exact_residual_reference"][
        "field_residual_absolute_error_norm"
    ] == 0.0
    assert off_shell["exact_residual_reference"][
        "computed_coefficient_before_a_inverse_squared"
    ] == pytest.approx(0.84)
    assert off_shell["exact_residual_reference"][
        "coefficient_absolute_error"
    ] <= 1e-12
    assert off_shell["exact_residual_reference"][
        "field_residual_absolute_error_norm"
    ] <= 1e-15


def test_frozen_connection_changes_only_the_divergence_connection() -> None:
    eta_zero = evaluate_time_slice(
        resolution=RESOLUTIONS[-1],
        time=0.0,
        omega=OMEGA_ON,
    )
    curved_slice = evaluate_time_slice(
        resolution=RESOLUTIONS[-1],
        time=TIME_SLICES[-1],
        omega=OMEGA_ON,
    )
    at_zero = eta_zero["negative_control_errors"]
    away_from_zero = curved_slice["negative_control_errors"]
    assert at_zero["inconsistent_frozen_connection_combined"] == pytest.approx(
        at_zero["correct_covariant_combined"], abs=1e-15
    )
    assert away_from_zero["inconsistent_frozen_connection_combined"] > (
        50.0 * away_from_zero["correct_covariant_combined"]
    )


def test_result_passes_all_eleven_frozen_thresholds() -> None:
    result = build_result()
    evidence = result["threshold_evidence"]
    assert len(result["threshold_checks"]) == 11
    assert result["frozen_threshold_count"] == 11
    assert all(result["threshold_checks"].values())
    assert result["all_thresholds_passed"] is True
    assert evidence["minimum_observed_two_finest_convergence_order"] >= 1.8
    assert evidence["finest_combined_off_shell_relative_error"] <= 0.02
    assert evidence["exact_coefficient_absolute_error"] <= 1e-12
    assert evidence["finest_off_to_on_divergence_norm_ratio"] >= 100.0
    assert evidence["metric_compatibility_max_absolute_error"] <= 1e-12
    assert evidence["flat_limit_max_absolute_discrepancy"] <= 1e-12
    assert evidence["curvature_route_max_absolute_discrepancy"] <= 1e-12
    assert evidence["minimum_absolute_measured_scalar_curvature"] >= 0.05
    assert evidence["finest_on_shell_naive_to_correct_error_ratio"] >= 100.0
    assert evidence["curvature_omission_minimum_absolute_discrepancy"] >= 0.04
    assert evidence[
        "finest_minimum_on_off_frozen_connection_to_correct_error_ratio"
    ] >= 50.0


def test_result_records_geometry_and_two_dimensional_einstein_boundary() -> None:
    result = build_result()
    assert result["background_geometry_classification"] == (
        BACKGROUND_GEOMETRY_CLASSIFICATION
    )
    assert result["scalar_curvature_expected"] == EXPECTED_SCALAR_CURVATURE
    assert result["scalar_curvature_measured"] == pytest.approx(
        EXPECTED_SCALAR_CURVATURE, abs=1e-15
    )
    assert result["gravity_evolved"] is False
    assert result["einstein_tensor_source_tested"] is False
    assert result["two_dimensional_einstein_gravity_degenerate"] is True
    assert result["covariant_matter_identity_tested"] is True
    boundary = result["boundary"]
    assert boundary["einstein_tensor_identically_zero_in_two_dimensions"] is True
    assert boundary["ordinary_einstein_scalar_dynamics_claimed"] is False
    assert boundary["source_admissibility_claimed"] is False
    assert boundary["bianchi_compatibility_claimed"] is False
    assert boundary["qft_gr_seam_admissibility_claimed"] is False
    assert result["claim"]["claim_ceiling_level"] == 3
    assert result["claim"]["claim_status"] == "generated_pending_result_review"
    assert result["result_review"]["target"] == RESULT_REVIEW_TARGET


def test_generated_artifacts_are_canonical_and_hash_bound() -> None:
    output_path = REPO_ROOT / OUTPUT_RELATIVE_PATH
    manifest_path = REPO_ROOT / MANIFEST_RELATIVE_PATH
    result = json.loads(output_path.read_text(encoding="utf-8"))
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert output_path.read_bytes() == canonical_json_bytes(result)
    assert manifest_path.read_bytes() == canonical_json_bytes(manifest)
    assert manifest["calculation_id"] == CALCULATION_ID
    assert manifest["output_sha256"] == hashlib.sha256(
        output_path.read_bytes()
    ).hexdigest()
    assert manifest["guardrail_sha256"] == (
        "3670bfaa98876b32e95f5ff7406546a41aa691f937fe738fee6e3ab36a399191"
    )
    assert manifest["background_geometry_classification"] == (
        BACKGROUND_GEOMETRY_CLASSIFICATION
    )
    assert manifest["two_dimensional_einstein_gravity_degenerate"] is True


def test_fresh_write_is_deterministic(tmp_path) -> None:
    output_path = tmp_path / "result.json"
    manifest_path = tmp_path / "manifest.json"
    result, manifest = write_artifacts(
        output_path=output_path,
        manifest_path=manifest_path,
    )
    assert output_path.read_bytes() == canonical_json_bytes(result)
    assert manifest_path.read_bytes() == canonical_json_bytes(manifest)
    assert manifest["output_sha256"] == hashlib.sha256(
        output_path.read_bytes()
    ).hexdigest()
    assert result["all_thresholds_passed"] is True
    assert HUBBLE_PARAMETER == 0.2
