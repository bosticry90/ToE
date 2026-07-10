from __future__ import annotations

import json
import math
from pathlib import Path

import pytest

from formal.python.toe.calculations.calc_scalar_stress_energy_covariant_divergence_identity_conformal_background import (
    CAPTURED_AT_UTC,
    MANIFEST_RELATIVE_PATH,
    OUTPUT_RELATIVE_PATH,
    REPO_ROOT,
    RESOLUTIONS,
    RESULT_REVIEW_TARGET,
    build_result,
    canonical_json_bytes,
    evaluate_time_slice,
    flat_limit_max_discrepancy,
    geometry_diagnostics,
    metric_compatibility_max_error,
    write_artifacts,
)


OUTPUT_PATH = REPO_ROOT / OUTPUT_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH


def test_geometry_is_locally_flat_with_nontrivial_connection() -> None:
    geometry = geometry_diagnostics()
    assert geometry["background_geometry_classification"] == (
        "locally_flat_nontrivial_conformal_connection"
    )
    assert geometry["scalar_curvature"] == 0.0
    assert geometry["riemann_tensor_max_absolute_component"] == 0.0
    assert geometry["nonzero_connection_component_count"] == 4
    assert geometry["curvature_test_claimed"] is False
    assert geometry["covariant_connection_test_claimed"] is True


def test_metric_compatibility_and_flat_limit_are_exact_controls() -> None:
    for time in (0.0, 0.37, 0.91):
        assert metric_compatibility_max_error(
            time=time,
            conformal_rate=0.2,
        ) <= 1e-12
    assert flat_limit_max_discrepancy() <= 1e-12


def test_on_shell_covariant_divergence_converges_second_order() -> None:
    result = build_result()
    on_shell = result["on_shell"]
    assert on_shell["relative_error_against_zero_formed"] is False
    assert len(on_shell["time_slice_results"]) == 12
    assert all(
        row["order"] >= 1.8
        for row in on_shell["combined_absolute_divergence_convergence_orders"][-2:]
    )


def test_off_shell_identity_matches_exact_conformal_residual() -> None:
    result = build_result()
    off_shell = result["off_shell"]
    finest = off_shell["resolution_aggregates"][-1]
    assert off_shell["exact_reference"] == (
        "E_phi = 0.84 * a(eta)^(-2) * phi"
    )
    assert finest["covariant_identity_relative_error_norms"]["combined"] <= 0.02
    assert finest["exact_residual_reference"][
        "computed_coefficient_before_a_inverse_squared"
    ] == pytest.approx(0.84, abs=1e-12)
    assert finest["exact_residual_reference"][
        "field_residual_relative_error_norm"
    ] <= 1e-12
    assert all(
        row["order"] >= 1.8
        for row in off_shell["combined_identity_error_convergence_orders"][-2:]
    )


def test_naive_partial_divergence_is_detected_as_diagnostic_negative_control() -> None:
    result = build_result()
    diagnostic = result["naive_partial_divergence_negative_control"]
    assert diagnostic["failure_detected"] is True
    assert diagnostic["finest_on_shell_naive_to_covariant_error_ratio"] > 100.0
    assert diagnostic["diagnostic_only_not_guardrail_threshold"] is True


def test_all_frozen_guardrail_thresholds_pass() -> None:
    result = build_result()
    assert result["all_thresholds_passed"] is True
    assert all(result["threshold_checks"].values())
    assert result["claim"]["primary_label"] == "E-REPRO"
    assert result["claim"]["claim_status"] == "generated_pending_result_review"
    assert result["claim"]["next_work_status"] == RESULT_REVIEW_TARGET


def test_execution_records_interpretive_and_promotion_boundaries() -> None:
    result = build_result()
    boundary = result["boundary"]
    assert result["equation_compendium_edited"] is False
    assert boundary["background_metric_evolved"] is False
    assert boundary["genuine_nonzero_curvature_test_executed"] is False
    assert boundary["curvature_test_claimed"] is False
    assert boundary["covariant_connection_test_claimed"] is True
    assert boundary["source_admissibility_claimed"] is False
    assert boundary["bianchi_compatibility_claimed"] is False
    assert boundary["qft_gr_seam_admissibility_claimed"] is False
    assert boundary["master_action_promoted"] is False


def test_component_identity_is_evaluated_for_both_indices() -> None:
    row = evaluate_time_slice(resolution=128, time=0.37, omega=2.2)
    assert set(row["covariant_divergence_norms"]) == {
        "nu_eta",
        "nu_x",
        "combined",
    }
    assert row["equation_residual_coefficient_before_a_inverse_squared"] == (
        pytest.approx(0.84, abs=1e-12)
    )


def test_checked_artifacts_match_fresh_canonical_execution(tmp_path: Path) -> None:
    fresh_output = tmp_path / "result.json"
    fresh_manifest = tmp_path / "manifest.json"
    result, manifest = write_artifacts(
        output_path=fresh_output,
        manifest_path=fresh_manifest,
        captured_at_utc=CAPTURED_AT_UTC,
    )
    assert result == json.loads(OUTPUT_PATH.read_text(encoding="utf-8"))
    assert manifest == json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    assert fresh_output.read_bytes() == OUTPUT_PATH.read_bytes()
    assert fresh_manifest.read_bytes() == MANIFEST_PATH.read_bytes()
    assert fresh_output.read_bytes() == canonical_json_bytes(result)
    assert fresh_manifest.read_bytes() == canonical_json_bytes(manifest)


def test_canonical_json_rejects_nan_and_infinity() -> None:
    for nonfinite in (math.nan, math.inf, -math.inf):
        with pytest.raises(ValueError):
            canonical_json_bytes({"value": nonfinite})


def test_resolution_order_and_result_are_deterministic() -> None:
    assert RESOLUTIONS == (64, 128, 256, 512)
    assert canonical_json_bytes(build_result()) == canonical_json_bytes(build_result())
