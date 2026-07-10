from __future__ import annotations

import hashlib
import json

import numpy as np
import pytest

import formal.python.toe.calculations.calc_scalar_stress_energy_covariant_divergence_identity_higher_dimensional_curved_background as calculation


@pytest.fixture(scope="module")
def result() -> dict[str, object]:
    return calculation.build_result()


def test_axis_aware_periodic_difference_on_rectangular_grid() -> None:
    nx = 48
    ny = 80
    dx = 2.0 * np.pi / nx
    dy = 2.0 * np.pi / ny
    x = np.arange(nx)[:, None] * dx
    y = np.arange(ny)[None, :] * dy
    values = np.sin(3.0 * x) * np.cos(5.0 * y)
    derivative_x = calculation.centered_periodic_difference(
        values, dx, axis=0
    )
    derivative_y = calculation.centered_periodic_difference(
        values, dy, axis=1
    )
    assert np.max(np.abs(derivative_x - 3.0 * np.cos(3.0 * x) * np.cos(5.0 * y))) < 0.08
    assert np.max(np.abs(derivative_y + 5.0 * np.sin(3.0 * x) * np.sin(5.0 * y))) < 0.14


def test_generic_curvature_route_and_metric_compatibility() -> None:
    verification = calculation.curvature_verification()
    assert verification["scalar_curvature_minimum"] == pytest.approx(-0.5)
    assert verification["scalar_curvature_maximum"] == pytest.approx(1.0 / 3.0)
    assert verification["peak_absolute_scalar_curvature"] == pytest.approx(0.5)
    assert verification["peak_to_peak_scalar_curvature"] == pytest.approx(5.0 / 6.0)
    assert verification["maximum_curvature_route_absolute_discrepancy"] <= 1e-12
    assert verification["maximum_metric_compatibility_absolute_error"] <= 1e-12
    for row, resolution in zip(
        verification["resolution_diagnostics"], calculation.RESOLUTIONS
    ):
        assert row["excluded_x_index_count"] == 2
        assert row["excluded_x_indices"] == [resolution // 4, 3 * resolution // 4]
        assert row["excluded_spatial_gridpoint_count"] == 2 * resolution
        assert all(
            item["relative_error"] is None
            and item["status"] == "excluded_near_zero"
            for item in row["excluded_crossing_relative_errors"]
        )
        excluded = {
            item["x_index"]: item
            for item in row["x_index_error_rows"]
            if item["status"] == "excluded_near_zero"
        }
        assert sorted(excluded) == [resolution // 4, 3 * resolution // 4]
        assert all(item["relative_error"] is None for item in excluded.values())


def test_generic_curvature_route_does_not_call_analytic_helper(monkeypatch) -> None:
    def forbidden(*args, **kwargs):
        raise AssertionError("analytic curvature helper was called")

    monkeypatch.setattr(calculation, "analytic_scalar_curvature", forbidden)
    reconstructed = calculation.reconstruct_curvature(32)
    assert np.max(np.abs(reconstructed["scalar_curvature"])) >= 0.49


def test_covariant_divergence_route_does_not_call_residual_helper(
    monkeypatch,
) -> None:
    def forbidden(*args, **kwargs):
        raise AssertionError("analytic residual helper was called")

    monkeypatch.setattr(calculation, "_explicit_profile_residual", forbidden)
    arrays = calculation.compute_covariant_divergence_slice(
        resolution=32,
        time=0.37,
        profile_id="off_shell_x_mode",
    )
    assert arrays["divergence"].shape == (3, 32, 32)
    assert np.all(np.isfinite(arrays["divergence"]))


@pytest.mark.parametrize("profile_id", calculation.PROFILE_IDS)
def test_profile_residual_formula_matches_independent_analytic_assembly(
    profile_id: str,
) -> None:
    row = calculation.evaluate_time_slice(
        resolution=64,
        time=0.37,
        profile_id=profile_id,
    )
    assert row["analytic_residual_reference_max_absolute_error"] <= 1e-12
    if profile_id == "on_shell_temporal_mode":
        assert row["identity_metrics"]["combined"][
            "relative_error_applicable"
        ] is False
        assert row["identity_metrics"]["combined"]["relative_error"] is None
        assert row["identity_metrics"]["combined"]["convergence_status"] == (
            "not_applicable_exact_zero"
        )


def test_result_has_exact_rows_aggregates_gates_and_scoped_boundary(result) -> None:
    assert result["profile_time_resolution_row_count"] == 36
    assert len(result["profile_time_resolution_rows"]) == 36
    assert result["profile_resolution_aggregate_count"] == 12
    assert len(result["profile_resolution_aggregates"]) == 12
    assert result["frozen_threshold_count"] == 16
    assert len(result["threshold_checks"]) == 16
    assert [row["decision_number"] for row in result["threshold_decisions"]] == list(
        range(1, 17)
    )
    assert all(result["threshold_checks"].values())
    assert result["all_thresholds_passed"] is True
    assert result["claim"]["primary_label"] == "E-REPRO"
    assert result["claim"]["claim_ceiling_level"] == 3
    assert result["result_review"]["target"] == calculation.RESULT_REVIEW_TARGET
    boundary = result["boundary"]
    assert boundary["spacetime_dimension"] == 3
    assert boundary["two_dimensional_Einstein_degeneracy_not_applicable"] is True
    assert boundary["einstein_tensor_can_be_nonzero"] is True
    assert boundary["background_fixed"] is True
    assert boundary["Einstein_source_tested"] is False
    assert boundary["gravity_evolved"] is False
    assert "two_dimensional_einstein_gravity_degenerate" not in result
    safety = result["geometry_safety_verification"]
    assert safety["minimum_warp_factor"] == pytest.approx(0.8)
    assert safety["maximum_warp_factor"] == pytest.approx(1.2)
    assert safety["maximum_inverse_y_metric_factor"] == pytest.approx(1.5625)
    assert safety["minimum_absolute_determinant"] == pytest.approx(0.64)
    assert safety["all_frozen_grids_nonsingular"] is True


def test_two_finest_orders_and_all_five_controls_pass(result) -> None:
    convergence = result["convergence_diagnostics"]
    assert convergence["off_shell_x_mode"]["combined"][
        "minimum_two_finest_order"
    ] >= 1.8
    assert convergence["off_shell_y_mode"]["combined"][
        "minimum_two_finest_order"
    ] >= 1.8
    for profile_id in ("off_shell_x_mode", "off_shell_y_mode"):
        combined = convergence[profile_id]["combined"]
        assert combined["p_64_128"] == combined["orders"][1]["order"]
        assert combined["p_128_256"] == combined["orders"][2]["order"]
        assert combined["p_min"] == min(
            combined["p_64_128"], combined["p_128_256"]
        )
    assert convergence["on_shell_temporal_mode"]["combined"][
        "convergence_status"
    ] == "not_applicable_exact_zero"
    controls = result["negative_controls"]
    assert controls["record_count"] == 20
    adjudication = controls["finest_resolution_adjudication"]
    assert adjudication["all_five_negative_controls_passed"] is True
    assert sum(
        1
        for key, value in adjudication.items()
        if key != "all_five_negative_controls_passed" and value["pass"]
    ) == 5
    assert all(
        record["resolution_N"] in calculation.RESOLUTIONS
        and "exact_defective_operation" in record
        and "profile_evidence" in record
        for record in controls["records"]
    )


def test_flat_limit_uses_numeric_tolerance_and_exact_operator_metadata(result) -> None:
    flat = result["flat_limit_control"]
    assert flat["maximum_flat_limit_absolute_discrepancy"] <= 1e-11
    assert flat["operator_metadata"] == {
        "coordinate_order": ["t", "x", "y"],
        "operator_coefficients": [-1, 1, 1],
        "connection": 0,
        "curvature": 0,
        "symbolic_metadata_exact": True,
    }
    assert len(flat["rows"]) == 36


def test_result_is_finite_canonical_json_and_contains_no_raw_grids(result) -> None:
    encoded = calculation.canonical_json_bytes(result)
    assert encoded.endswith(b"\n") and not encoded.endswith(b"\n\n")
    assert not encoded.startswith(b"\xef\xbb\xbf")
    decoded = json.loads(encoded)
    assert decoded["method"]["raw_grids_persisted"] is False
    assert b"NaN" not in encoded and b"Infinity" not in encoded


def test_write_artifacts_is_canonical_hash_bound_and_path_independent(
    tmp_path,
) -> None:
    first_output = tmp_path / "one" / "result.json"
    first_manifest = tmp_path / "one" / "manifest.json"
    second_output = tmp_path / "two" / "result.json"
    second_manifest = tmp_path / "two" / "manifest.json"
    first_result, first_binding = calculation.write_artifacts(
        output_path=first_output,
        manifest_path=first_manifest,
    )
    second_output.parent.mkdir(parents=True)
    second_output.write_bytes(calculation.canonical_json_bytes(first_result))
    second_binding = calculation.build_manifest(
        output_path=second_output,
        result=first_result,
    )
    second_manifest.write_bytes(calculation.canonical_json_bytes(second_binding))
    assert first_output.read_bytes() == second_output.read_bytes()
    assert first_manifest.read_bytes() == second_manifest.read_bytes()
    assert first_binding == second_binding
    assert first_output.read_bytes() == calculation.canonical_json_bytes(first_result)
    assert first_binding["output_sha256"] == hashlib.sha256(
        first_output.read_bytes()
    ).hexdigest()
    assert first_binding["guardrail_sha256"] == calculation.sha256_file(
        calculation.REPO_ROOT / calculation.GUARDRAIL_RELATIVE_PATH
    )
    serialized = first_manifest.read_text(encoding="utf-8")
    assert str(tmp_path) not in serialized
    assert first_binding["temporary_output_paths_serialized"] is False
    assert first_binding["environment"]["blas_lapack"]["blas"].keys() == {
        "name",
        "version",
    }


def test_threshold_failure_preserves_artifacts_without_opening_review(
    monkeypatch,
    tmp_path,
) -> None:
    original = calculation._negative_control_records

    def force_control_failure(aggregate_by_key):
        records, adjudication = original(aggregate_by_key)
        adjudication["naive_partial_divergence"]["pass"] = False
        adjudication["all_five_negative_controls_passed"] = False
        return records, adjudication

    monkeypatch.setattr(
        calculation,
        "_negative_control_records",
        force_control_failure,
    )
    result = calculation.build_result()
    assert result["all_thresholds_passed"] is False
    assert result["calculation_status"] == "executed_blocked"
    assert result["claim"]["primary_label"] == "B-BLOCKED"
    assert result["selected_next_target"] == calculation.THRESHOLD_FAILURE_TARGET
    assert result["result_review"] == {
        "status": "not_created_threshold_failure",
        "target": None,
    }

    output = tmp_path / "blocked-result.json"
    output.write_bytes(calculation.canonical_json_bytes(result))
    manifest = calculation.build_manifest(output_path=output, result=result)
    assert manifest["selected_next_target"] == calculation.THRESHOLD_FAILURE_TARGET
    assert manifest["result_review_status"] == "not_created_threshold_failure"
    assert manifest["result_review_target"] is None
