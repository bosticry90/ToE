from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest

from formal.python.toe.calculations.calc_scalar_stress_energy_covariant_divergence_identity_nonzero_curvature_background import (
    canonical_json_bytes as calculation_canonical_json_bytes,
)
from formal.python.tools.scalar_nonzero_curvature_background_reports import (
    CALCULATION_MANIFEST_PATH,
    CALCULATION_OUTPUT_PATH,
    CALCULATION_SCRIPT_PATH,
    EXECUTION_REPORT_PATH,
    EXPECTED_EXECUTION_HASHES,
    GUARDRAIL_REPORT_PATH,
    HIGHER_DIMENSIONAL_CURVED_BACKGROUND_GUARDRAIL_TARGET,
    REPRODUCIBILITY_REPAIR_TARGET,
    REVIEW_OUTCOME,
    REVIEW_REPORT_PATH,
    REVIEW_STRICT_OUTCOME,
    build_review_report,
    report_json_bytes,
    verify_calculation_result,
)


def _paths() -> dict[str, Path]:
    return {
        "guardrail_path": GUARDRAIL_REPORT_PATH,
        "script_path": CALCULATION_SCRIPT_PATH,
        "output_path": CALCULATION_OUTPUT_PATH,
        "manifest_path": CALCULATION_MANIFEST_PATH,
        "execution_report_path": EXECUTION_REPORT_PATH,
    }


def _copy_artifacts(tmp_path: Path) -> dict[str, Path]:
    copied: dict[str, Path] = {}
    for argument, source in _paths().items():
        target = tmp_path / source.name
        shutil.copyfile(source, target)
        copied[argument] = target
    return copied


def _rewrite_output(path: Path, payload: dict[str, object]) -> None:
    path.write_bytes(calculation_canonical_json_bytes(payload))


def test_review_accepts_all_five_hashes_and_independent_regeneration() -> None:
    verification = verify_calculation_result()
    assert verification["accepted"] is True
    assert verification["mismatch_codes"] == []
    assert verification["expected_hashes"] == EXPECTED_EXECUTION_HASHES
    assert verification["actual_hashes"] == EXPECTED_EXECUTION_HASHES
    assert verification["all_five_execution_artifact_hashes_match"] is True
    assert verification["manifest_hash_links_match"] is True
    assert verification["execution_report_hash_links_match"] is True
    assert verification["canonical_bytes_match"] is True
    assert all(verification["canonical_byte_checks"].values())
    assert verification["independent_in_memory_regeneration_match"] is True
    assert verification["independent_regenerated_output_sha256"] == (
        EXPECTED_EXECUTION_HASHES["output_sha256"]
    )


def test_review_matches_every_time_resolution_row_and_aggregate_bytes() -> None:
    verification = verify_calculation_result()
    assert verification["all_row_and_aggregate_counts_match"] is True
    assert verification["time_resolution_rows_exact_bytes_match"] is True
    assert verification["resolution_aggregates_exact_bytes_match"] is True
    assert verification["per_resolution_results_match"] is True
    assert verification["observed_control_counts"] == (
        verification["expected_control_counts"]
    )
    assert verification["expected_control_counts"] == {
        "time_slice_count": 3,
        "resolution_count": 4,
        "on_shell_time_resolution_rows": 12,
        "off_shell_time_resolution_rows": 12,
        "on_shell_resolution_aggregates": 4,
        "off_shell_resolution_aggregates": 4,
        "curvature_analytic_rows": 3,
        "curvature_component_rows": 3,
        "curvature_omission_rows": 3,
        "curvature_verification_route_count": 2,
        "negative_control_count": 3,
        "frozen_threshold_count": 11,
        "divergence_component_count": 2,
    }
    assert all(
        hashes["observed_sha256"]
        == hashes["independently_regenerated_sha256"]
        for hashes in verification["per_resolution_section_hashes"].values()
    )


def test_review_verifies_thresholds_curvature_controls_patch_and_boundary() -> None:
    verification = verify_calculation_result()
    assert verification["all_eleven_thresholds_match"] is True
    assert len(verification["threshold_checks"]) == 11
    assert all(verification["threshold_checks"].values())
    assert verification["both_curvature_routes_match"] is True
    assert verification["all_three_negative_controls_match"] is True
    assert set(verification["negative_controls"]) == {
        "naive_partial_divergence",
        "inconsistent_frozen_connection",
        "curvature_derivative_omission",
    }
    assert verification["patch_domain_safety_match"] is True
    assert verification["patch_domain_safety"][
        "minimum_one_minus_H_eta_over_domain"
    ] == 0.8
    assert verification["patch_domain_safety"][
        "maximum_scale_factor_over_domain"
    ] == 1.25
    assert verification["patch_domain_safety"][
        "minimum_coordinate_distance_to_patch_singularity_over_domain"
    ] == 4.0
    assert verification["background_geometry_classification_match"] is True
    assert verification["on_shell_absolute_error_policy_match"] is True
    assert verification["on_shell_and_off_shell_controls_match"] is True
    assert verification[
        "two_dimensional_einstein_degeneracy_and_nonclaims_match"
    ] is True


def test_review_accepts_only_level_three_fixed_de_sitter_matter_identity() -> None:
    report = build_review_report()
    assert report["packet_result"] == REVIEW_OUTCOME
    assert report["strict_packet_result"] == REVIEW_STRICT_OUTCOME
    assert report["review_result"] == REVIEW_OUTCOME
    assert report["strict_review_result"] == REVIEW_STRICT_OUTCOME
    assert report["selected_next_target"] == (
        HIGHER_DIMENSIONAL_CURVED_BACKGROUND_GUARDRAIL_TARGET
    )
    assert report["claim"]["primary_label"] == "E-REPRO"
    assert report["claim"]["claim_ceiling_level"] == 3
    assert report["background_geometry"]["scalar_curvature_measured"] == 0.08
    assert report["background_geometry"][
        "genuine_nonzero_curvature_validated"
    ] is True
    assert report["gravity_evolved"] is False
    assert report["einstein_tensor_source_tested"] is False
    assert report["two_dimensional_einstein_gravity_degenerate"] is True
    assert report["execution_artifacts_modified_by_review"] is False
    assert report["equation_surface_upgraded_by_review"] is False
    boundary = report["boundary"]
    assert boundary["einstein_source_tested"] is False
    assert boundary["source_admissibility_claimed"] is False
    assert boundary["bianchi_compatibility_claimed"] is False
    assert boundary["qft_gr_seam_admissibility_claimed"] is False
    assert boundary["qft_gr_seam_closure_claimed"] is False
    assert boundary["master_action_promoted"] is False


def test_review_marks_on_shell_relative_fields_as_non_citable_diagnostics() -> None:
    report = build_review_report()
    note = report["on_shell_error_presentation_note"]
    assert note["relative_error_against_zero_formed"] is False
    assert "do not interpret or cite" in note["serialized_relative_error_fields"]
    assert note["threshold_dependency"] is False
    assert note["review_effect"] == "nonblocking"


def test_release_artifact_matches_deterministic_review_builder_bytes() -> None:
    assert REVIEW_REPORT_PATH.read_bytes() == report_json_bytes(
        build_review_report()
    )


@pytest.mark.parametrize(
    ("argument", "mismatch_code"),
    [
        ("guardrail_path", "guardrail_hash_mismatch"),
        ("script_path", "script_hash_mismatch"),
        ("output_path", "output_hash_mismatch"),
        ("manifest_path", "manifest_hash_mismatch"),
        ("execution_report_path", "execution_report_hash_mismatch"),
    ],
)
def test_each_immutable_artifact_hash_is_enforced(
    tmp_path: Path, argument: str, mismatch_code: str
) -> None:
    paths = _copy_artifacts(tmp_path)
    paths[argument].write_bytes(paths[argument].read_bytes() + b" ")
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert mismatch_code in verification["mismatch_codes"]
    assert verification["primary_claim_label"] == "B-BLOCKED"
    assert verification["selected_next_target"] == REPRODUCIBILITY_REPAIR_TARGET


def test_noncanonical_calculation_output_is_rejected(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    paths["output_path"].write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="",
    )
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert "canonicalization_mismatch" in verification["mismatch_codes"]


def test_schema_mismatch_is_localized_without_abort(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    del payload["claim"]
    _rewrite_output(paths["output_path"], payload)
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert "schema_mismatch" in verification["mismatch_codes"]


def test_row_and_aggregate_mismatch_is_localized(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    payload["on_shell"]["time_slice_results"].pop()
    _rewrite_output(paths["output_path"], payload)
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert "count_mismatch" in verification["mismatch_codes"]
    assert "row_aggregate_mismatch" in verification["mismatch_codes"]


def test_threshold_mismatch_is_localized(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    payload["threshold_checks"][
        "metric_compatibility_error_at_most_1e_12"
    ] = False
    _rewrite_output(paths["output_path"], payload)
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert "threshold_mismatch" in verification["mismatch_codes"]


def test_curvature_route_mismatch_is_localized(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    payload["curvature_verification"]["analytic_conformal_route"]["rows"][0][
        "scalar_curvature"
    ] = 0.0
    _rewrite_output(paths["output_path"], payload)
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert "curvature_route_mismatch" in verification["mismatch_codes"]


def test_negative_control_mismatch_is_localized(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    payload["negative_controls"]["naive_partial_divergence"][
        "failure_detected"
    ] = False
    _rewrite_output(paths["output_path"], payload)
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert "negative_control_mismatch" in verification["mismatch_codes"]


def test_patch_safety_mismatch_is_localized(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    payload["patch_domain_safety"]["strictly_inside_coordinate_patch"] = False
    _rewrite_output(paths["output_path"], payload)
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert "patch_safety_mismatch" in verification["mismatch_codes"]


def test_two_dimensional_degeneracy_nonclaim_mismatch_is_localized(
    tmp_path: Path,
) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    payload["boundary"]["einstein_tensor_source_tested"] = True
    _rewrite_output(paths["output_path"], payload)
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert "boundary_nonclaim_mismatch" in verification["mismatch_codes"]


def test_on_shell_relative_error_policy_mismatch_is_rejected(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    payload["on_shell"]["relative_error_against_zero_formed"] = True
    _rewrite_output(paths["output_path"], payload)
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert "on_shell_error_policy_mismatch" in verification["mismatch_codes"]


@pytest.mark.parametrize("constant", ["NaN", "Infinity", "-Infinity"])
def test_nonfinite_json_is_rejected(tmp_path: Path, constant: str) -> None:
    paths = _copy_artifacts(tmp_path)
    raw = paths["output_path"].read_text(encoding="utf-8")
    paths["output_path"].write_text(
        raw.replace('"amplitude_A":0.2', f'"amplitude_A":{constant}', 1),
        encoding="utf-8",
        newline="",
    )
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert "schema_mismatch" in verification["mismatch_codes"]
