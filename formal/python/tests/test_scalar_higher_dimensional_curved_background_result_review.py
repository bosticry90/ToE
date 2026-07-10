from __future__ import annotations

import copy
import json
import shutil
from pathlib import Path
from typing import Any, Callable

import pytest

from formal.python.tools import scalar_higher_dimensional_curved_background_result_review as review


def _copy_chain(tmp_path: Path) -> dict[str, Path]:
    paths = {
        "guardrail_path": tmp_path / "guardrail.json",
        "script_path": tmp_path / "calculation.py",
        "output_path": tmp_path / "result.json",
        "manifest_path": tmp_path / "manifest.json",
        "execution_report_path": tmp_path / "execution.json",
    }
    sources = {
        "guardrail_path": review.GUARDRAIL_PATH,
        "script_path": review.SCRIPT_PATH,
        "output_path": review.OUTPUT_PATH,
        "manifest_path": review.MANIFEST_PATH,
        "execution_report_path": review.EXECUTION_REPORT_PATH,
    }
    for key, destination in paths.items():
        shutil.copyfile(sources[key], destination)
    return paths


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write(path: Path, payload: dict[str, Any], *, compact: bool) -> None:
    encoder = review.canonical_json_bytes if compact else review.report_json_bytes
    path.write_bytes(encoder(payload))


def test_independent_review_accepts_frozen_chain_and_two_fresh_runs() -> None:
    verification = review.verify_calculation_result()
    assert verification["accepted"] is True
    assert verification["mismatch_codes"] == []
    assert verification["all_five_artifact_hashes_match"] is True
    assert all(verification["independent_section_matches"].values())
    assert verification["execution_self_adjudication_trusted"] is False
    assert verification["all_sixteen_independently_recomputed_thresholds_pass"] is True
    assert verification["all_five_independently_recomputed_negative_controls_pass"] is True
    fresh = verification["fresh_subprocess_reproduction"]
    assert fresh["run_count"] == 2
    assert fresh["distinct_temporary_directories"] is True
    assert fresh["both_runs_byte_identical"] is True
    assert fresh["fresh_runs_match_repository_artifacts"] is True


def test_review_report_is_deterministic_level_3_and_uses_exact_targets() -> None:
    first = review.build_review_report(run_subprocesses=False)
    second = review.build_review_report(run_subprocesses=False)
    assert review.report_json_bytes(first) == review.report_json_bytes(second)
    assert first["verification"]["accepted"] is False
    assert first["selected_next_target"] == review.FAILURE_TARGET
    accepted = review.build_review_report()
    assert accepted["status"] == "accepted_level_3_scoped_e_repro"
    assert accepted["selected_next_target"] == review.SUCCESS_TARGET
    assert accepted["claim"]["claim_ceiling_level"] == 3
    assert accepted["boundary"]["level_4_or_level_5_claimed"] is False
    assert accepted["boundary"]["Einstein_source_tested"] is False


def test_strict_parser_rejects_duplicate_nonfinite_bom_and_noncanonical_bytes(
    tmp_path: Path,
) -> None:
    duplicate = tmp_path / "duplicate.json"
    duplicate.write_bytes(b'{"a":1,"a":2}\n')
    with pytest.raises(review.DuplicateKeyError):
        review.load_strict_json_object(duplicate, style="compact")
    nonfinite = tmp_path / "nonfinite.json"
    nonfinite.write_bytes(b'{"a":NaN}\n')
    with pytest.raises(review.NonFiniteJSONError):
        review.load_strict_json_object(nonfinite, style="compact")
    overflow = tmp_path / "overflow.json"
    overflow.write_bytes(b'{"a":1e999}\n')
    with pytest.raises(review.NonFiniteJSONError):
        review.load_strict_json_object(overflow, style="compact")
    bom = tmp_path / "bom.json"
    bom.write_bytes(b"\xef\xbb\xbf{}\n")
    with pytest.raises(ValueError, match="BOM"):
        review.load_strict_json_object(bom, style="compact")
    noncanonical = tmp_path / "noncanonical.json"
    noncanonical.write_bytes(b'{ "a": 1 }\n')
    with pytest.raises(ValueError, match="canonical"):
        review.load_strict_json_object(noncanonical, style="compact")


@pytest.mark.parametrize(
    ("artifact", "expected_code"),
    [
        ("guardrail_path", "guardrail_hash_mismatch"),
        ("script_path", "calculation_script_hash_mismatch"),
        ("output_path", "calculation_output_hash_mismatch"),
        ("manifest_path", "calculation_manifest_hash_mismatch"),
        ("execution_report_path", "execution_report_hash_mismatch"),
    ],
)
def test_each_artifact_hash_is_individually_tamper_evident(
    tmp_path: Path, artifact: str, expected_code: str
) -> None:
    paths = _copy_chain(tmp_path)
    paths[artifact].write_bytes(paths[artifact].read_bytes() + b"tamper")
    verification = review.verify_calculation_result(
        **paths, run_subprocesses=False
    )
    assert verification["accepted"] is False
    assert expected_code in verification["mismatch_codes"]


def _remove_schema_field(payload: dict[str, Any]) -> None:
    payload.pop("question")


def _alter_row(payload: dict[str, Any]) -> None:
    payload["profile_time_resolution_rows"][0]["identity_metrics"]["combined"][
        "absolute_error_rms"
    ] = 0.25


def _alter_aggregate(payload: dict[str, Any]) -> None:
    payload["profile_resolution_aggregates"][0]["identity_metrics"]["combined"][
        "absolute_error_rms"
    ] = 0.25


def _alter_row_count(payload: dict[str, Any]) -> None:
    payload["profile_time_resolution_row_count"] = 35


def _alter_aggregate_count(payload: dict[str, Any]) -> None:
    payload["profile_resolution_aggregate_count"] = 11


def _alter_threshold(payload: dict[str, Any]) -> None:
    payload["thresholds"]["minimum_two_finest_x_mode_convergence_order"] = 0.0


def _alter_threshold_result(payload: dict[str, Any]) -> None:
    payload["threshold_checks"]["minimum_two_finest_x_mode_convergence_order"] = False


def _alter_control(payload: dict[str, Any]) -> None:
    payload["negative_controls"]["records"][-1]["comparison_value"] = 0.0


def _mask_combined_controls(payload: dict[str, Any]) -> None:
    adjudication = payload["negative_controls"]["finest_resolution_adjudication"]
    adjudication["naive_partial_divergence"]["pass"] = False
    assert adjudication["all_five_negative_controls_passed"] is True


def _alter_control_record_count(payload: dict[str, Any]) -> None:
    payload["negative_controls"]["record_count"] = 19


def _alter_exclusion_count(payload: dict[str, Any]) -> None:
    payload["geometry_verification"]["resolution_diagnostics"][0][
        "excluded_spatial_gridpoint_count"
    ] = 2


def _alter_curvature_cutoff(payload: dict[str, Any]) -> None:
    payload["geometry_verification"]["resolution_diagnostics"][0][
        "relative_error_cutoff_epsilon_R"
    ] = 1e-6


def _alter_flat_limit(payload: dict[str, Any]) -> None:
    payload["flat_limit_control"]["operator_metadata"]["operator_coefficients"] = [
        1,
        1,
        1,
    ]


def _fake_zero_convergence(payload: dict[str, Any]) -> None:
    payload["convergence_diagnostics"]["on_shell_temporal_mode"]["combined"][
        "p_min"
    ] = 2.0


def _alter_residual_sign(payload: dict[str, Any]) -> None:
    payload["analytic_profile_references"]["off_shell_x_mode"] = (
        "E_phi=(omega_x^2-m^2-k^2)*phi_x+"
        "A*k*(f'/f)*cos(omega_x*t)*sin(k*x)"
    )


def _import_1plus1_field(payload: dict[str, Any]) -> None:
    payload["boundary"]["two_dimensional_einstein_gravity_degenerate"] = True


def _promote_forbidden_claim(payload: dict[str, Any]) -> None:
    payload["boundary"]["level_4_or_level_5_claimed"] = True


@pytest.mark.parametrize(
    ("mutator", "expected_code"),
    [
        (_remove_schema_field, "schema_or_required_field_mismatch"),
        (_alter_row, "profile_time_row_mismatch"),
        (_alter_aggregate, "space_time_aggregate_mismatch"),
        (_alter_row_count, "profile_time_row_mismatch"),
        (_alter_aggregate_count, "space_time_aggregate_mismatch"),
        (_alter_threshold, "sixteen_threshold_decision_mismatch"),
        (_alter_threshold_result, "sixteen_threshold_decision_mismatch"),
        (_alter_control, "negative_control_or_combined_masking_mismatch"),
        (_mask_combined_controls, "negative_control_or_combined_masking_mismatch"),
        (_alter_control_record_count, "negative_control_or_combined_masking_mismatch"),
        (_alter_exclusion_count, "curvature_or_zero_exclusion_mismatch"),
        (_alter_curvature_cutoff, "curvature_or_zero_exclusion_mismatch"),
        (_alter_flat_limit, "flat_limit_evidence_mismatch"),
        (_fake_zero_convergence, "convergence_or_exact_zero_policy_mismatch"),
        (_alter_residual_sign, "analytic_residual_sign_or_formula_mismatch"),
        (_import_1plus1_field, "claim_boundary_or_1plus1_degeneracy_mismatch"),
        (_promote_forbidden_claim, "claim_boundary_or_1plus1_degeneracy_mismatch"),
    ],
)
def test_result_tamper_matrix_is_semantically_adjudicated(
    tmp_path: Path,
    mutator: Callable[[dict[str, Any]], None],
    expected_code: str,
) -> None:
    paths = _copy_chain(tmp_path)
    payload = _load(paths["output_path"])
    mutator(payload)
    _write(paths["output_path"], payload, compact=True)
    verification = review.verify_calculation_result(
        **paths, run_subprocesses=False
    )
    assert verification["accepted"] is False
    assert expected_code in verification["mismatch_codes"]


def test_execution_report_cannot_mask_failed_control_or_promote_claim(
    tmp_path: Path,
) -> None:
    paths = _copy_chain(tmp_path)
    payload = _load(paths["execution_report_path"])
    adjudication = payload["negative_controls"]["finest_resolution_adjudication"]
    adjudication["naive_partial_divergence"]["pass"] = False
    assert adjudication["all_five_negative_controls_passed"] is True
    payload["control_counts"]["negative_control_record_count"] = 19
    payload["claim"]["claim_ceiling_level"] = 4
    _write(paths["execution_report_path"], payload, compact=False)
    verification = review.verify_calculation_result(
        **paths, run_subprocesses=False
    )
    assert "negative_control_or_combined_masking_mismatch" in verification["mismatch_codes"]
    assert "claim_boundary_or_1plus1_degeneracy_mismatch" in verification["mismatch_codes"]


def test_execution_report_control_counts_are_frozen(tmp_path: Path) -> None:
    paths = _copy_chain(tmp_path)
    payload = _load(paths["execution_report_path"])
    payload["control_counts"]["negative_control_record_count"] = 19
    _write(paths["execution_report_path"], payload, compact=False)
    verification = review.verify_calculation_result(
        **paths, run_subprocesses=False
    )
    assert "schema_or_required_field_mismatch" in verification["mismatch_codes"]


def test_verifier_reports_duplicate_and_nonfinite_artifact_codes(tmp_path: Path) -> None:
    paths = _copy_chain(tmp_path)
    raw = paths["output_path"].read_text(encoding="utf-8")
    paths["output_path"].write_text(
        raw.replace('{"all_thresholds_passed":true', '{"all_thresholds_passed":true,"all_thresholds_passed":true', 1),
        encoding="utf-8",
        newline="\n",
    )
    duplicate = review.verify_calculation_result(**paths, run_subprocesses=False)
    assert "duplicate_json_key" in duplicate["mismatch_codes"]
    paths = _copy_chain(tmp_path)
    raw = paths["output_path"].read_text(encoding="utf-8")
    paths["output_path"].write_text(
        raw.replace('"amplitude_A":0.2', '"amplitude_A":NaN', 1),
        encoding="utf-8",
        newline="\n",
    )
    nonfinite = review.verify_calculation_result(**paths, run_subprocesses=False)
    assert "nonfinite_json_value" in nonfinite["mismatch_codes"]


@pytest.mark.parametrize(
    ("artifact", "field", "compact"),
    [
        ("guardrail_path", "question", False),
        ("manifest_path", "test_path", True),
        ("execution_report_path", "control_counts", False),
    ],
)
def test_each_json_artifact_schema_rejects_missing_required_fields(
    tmp_path: Path,
    artifact: str,
    field: str,
    compact: bool,
) -> None:
    paths = _copy_chain(tmp_path)
    payload = _load(paths[artifact])
    payload.pop(field)
    _write(paths[artifact], payload, compact=compact)
    verification = review.verify_calculation_result(
        **paths, run_subprocesses=False
    )
    assert "schema_or_required_field_mismatch" in verification["mismatch_codes"]


@pytest.mark.parametrize(
    "forbidden_field",
    [
        "gravity_evolved",
        "background_metric_evolved",
        "einstein_equation_solved",
        "Einstein_source_tested",
        "source_admissibility_claimed",
        "bianchi_compatibility_claimed",
        "qft_gr_seam_admissibility_claimed",
        "qft_gr_seam_closure_claimed",
        "quantum_or_renormalized_stress_energy_claimed",
        "multi_background_robustness_claimed",
        "level_4_or_level_5_claimed",
        "ccft_resumed",
        "master_action_promoted",
    ],
)
def test_every_forbidden_promotion_is_rejected(
    tmp_path: Path,
    forbidden_field: str,
) -> None:
    paths = _copy_chain(tmp_path)
    for artifact, compact in (
        ("output_path", True),
        ("manifest_path", True),
        ("execution_report_path", False),
    ):
        payload = _load(paths[artifact])
        payload["boundary"][forbidden_field] = True
        _write(paths[artifact], payload, compact=compact)
    verification = review.verify_calculation_result(
        **paths, run_subprocesses=False
    )
    assert (
        "claim_boundary_or_1plus1_degeneracy_mismatch"
        in verification["mismatch_codes"]
    )


def test_cli_wrapper_is_exact_and_blocking_target_is_frozen() -> None:
    assert review.FAILURE_TARGET == (
        "diagnose_calc_scalar_stress_energy_covariant_divergence_identity_higher_"
        "dimensional_curved_background_v0_reproducibility_mismatch"
    )
    assert review.EXPECTED_EXECUTION_HASHES == {
        "guardrail_sha256": "e6ce9dfb08364e3fa3a0a3895a3d1b16635348ab2fc7b0490f0b3b6e04db6b96",
        "script_sha256": "5d43b770a47ec86ccf8a0e09a68d4c1aebf454daea9c471434d288700f57de53",
        "output_sha256": "755e39e4672ad68e2fbf142d0e2bc9140abb80988e4a330ec3a5fd4ddca859ce",
        "manifest_sha256": "12791f7844d1c48ea81c647e5d8ee65e32b264592b0101eed875afc7a9d8e5f3",
        "execution_report_sha256": "e502995f084bb9d7cdcce8141f7c54fce60026660a3c94f393cf2633f0f22dd2",
    }
