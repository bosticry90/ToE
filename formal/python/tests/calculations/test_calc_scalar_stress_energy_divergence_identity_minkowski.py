from __future__ import annotations

import json
import math
from pathlib import Path

import pytest

from formal.python.toe.calculations.calc_scalar_stress_energy_divergence_identity_minkowski import (
    CAPTURED_AT_UTC,
    EXACT_OFF_SHELL_COEFFICIENT,
    MANIFEST_RELATIVE_PATH,
    OUTPUT_RELATIVE_PATH,
    REPO_ROOT,
    RESOLUTIONS,
    RESULT_REVIEW_TARGET,
    build_result,
    canonical_json_bytes,
    evaluate_time_slice,
    write_artifacts,
)


OUTPUT_PATH = REPO_ROOT / OUTPUT_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH


def test_on_shell_control_uses_absolute_norms_and_converges() -> None:
    result = build_result()
    on_shell = result["on_shell"]
    assert on_shell["relative_error_against_zero_formed"] is False
    assert len(on_shell["time_slice_results"]) == 12
    finest = on_shell["resolution_aggregates"][-1]
    assert set(finest["divergence_norms"]) == {"nu_0", "nu_1", "combined"}
    assert all(
        row["order"] >= 1.8
        for row in on_shell["combined_absolute_divergence_convergence_orders"][-2:]
    )


def test_off_shell_negative_control_matches_identity_and_exact_residual() -> None:
    result = build_result()
    off_shell = result["off_shell"]
    assert off_shell["exact_reference"] == "E_phi = 1.05 * phi"
    finest = off_shell["resolution_aggregates"][-1]
    assert finest["identity_relative_error_norms"]["combined"] <= 0.02
    assert finest["exact_residual_reference"]["computed_coefficient"] == pytest.approx(
        EXACT_OFF_SHELL_COEFFICIENT,
        abs=1e-12,
    )
    assert finest["exact_residual_reference"][
        "field_residual_relative_error_norm"
    ] <= 1e-12
    assert all(
        row["order"] >= 1.8
        for row in off_shell["combined_identity_error_convergence_orders"][-2:]
    )


def test_positive_and_negative_controls_pass_all_frozen_thresholds() -> None:
    result = build_result()
    assert result["all_thresholds_passed"] is True
    assert all(result["threshold_checks"].values())
    assert result["threshold_evidence"][
        "finest_off_to_on_divergence_norm_ratio"
    ] > 100.0
    assert result["claim"]["primary_label"] == "E-REPRO"
    assert result["claim"]["claim_status"] == "generated_pending_result_review"
    assert result["claim"]["next_work_status"] == RESULT_REVIEW_TARGET


def test_component_identity_is_evaluated_for_both_indices() -> None:
    row = evaluate_time_slice(resolution=128, time=0.37, omega=1.1 * math.sqrt(5.0))
    assert set(row["divergence_norms"]) == {"nu_0", "nu_1", "combined"}
    assert set(row["identity_relative_error_norms"]) == {
        "nu_0",
        "nu_1",
        "combined",
    }
    assert row["equation_residual_coefficient"] == pytest.approx(1.05, abs=1e-12)


def test_result_boundaries_and_equation_ids_remain_pending_review() -> None:
    result = build_result()
    boundary = result["boundary"]
    assert result["equation_compendium_edited"] is False
    assert result["proposed_equation_ids_pending_review"] == [
        "EQ-QFT-SCALAR-STRESS-ENERGY-v0",
        "EQ-QFT-SCALAR-STRESS-DIVERGENCE-IDENTITY-v0",
    ]
    assert boundary["gravity_dynamics_executed"] is False
    assert boundary["source_admissibility_claimed"] is False
    assert boundary["bianchi_compatibility_claimed"] is False
    assert boundary["qft_gr_seam_admissibility_claimed"] is False
    assert boundary["master_action_promoted"] is False


def test_checked_artifacts_match_fresh_canonical_execution(tmp_path: Path) -> None:
    fresh_output = tmp_path / "result.json"
    fresh_manifest = tmp_path / "manifest.json"
    result, manifest = write_artifacts(
        output_path=fresh_output,
        manifest_path=fresh_manifest,
        captured_at_utc=CAPTURED_AT_UTC,
    )
    checked_result = json.loads(OUTPUT_PATH.read_text(encoding="utf-8"))
    checked_manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    assert result == checked_result
    assert manifest == checked_manifest
    assert fresh_output.read_bytes() == OUTPUT_PATH.read_bytes()
    assert fresh_manifest.read_bytes() == MANIFEST_PATH.read_bytes()
    assert fresh_output.read_bytes() == canonical_json_bytes(result)
    assert fresh_manifest.read_bytes() == canonical_json_bytes(manifest)


def test_canonical_json_rejects_nan_and_infinity() -> None:
    for nonfinite in (math.nan, math.inf, -math.inf):
        with pytest.raises(ValueError):
            canonical_json_bytes({"value": nonfinite})


def test_resolution_order_is_frozen_and_deterministic() -> None:
    first = canonical_json_bytes(build_result())
    second = canonical_json_bytes(build_result())
    assert RESOLUTIONS == (64, 128, 256, 512)
    assert first == second
