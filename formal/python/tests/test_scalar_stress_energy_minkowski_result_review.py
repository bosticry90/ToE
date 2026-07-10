from __future__ import annotations

import json
import math
import shutil
from pathlib import Path

import pytest

from formal.python.toe.calculations.calc_scalar_stress_energy_divergence_identity_minkowski import (
    canonical_json_bytes,
)
from formal.python.tests.strict_physics_state_helpers import (
    active_workstream,
    current_target_state,
    loop_registry,
    workstream,
)
from formal.python.tools.scalar_stress_energy_minkowski_reports import (
    CALCULATION_MANIFEST_PATH,
    CALCULATION_OUTPUT_PATH,
    CALCULATION_SCRIPT_PATH,
    CURVED_RETEST_GUARDRAIL_TARGET,
    EXECUTION_REPORT_PATH,
    EXPECTED_EXECUTION_HASHES,
    GUARDRAIL_REPORT_PATH,
    REPRODUCIBILITY_REPAIR_TARGET,
    REPO_ROOT,
    REVIEW_OUTCOME,
    REVIEW_STRICT_OUTCOME,
    build_review_report,
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


def test_review_accepts_exact_artifacts_and_independent_regeneration() -> None:
    verification = verify_calculation_result()
    assert verification["accepted"] is True
    assert verification["mismatch_codes"] == []
    assert verification["expected_hashes"] == EXPECTED_EXECUTION_HASHES
    assert verification["canonical_bytes_match"] is True
    assert verification["independent_in_memory_regeneration_match"] is True
    assert verification["selected_next_target"] == CURVED_RETEST_GUARDRAIL_TARGET


def test_review_accepts_only_level_three_scoped_e_repro() -> None:
    report = build_review_report()
    assert report["packet_result"] == REVIEW_OUTCOME
    assert report["strict_packet_result"] == REVIEW_STRICT_OUTCOME
    assert report["claim"]["primary_label"] == "E-REPRO"
    assert report["claim"]["claim_ceiling_level"] == 3
    assert report["execution_artifacts_modified_by_review"] is False
    assert report["equation_compendium_status"] == (
        "ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO"
    )
    assert len(report["equation_compendium_rows_activated"]) == 2
    assert report["boundary"]["source_admissibility_claimed"] is False
    assert report["boundary"]["qft_gr_seam_admissibility_claimed"] is False


def test_review_is_preserved_after_curved_guardrail_rotation() -> None:
    registry = loop_registry()
    state = current_target_state(registry)
    active = active_workstream(registry)
    review = workstream(
        "review_calc_scalar_stress_energy_divergence_identity_minkowski_v0_result",
        registry,
    )
    assert review["status"] == "paused"
    assert review["selected_next_target"] == CURVED_RETEST_GUARDRAIL_TARGET
    assert state["previous_live_next_target"] == (
        "prepare_scalar_stress_energy_covariant_divergence_identity_higher_"
        "dimensional_curved_background_guardrail_packet"
    )
    assert state["live_next_target"] == (
        "execute_calc_scalar_stress_energy_covariant_divergence_identity_higher_"
        "dimensional_curved_background_v0"
    )
    assert active["workstream_id"] == state["live_next_target"]
    assert active["calculation_executed"] == "no"


def test_successful_review_preserves_the_two_minkowski_equation_surfaces() -> None:
    compendium = (
        REPO_ROOT
        / "formal"
        / "docs"
        / "paper"
        / "TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md"
    ).read_text(encoding="utf-8")
    for equation_id in (
        "EQ-QFT-SCALAR-STRESS-ENERGY-v0",
        "EQ-QFT-SCALAR-STRESS-DIVERGENCE-IDENTITY-v0",
    ):
        assert equation_id in compendium
    assert compendium.count("ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO") == 3


def test_tampered_output_hash_returns_structured_blocker(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    paths["output_path"].write_bytes(paths["output_path"].read_bytes() + b" ")
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert "output_hash_mismatch" in verification["mismatch_codes"]
    assert verification["primary_claim_label"] == "B-BLOCKED"
    assert verification["selected_next_target"] == REPRODUCIBILITY_REPAIR_TARGET


def test_schema_mismatch_is_localized_without_abort(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    del payload["claim"]
    paths["output_path"].write_bytes(canonical_json_bytes(payload))
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert "schema_mismatch" in verification["mismatch_codes"]


def test_count_mismatch_is_localized_without_abort(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    payload["on_shell"]["time_slice_results"].pop()
    paths["output_path"].write_bytes(canonical_json_bytes(payload))
    verification = verify_calculation_result(**paths)
    assert verification["accepted"] is False
    assert "count_mismatch" in verification["mismatch_codes"]


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


def test_noncanonical_pretty_json_is_rejected(tmp_path: Path) -> None:
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
