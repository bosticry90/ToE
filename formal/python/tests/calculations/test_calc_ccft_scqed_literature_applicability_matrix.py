from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools.claim_label_policy import validate_release_claim_row
from formal.python.toe.calculations.calc_ccft_scqed_literature_applicability_matrix import (
    CAPTURED_AT_UTC,
    INPUT_RELATIVE_PATH,
    MANIFEST_RELATIVE_PATH,
    OUTPUT_RELATIVE_PATH,
    REPO_ROOT,
    RESULT_REVIEW_TARGET,
    build_result,
    load_and_validate_crosswalk,
    sha256_file,
    write_artifacts,
)


INPUT_PATH = REPO_ROOT / INPUT_RELATIVE_PATH
OUTPUT_PATH = REPO_ROOT / OUTPUT_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_crosswalk_input_is_complete_and_preserves_nonvalidation_statuses() -> None:
    _, rows = load_and_validate_crosswalk(INPUT_PATH)

    assert len(rows) == 48
    assert len({row["literature_review_row_id"] for row in rows}) == 4
    assert len({row["literature_source_locator"] for row in rows}) == 4
    assert len({row["source_candidate_id"] for row in rows}) == 2
    assert len({row["platform_requirement_id"] for row in rows}) == 12
    assert {row["source_validation_status"] for row in rows} == {
        "not_validated"
    }
    assert {row["equation_adoption_status"] for row in rows} == {
        "not_adopted"
    }
    assert {row["tau_baseline_status"] for row in rows} == {"not_computed"}


def test_calculation_result_pins_matrix_status_and_missing_field_counts() -> None:
    result = build_result(INPUT_PATH)

    assert result["matrix_dimensions"] == {
        "total_rows": 48,
        "literature_review_rows": 4,
        "literature_source_locators": 4,
        "source_candidates": 2,
        "platform_requirements": 12,
        "expected_cartesian_rows": 48,
        "complete_cartesian_matrix": True,
        "unique_crosswalk_row_ids": 48,
    }
    assert result["status_distribution"] == {
        "platform_relevant_unvalidated": 12,
        "partially_relevant_unvalidated": 23,
        "unclear_requires_review": 7,
        "blocked_missing_requirement_binding": 2,
        "not_applicable_for_requirement": 4,
    }
    assert result["missing_field_counts"]["missing_variables"] | {
        "occurrence_counts": None
    } == {
        "total_occurrences": 92,
        "rows_with_missing": 40,
        "rows_without_missing": 8,
        "unique_item_count": 23,
        "occurrence_counts": None,
    }
    assert result["missing_field_counts"]["missing_units"] | {
        "occurrence_counts": None
    } == {
        "total_occurrences": 64,
        "rows_with_missing": 32,
        "rows_without_missing": 16,
        "unique_item_count": 16,
        "occurrence_counts": None,
    }
    assert result["missing_field_counts"]["missing_assumptions"] | {
        "occurrence_counts": None
    } == {
        "total_occurrences": 52,
        "rows_with_missing": 48,
        "rows_without_missing": 0,
        "unique_item_count": 13,
        "occurrence_counts": None,
    }


def test_calculation_result_pins_per_source_and_requirement_counts() -> None:
    result = build_result(INPUT_PATH)
    per_source = result["per_source_applicability_counts"]

    assert set(per_source) == {
        "OSD-REPL-CAND-SCHLOSSHAUER-RMP-v0",
        "OSD-TLR-CAND-SCHLOSSHAUER-QUANTUM-DECOHERENCE-v0",
    }
    assert per_source["OSD-REPL-CAND-SCHLOSSHAUER-RMP-v0"]["row_count"] == 24
    assert per_source["OSD-REPL-CAND-SCHLOSSHAUER-RMP-v0"][
        "status_counts"
    ] == {
        "platform_relevant_unvalidated": 6,
        "partially_relevant_unvalidated": 12,
        "unclear_requires_review": 4,
        "blocked_missing_requirement_binding": 0,
        "not_applicable_for_requirement": 2,
    }
    assert per_source["OSD-TLR-CAND-SCHLOSSHAUER-QUANTUM-DECOHERENCE-v0"][
        "status_counts"
    ] == {
        "platform_relevant_unvalidated": 6,
        "partially_relevant_unvalidated": 11,
        "unclear_requires_review": 3,
        "blocked_missing_requirement_binding": 2,
        "not_applicable_for_requirement": 2,
    }

    per_requirement = result["per_requirement_blocker_counts"]
    assert len(per_requirement) == 12
    assert sum(
        row["blocked_missing_requirement_binding_count"]
        for row in per_requirement.values()
    ) == 2
    assert sum(
        row["unclear_requires_review_count"]
        for row in per_requirement.values()
    ) == 7
    assert sum(
        row["not_applicable_classification_count"]
        for row in per_requirement.values()
    ) == 4
    assert per_requirement["SCQED-REQ-DRIVE-READOUT-v0"][
        "blocked_missing_requirement_binding_count"
    ] == 1
    assert per_requirement["SCQED-REQ-TEMPERATURE-DISSIPATION-v0"][
        "blocked_missing_requirement_binding_count"
    ] == 1


def test_e_repro_claim_is_scoped_to_counts_and_keeps_physics_claims_closed() -> None:
    result = build_result(INPUT_PATH)
    claim = result["claim"]

    assert validate_release_claim_row(claim) == []
    assert claim["primary_label"] == "E-REPRO"
    assert claim["claim_status"] == "generated_pending_result_review"
    assert claim["next_work_status"] == RESULT_REVIEW_TARGET
    assert result["classification_semantics"]["input_classifications_modified"] is False
    assert result["classification_semantics"][
        "scores_or_acceptance_thresholds_computed"
    ] is False
    assert result["classification_semantics"][
        "not_applicable_for_requirement"
    ] == "applicability classification only, not source rejection"
    assert result["boundary"] == {
        "calculation_executed": True,
        "source_validated": False,
        "source_adopted": False,
        "source_replaced": False,
        "equation_imported": False,
        "equation_adopted": False,
        "lindblad_or_master_equation_imported": False,
        "tau_baseline_computed": False,
        "tau_candidate_computed": False,
        "r_tau_empirical_value_computed": False,
        "empirical_fit_executed": False,
        "measurement_protocol_defined": False,
        "statistical_validation_performed": False,
        "residual_separation_claimed": False,
        "ccft_validated": False,
        "master_action_promoted": False,
    }


def test_checked_artifacts_match_a_fresh_deterministic_execution(
    tmp_path: Path,
) -> None:
    fresh_output = tmp_path / "result.json"
    fresh_manifest = tmp_path / "manifest.json"
    result, manifest = write_artifacts(
        input_path=INPUT_PATH,
        output_path=fresh_output,
        manifest_path=fresh_manifest,
        captured_at_utc=CAPTURED_AT_UTC,
    )

    assert result == _read_json(OUTPUT_PATH)
    assert manifest == _read_json(MANIFEST_PATH)
    assert fresh_output.read_bytes() == OUTPUT_PATH.read_bytes()
    assert fresh_manifest.read_bytes() == MANIFEST_PATH.read_bytes()
    assert manifest["input_sha256"] == sha256_file(INPUT_PATH)
    assert manifest["output_sha256"] == sha256_file(OUTPUT_PATH)
    assert manifest["captured_at_utc"] == CAPTURED_AT_UTC
    assert manifest["result_review_status"] == "pending"


def test_crosswalk_validation_rejects_incomplete_input(tmp_path: Path) -> None:
    payload = _read_json(INPUT_PATH)
    payload[
        "platform_specific_literature_applicability_crosswalk_rows"
    ].pop()
    invalid_input = tmp_path / "invalid-crosswalk.json"
    invalid_input.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(ValueError, match="expected 48 crosswalk rows"):
        load_and_validate_crosswalk(invalid_input)
