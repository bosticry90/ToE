from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest

from formal.python.tools.post_phi_transport_ccft_chain_reports import (
    CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_RESULT_REVIEW_EXPECTED_HASHES,
    CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_RESULT_REVIEW_MISSING_COUNTS,
    CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_RESULT_REVIEW_STATUS_COUNTS,
    CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_SPRINT_GUARDRAIL_INPUT,
    CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_SPRINT_GUARDRAIL_MANIFEST,
    CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_SPRINT_GUARDRAIL_OUTPUT,
    CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_SPRINT_GUARDRAIL_SCRIPT,
    CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_RESULT_REVIEW_EXECUTION_REPORT,
    REPO_ROOT,
    _canonical_ccft_matrix_v0_bytes,
    build_stage_payload,
    verify_ccft_scqed_literature_applicability_matrix_v0,
)


def _paths() -> dict[str, Path]:
    return {
        "input_path": REPO_ROOT
        / CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_SPRINT_GUARDRAIL_INPUT,
        "script_path": REPO_ROOT
        / CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_SPRINT_GUARDRAIL_SCRIPT,
        "output_path": REPO_ROOT
        / CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_SPRINT_GUARDRAIL_OUTPUT,
        "manifest_path": REPO_ROOT
        / CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_SPRINT_GUARDRAIL_MANIFEST,
        "execution_report_path": REPO_ROOT
        / CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_RESULT_REVIEW_EXECUTION_REPORT,
    }


def _copy_artifacts(tmp_path: Path) -> dict[str, Path]:
    copied: dict[str, Path] = {}
    for argument, source in _paths().items():
        target = tmp_path / source.name
        shutil.copyfile(source, target)
        copied[argument] = target
    return copied


def test_review_accepts_exact_immutable_artifacts() -> None:
    verification = verify_ccft_scqed_literature_applicability_matrix_v0()
    assert verification["accepted"] is True
    assert verification["mismatch_codes"] == []
    assert verification["expected_hashes"] == (
        CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_RESULT_REVIEW_EXPECTED_HASHES
    )
    assert verification["status_counts"] == (
        CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_RESULT_REVIEW_STATUS_COUNTS
    )
    assert verification["missing_field_occurrences"] == (
        CCFT_SCQED_LITERATURE_APPLICABILITY_MATRIX_CALCULATION_RESULT_REVIEW_MISSING_COUNTS
    )
    assert verification["canonical_bytes_match"] is True
    assert verification["independent_in_memory_rebuild_match"] is True


def test_review_payload_accepts_only_scoped_e_repro() -> None:
    payload = build_stage_payload(
        "ccft_scqed_literature_applicability_matrix_calculation_result_review"
    )
    assert payload["accepted"] is True
    assert payload["e_repro_claim_status"] == (
        "accepted_scoped_matrix_counts_only"
    )
    assert payload["ccft_empirical_lane_status"] == (
        "paused_upstream_prerequisites"
    )
    assert payload["selected_next_target"] == (
        "prepare_science_first_pillar_seam_dependency_rebase_packet"
    )
    assert payload["lean_status_wording"] == (
        "scoped Lean passed; full ToeFormal aggregate not run / not upgraded"
    )
    assert payload["full_toeformal_aggregate_status"] == "NOT_RUN_NOT_UPGRADED"
    assert payload["source_validated"] is False
    assert payload["equation_adopted"] is False
    assert payload["tau_baseline_value_computed"] is False
    assert payload["CCFT_validated"] is False
    assert payload["master_action_promoted"] is False


def test_tampered_input_returns_structured_hash_mismatch(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    paths["input_path"].write_bytes(paths["input_path"].read_bytes() + b" ")
    verification = verify_ccft_scqed_literature_applicability_matrix_v0(**paths)
    assert verification["accepted"] is False
    assert "input_hash_mismatch" in verification["mismatch_codes"]
    assert verification["primary_claim_label"] == "B-BLOCKED"
    assert verification["selected_next_target"].startswith("repair_calc_")


def test_schema_mismatch_is_returned_without_abort(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    del payload["claim"]
    paths["output_path"].write_bytes(_canonical_ccft_matrix_v0_bytes(payload))
    verification = verify_ccft_scqed_literature_applicability_matrix_v0(**paths)
    assert verification["accepted"] is False
    assert "schema_mismatch" in verification["mismatch_codes"]


def test_count_mismatch_is_returned_without_abort(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    payload["status_distribution"]["platform_relevant_unvalidated"] = 11
    paths["output_path"].write_bytes(_canonical_ccft_matrix_v0_bytes(payload))
    verification = verify_ccft_scqed_literature_applicability_matrix_v0(**paths)
    assert verification["accepted"] is False
    assert "count_mismatch" in verification["mismatch_codes"]


@pytest.mark.parametrize("constant", ["NaN", "Infinity", "-Infinity"])
def test_nonfinite_json_is_rejected(tmp_path: Path, constant: str) -> None:
    paths = _copy_artifacts(tmp_path)
    raw = paths["output_path"].read_text(encoding="utf-8")
    paths["output_path"].write_text(
        raw.replace('"total_rows": 48', f'"total_rows": {constant}', 1),
        encoding="utf-8",
        newline="",
    )
    verification = verify_ccft_scqed_literature_applicability_matrix_v0(**paths)
    assert verification["accepted"] is False
    assert "schema_mismatch" in verification["mismatch_codes"]


def test_lf_bytes_fail_frozen_v0_canonical_contract(tmp_path: Path) -> None:
    paths = _copy_artifacts(tmp_path)
    payload = json.loads(paths["output_path"].read_text(encoding="utf-8"))
    lf_bytes = (
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")
    paths["output_path"].write_bytes(lf_bytes)
    verification = verify_ccft_scqed_literature_applicability_matrix_v0(**paths)
    assert verification["accepted"] is False
    assert "canonicalization_mismatch" in verification["mismatch_codes"]
