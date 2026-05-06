from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)


REPO_ROOT = find_repo_root(Path(__file__))
SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostReadOnlyValidationHygieneBoundedAttackSelection.lean"
)
HYGIENE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ReadOnlyValidationHygiene.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_READ_ONLY_VALIDATION_HYGIENE_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
)
HYGIENE_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "READ_ONLY_VALIDATION_HYGIENE_20260505_v0.json"
)

REPORT_ID = "POST_READ_ONLY_VALIDATION_HYGIENE_BOUNDED_ATTACK_SELECTION_20260505_v0"
SURFACE_ID = "post_read_only_validation_hygiene_bounded_attack_selection_v0"
CONSUMED_TARGET = "review_read_only_validation_hygiene_result"
CONSUMED_HYGIENE_TOKEN = "READ_ONLY_VALIDATION_HYGIENE_ENFORCED"
RESULT_TOKEN = "POST_READ_ONLY_VALIDATION_HYGIENE_NEXT_ATTACK_SELECTED"
SELECTED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
CANDIDATE_TARGETS = {
    "return_to_full_pillar_target_map_next_lane_selection",
    "prepare_next_proof_debt_ledger_discharge_item",
    "prepare_artifact_retention_enforcement_plan",
    "prepare_qm_stat_theorem_gap_reentry",
    "prepare_sr_cosmo_global_obstruction_followup",
    "prepare_qft_gr_witness_search_plan",
    "prepare_master_action_dependency_gap_reduction_plan",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_post_hygiene_selector_surface_selects_full_pillar_return() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_HYGIENE_TOKEN,
        RESULT_TOKEN,
        SELECTED_TARGET,
        "PostReadOnlyValidationHygieneBoundedAttackSelectionStatus",
        "PostReadOnlyValidationHygieneBoundedAttackSelectionDecision",
        "returnToFullPillarTargetMapNextLaneSelection",
        "post_read_only_validation_hygiene_bounded_attack_selection_consumes_live_target_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_consumes_hygiene_token_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_exactly_one_target_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_selected_target_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_candidate_count_v0",
    } | CANDIDATE_TARGETS:
        assert token in text

    assert (
        "import ToeFormal.Derivation.PostReadOnlyValidationHygieneBoundedAttackSelection"
        in aggregate_text
    )


def test_post_hygiene_selector_surface_preserves_validation_proof() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_read_only_validation_hygiene_bounded_attack_selection_pytest_read_only_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_diff_proof_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_governance_suite_passed_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_full_pytest_count_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_full_pytest_skipped_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_lean_jobs_v0",
        "full_pytest_passed_count := 6536",
        "full_pytest_skipped_count := 230",
        "lean_build_jobs_confirmed := 7975",
        "ordinary_pytest_read_only_enforced",
        "read_only_diff_proof_confirmed",
    }:
        assert token in text


def test_post_hygiene_selector_surface_preserves_posture_and_nonclaims() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_read_only_validation_hygiene_bounded_attack_selection_artifact_policy_recorded_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_authoritative_surface_index_recorded_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_axiom_count_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_default_nonalias_absent_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_sample_rep32_retained_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_qft_gr_source_map_not_authorized_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_does_not_execute_target_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_proof_debt_not_selected_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_artifact_retention_not_selected_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_qm_stat_reentry_not_selected_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_sr_cosmo_not_selected_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_qft_gr_witness_not_selected_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_master_action_gap_not_selected_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_master_action_not_promoted_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_no_pillar_completion_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_no_seam_closure_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_no_phase2_readiness_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_no_empirical_adequacy_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_no_canonical_toe_claim_v0",
        "post_read_only_validation_hygiene_bounded_attack_selection_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_post_hygiene_selection_report_records_full_pillar_return() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_selection_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_hygiene_token"] == CONSUMED_HYGIENE_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selector_surface"] == str(SELECTION_PATH.relative_to(REPO_ROOT)).replace(
        "\\", "/"
    )
    assert report["source_hygiene_surface"] == str(
        HYGIENE_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert report["source_hygiene_report"] == str(
        HYGIENE_REPORT_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_TARGET"
    assert report["selection_executes_target"] is False
    assert report["selection_count"] == 1
    assert report["candidate_target_count"] == 7

    selected = [row for row in report["candidate_targets"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["target"] == SELECTED_TARGET
    assert {row["target"] for row in report["candidate_targets"]} == CANDIDATE_TARGETS
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_post_hygiene_selection_report_records_validation_checkpoint() -> None:
    report = _json(REPORT_PATH)
    checkpoint = report["validation_checkpoint"]

    assert checkpoint == {
        "full_pytest_passed": 6536,
        "full_pytest_skipped": 230,
        "read_only_proof": "full pytest from clean commit followed by git diff --exit-code",
        "read_only_proof_passed": True,
        "lean_build_target": "ToeFormal",
        "lean_build_jobs": 7975,
        "governance_suite_passed": True,
    }
    assert report["preserved_posture"]["real_axiom_count"] == 60
    assert report["preserved_posture"]["qft_gr_source_map_closure_authorized"] is False
    assert report["nonclaim_boundaries"]["master_action_promotion_authorized"] is False


def test_post_hygiene_selector_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_post_read_only_validation_hygiene_bounded_attack_selection_gate.py"
    )
