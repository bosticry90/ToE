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
    / "FullPillarTargetMapNextLaneSelectionAfterReadOnlyHygiene.lean"
)
POST_HYGIENE_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostReadOnlyValidationHygieneBoundedAttackSelection.lean"
)
TARGET_MAP_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapRebase.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_READ_ONLY_HYGIENE_20260505_v0.json"
)
POST_HYGIENE_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_READ_ONLY_VALIDATION_HYGIENE_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
)

REPORT_ID = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_READ_ONLY_HYGIENE_20260505_v0"
SURFACE_ID = "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_v0"
CONSUMED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
CONSUMED_TOKEN = "POST_READ_ONLY_VALIDATION_HYGIENE_NEXT_ATTACK_SELECTED"
RESULT_TOKEN = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_READ_ONLY_HYGIENE"
SELECTED_LANE = "ARTIFACT_RETENTION_ENFORCEMENT_PLAN"
SELECTED_TARGET = "prepare_artifact_retention_enforcement_plan"
CANDIDATE_CLASSES = {
    "PROOF_DEBT_LEDGER_DISCHARGE_LANE",
    "ARTIFACT_RETENTION_ENFORCEMENT_PLAN",
    "QM_STAT_THEOREM_GAP_RE_ENTRY_LANE",
    "SR_COSMO_GLOBAL_OBSTRUCTION_FOLLOW_UP",
    "QFT_GR_WITNESS_SEARCH_PLAN",
    "MASTER_ACTION_DEPENDENCY_GAP_REDUCTION_PLAN",
    "STALE_TARGET_SYNCHRONIZATION_SWEEP",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_after_hygiene_full_pillar_selector_selects_artifact_retention() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        SELECTED_LANE,
        SELECTED_TARGET,
        "FullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneStatus",
        "FullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneDecision",
        "selectArtifactRetentionEnforcementPlan",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_consumes_return_target_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_consumes_selector_token_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_rows_evaluated_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_artifact_risk_identified_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_exactly_one_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_result_token_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_selected_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_selected_target_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_candidate_count_v0",
    } | CANDIDATE_CLASSES:
        assert token in text

    assert (
        "import ToeFormal.Derivation.FullPillarTargetMapNextLaneSelectionAfterReadOnlyHygiene"
        in aggregate_text
    )


def test_after_hygiene_full_pillar_selector_preserves_validation_checkpoint() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_validation_checkpoint_preserved_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_pytest_read_only_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_diff_proof_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_governance_suite_checkpoint_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_full_pytest_count_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_full_pytest_skipped_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_lean_jobs_v0",
        "full_pytest_checkpoint_passed_count",
        "full_pytest_checkpoint_skipped_count",
        "lean_build_jobs_confirmed := 7976",
        "latest_validation_posture_preserved",
        "ordinary_pytest_read_only_enforced",
        "read_only_diff_proof_confirmed",
    }:
        assert token in text


def test_after_hygiene_full_pillar_selector_preserves_nonclaims() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_axiom_count_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_default_nonalias_absent_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_sample_rep32_retained_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_qft_gr_source_map_not_authorized_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_does_not_execute_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_proof_debt_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_artifact_retention_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_qm_stat_reentry_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_sr_cosmo_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_qft_gr_witness_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_gap_reduction_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_stale_sync_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_master_action_not_promoted_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_no_pillar_completion_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_no_seam_closure_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_no_phase2_readiness_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_no_empirical_adequacy_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_no_canonical_toe_claim_v0",
        "full_pillar_target_map_next_lane_selection_after_read_only_hygiene_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_after_hygiene_full_pillar_report_records_artifact_retention_lane() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_lane"] == SELECTED_LANE
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selection_surface"] == str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    assert report["post_read_only_selection_surface"] == str(
        POST_HYGIENE_SELECTION_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert report["post_read_only_selection_report"] == str(
        POST_HYGIENE_REPORT_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert report["target_map_surface"] == str(TARGET_MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_LANE"
    assert report["selection_executes_lane"] is False
    assert report["selection_count"] == 1
    assert report["candidate_lane_count"] == 7

    selected = [row for row in report["candidate_classes"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["class_id"] == SELECTED_LANE
    assert selected[0]["candidate_target"] == SELECTED_TARGET
    assert {row["class_id"] for row in report["candidate_classes"]} == CANDIDATE_CLASSES
    assert report["preserved_posture"]["real_axiom_count"] == 60
    assert report["preserved_posture"]["qft_gr_source_map_closure_authorized"] is False
    assert report["nonclaim_boundaries"]["master_action_promotion_authorized"] is False
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_after_hygiene_full_pillar_report_records_validation_checkpoint() -> None:
    report = _json(REPORT_PATH)
    checkpoint = report["validation_checkpoint"]

    assert checkpoint == {
        "full_pytest_passed": 6536,
        "full_pytest_skipped": 230,
        "full_pytest_is_prior_checkpoint_not_fresh_for_this_selector": True,
        "read_only_proof": "full pytest from clean commit followed by git diff --exit-code",
        "read_only_proof_passed": True,
        "lean_build_target": "ToeFormal",
        "lean_build_jobs": 7976,
        "governance_suite_passed": True,
    }


def test_after_hygiene_full_pillar_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_full_pillar_target_map_next_lane_selection_after_read_only_hygiene_gate.py"
    )
