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
    / "PostArtifactRetentionEnforcementBoundedAttackSelection.lean"
)
RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ArtifactRetentionEnforcementPlanResultReview.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_ARTIFACT_RETENTION_ENFORCEMENT_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
)
RESULT_REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "ARTIFACT_RETENTION_ENFORCEMENT_PLAN_RESULT_REVIEW_20260505_v0.json"
)

REPORT_ID = "POST_ARTIFACT_RETENTION_ENFORCEMENT_BOUNDED_ATTACK_SELECTION_20260505_v0"
SURFACE_ID = "post_artifact_retention_enforcement_bounded_attack_selection_v0"
CONSUMED_TARGET = "select_next_post_artifact_retention_enforcement_bounded_attack"
CONSUMED_TOKEN = "ARTIFACT_RETENTION_ENFORCEMENT_PLAN_RESULT_REVIEW_CONSUMED"
RESULT_TOKEN = "POST_ARTIFACT_RETENTION_ENFORCEMENT_NEXT_ATTACK_SELECTED"
SELECTED_TARGET = "prepare_status_surface_canonicalization_plan"
CANDIDATE_TARGETS = {
    "prepare_artifact_retention_migration_plan",
    "prepare_next_proof_debt_ledger_discharge_item",
    "return_to_full_pillar_target_map_next_lane_selection",
    SELECTED_TARGET,
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_post_artifact_selector_surface_selects_status_surface_plan() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        SELECTED_TARGET,
        "PostArtifactRetentionEnforcementBoundedAttackSelectionStatus",
        "PostArtifactRetentionEnforcementBoundedAttackSelectionDecision",
        "prepareStatusSurfaceCanonicalizationPlan",
        "post_artifact_retention_enforcement_bounded_attack_selection_consumes_live_target_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_consumes_review_token_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_exactly_one_target_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_selected_target_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_decision_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_candidate_count_v0",
    } | CANDIDATE_TARGETS:
        assert token in text

    assert (
        "import ToeFormal.Derivation.PostArtifactRetentionEnforcementBoundedAttackSelection"
        in aggregate_text
    )


def test_post_artifact_selector_preserves_artifact_boundaries() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_artifact_retention_enforcement_bounded_attack_selection_freeze_preserved_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_zones_preserved_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_output_mutation_forbidden_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_large_artifact_justification_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_migration_deferred_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_no_migration_here_v0",
        "snapshot_migration_or_deletion_executed_here := False",
        "artifactRetentionEnforcementPlanResultReviewStatusReadoutV0",
    }:
        assert token in text


def test_post_artifact_selector_records_plan_scope_without_rewrite() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_artifact_retention_enforcement_bounded_attack_selection_status_plan_selected_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_no_surface_rewrite_here_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_canonical_sources_planned_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_public_summaries_planned_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_historical_surfaces_planned_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_drift_gates_planned_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_manual_boundaries_planned_v0",
        "canonicalization_plan_executes_surface_rewrite_here := False",
        "status_surface_canonicalization_plan_selected := True",
    }:
        assert token in text


def test_post_artifact_selector_preserves_checkpoint_and_nonclaims() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_artifact_retention_enforcement_bounded_attack_selection_pytest_read_only_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_diff_proof_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_full_pytest_count_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_full_pytest_skipped_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_lean_jobs_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_axiom_count_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_default_nonalias_absent_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_sample_rep32_retained_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_qft_gr_not_authorized_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_master_action_not_promoted_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_no_pillar_completion_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_no_seam_closure_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_no_phase2_readiness_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_no_empirical_adequacy_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_no_canonical_toe_claim_v0",
        "post_artifact_retention_enforcement_bounded_attack_selection_manifest_not_enrolled_v0",
        "lean_build_jobs_confirmed := 7979",
    }:
        assert token in text


def test_post_artifact_selector_report_records_selection() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_selection_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_result_review_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selected_next_target_kind"] == (
        "status_surface_canonicalization_plan_preparation"
    )
    assert report["selector_surface"] == _rel(SELECTION_PATH)
    assert report["source_result_review_surface"] == _rel(RESULT_REVIEW_PATH)
    assert report["source_result_review_report"] == _rel(RESULT_REVIEW_REPORT_PATH)
    assert report["focused_gate"] == (
        "formal/python/tests/"
        "test_post_artifact_retention_enforcement_bounded_attack_selection_gate.py"
    )
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_TARGET"
    assert report["selection_executes_target"] is False
    assert report["canonicalization_plan_executes_surface_rewrite_here"] is False
    assert report["migration_or_deletion_executed"] is False
    assert report["selection_count"] == 1
    assert report["candidate_target_count"] == 4
    assert {row["target"] for row in report["candidate_targets"]} == CANDIDATE_TARGETS

    selected = [row for row in report["candidate_targets"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["target"] == SELECTED_TARGET
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_post_artifact_selector_report_preserves_boundaries() -> None:
    report = _json(REPORT_PATH)
    checkpoint = report["validation_checkpoint"]
    enforcement = report["preserved_enforcement"]
    plan_scope = report["status_surface_canonicalization_plan_scope"]

    assert checkpoint == {
        "full_pytest_passed": 6536,
        "full_pytest_skipped": 230,
        "full_pytest_is_prior_checkpoint_not_fresh_for_this_selector": True,
        "ordinary_validation_mode": "read_only_by_default",
        "read_only_proof": "full pytest from clean commit followed by git diff --exit-code",
        "read_only_proof_passed": True,
        "lean_build_target": "ToeFormal",
        "lean_build_jobs": 7979,
        "governance_suite_passed": True,
    }
    assert enforcement["new_large_tracked_snapshots_frozen_by_default"] is True
    assert enforcement["tracked_generated_output_mutation_forbidden_during_validation"] is True
    assert enforcement["snapshot_migration_or_deletion_deferred_to_future_packet"] is True
    assert plan_scope["canonical_sources_of_truth_to_be_planned"] is True
    assert plan_scope["generated_public_summary_surfaces_to_be_planned"] is True
    assert plan_scope["historical_superseded_surfaces_to_be_planned"] is True
    assert plan_scope["drift_gates_to_be_planned"] is True
    assert plan_scope["manual_edit_boundaries_to_be_planned"] is True
    assert plan_scope["actual_rewrite_or_generation_change_authorized_here"] is False
    assert report["preserved_posture"]["real_axiom_count"] == 60
    assert report["preserved_posture"]["qft_gr_source_map_closure_authorized"] is False
    assert report["nonclaim_boundaries"] == {
        "snapshot_migration_or_deletion_executed": False,
        "status_surface_rewrite_executed": False,
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }


def test_post_artifact_selector_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_post_artifact_retention_enforcement_bounded_attack_selection_gate.py"
    )
