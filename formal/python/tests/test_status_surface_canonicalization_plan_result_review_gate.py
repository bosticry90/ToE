from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)


REPO_ROOT = find_repo_root(Path(__file__))
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "StatusSurfaceCanonicalizationPlanResultReview.lean"
)
PLAN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "StatusSurfaceCanonicalizationPlan.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_REVIEW_20260505_v0.json"
)
PLAN_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "STATUS_SURFACE_CANONICALIZATION_PLAN_20260505_v0.json"
)

REPORT_ID = "STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_REVIEW_20260505_v0"
SURFACE_ID = "status_surface_canonicalization_plan_result_review_v0"
CONSUMED_TARGET = "review_status_surface_canonicalization_plan_result"
CONSUMED_TOKEN = "STATUS_SURFACE_CANONICALIZATION_PLAN_PREPARED"
RESULT_TOKEN = "STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_REVIEW_CONSUMED"
NEXT_TARGET = "select_next_post_status_surface_canonicalization_bounded_attack"
RECOMMENDED_CANDIDATE = (
    "prepare_status_surface_canonicalization_enforcement_packet"
)
CANDIDATE_TARGETS = {
    RECOMMENDED_CANDIDATE,
    "prepare_next_proof_debt_ledger_discharge_item",
    "return_to_full_pillar_target_map_next_lane_selection",
    "prepare_artifact_retention_migration_plan",
    "prepare_qm_stat_theorem_gap_reentry",
    "prepare_sr_cosmo_global_obstruction_followup",
}
EXPECTED_CLASSES = {
    "CANONICAL_CONTROL_SOURCES",
    "PUBLIC_SUMMARY_SURFACES",
    "GENERATED_OUTPUT_SURFACES",
    "HISTORICAL_SUPERSEDED_SURFACES",
}
EXPECTED_RULES = {
    "ONLY_CANONICAL_SURFACES_DETERMINE_LIVE_TARGET_AND_CURRENT_AUTHORITY",
    "PUBLIC_SUMMARIES_MUST_MIRROR_CANONICAL_SURFACES",
    "HISTORICAL_RELEASE_DOCS_ARE_IMMUTABLE_EVIDENCE_NOT_CURRENT_AUTHORITY_UNLESS_REFERENCED_BY_REGISTRY_OR_FRONTIER",
    "NO_STALE_VALIDATION_COUNT_PROMOTION",
    "NO_MANUAL_OVERWRITE_OF_GENERATED_OUTPUTS_DURING_NORMAL_VALIDATION",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_status_surface_result_review_consumes_plan_and_rotates_to_selector() -> None:
    text = _read(REVIEW_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        NEXT_TARGET,
        "StatusSurfaceCanonicalizationPlanResultReviewStatus",
        "statusSurfaceCanonicalizationPlanResultReviewStatusV0",
        "status_surface_canonicalization_plan_result_review_consumes_target_v0",
        "status_surface_canonicalization_plan_result_review_consumes_plan_token_v0",
        "status_surface_canonicalization_plan_result_review_result_token_v0",
        "status_surface_canonicalization_plan_result_review_next_target_v0",
        "status_surface_canonicalization_plan_result_review_planning_consumed_v0",
        "status_surface_canonicalization_plan_result_review_selector_rotation_v0",
    } | CANDIDATE_TARGETS:
        assert token in text

    assert (
        "import ToeFormal.Derivation.StatusSurfaceCanonicalizationPlanResultReview"
        in aggregate_text
    )


def test_status_surface_result_review_preserves_classes_and_rules() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        "status_surface_canonicalization_plan_result_review_canonical_preserved_v0",
        "status_surface_canonicalization_plan_result_review_public_preserved_v0",
        "status_surface_canonicalization_plan_result_review_generated_preserved_v0",
        "status_surface_canonicalization_plan_result_review_historical_preserved_v0",
        "status_surface_canonicalization_plan_result_review_rules_preserved_v0",
        "status_surface_canonicalization_plan_result_review_canonical_authority_v0",
        "status_surface_canonicalization_plan_result_review_public_mirror_v0",
        "status_surface_canonicalization_plan_result_review_no_stale_validation_v0",
        "status_surface_canonicalization_plan_result_review_surface_class_count_v0",
        "status_surface_canonicalization_plan_result_review_drift_rule_count_v0",
    }:
        assert token in text


def test_status_surface_result_review_executes_no_rewrite_or_enforcement() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        "status_surface_canonicalization_plan_result_review_no_rewrite_here_v0",
        "status_surface_canonicalization_plan_result_review_no_generated_mutation_here_v0",
        "status_surface_canonicalization_plan_result_review_no_history_edit_here_v0",
        "status_surface_canonicalization_plan_result_review_no_enforcement_here_v0",
        "broad_status_surface_rewrite_executed_here := False",
        "generated_output_mutation_executed_here := False",
        "historical_packet_edit_executed_here := False",
        "enforcement_packet_executed_here := False",
        "selector_choice_made_here := False",
    }:
        assert token in text


def test_status_surface_result_review_preserves_posture_and_nonclaims() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        "status_surface_canonicalization_plan_result_review_freeze_preserved_v0",
        "status_surface_canonicalization_plan_result_review_read_only_preserved_v0",
        "status_surface_canonicalization_plan_result_review_migration_deferred_v0",
        "status_surface_canonicalization_plan_result_review_selector_candidates_v0",
        "status_surface_canonicalization_plan_result_review_selector_choice_not_made_v0",
        "status_surface_canonicalization_plan_result_review_candidate_count_v0",
        "status_surface_canonicalization_plan_result_review_recommended_candidate_v0",
        "status_surface_canonicalization_plan_result_review_full_pytest_count_v0",
        "status_surface_canonicalization_plan_result_review_full_pytest_skipped_v0",
        "status_surface_canonicalization_plan_result_review_lean_jobs_v0",
        "status_surface_canonicalization_plan_result_review_axiom_count_v0",
        "status_surface_canonicalization_plan_result_review_default_nonalias_absent_v0",
        "status_surface_canonicalization_plan_result_review_sample_rep32_retained_v0",
        "status_surface_canonicalization_plan_result_review_qft_gr_not_authorized_v0",
        "status_surface_canonicalization_plan_result_review_master_action_not_promoted_v0",
        "status_surface_canonicalization_plan_result_review_no_pillar_completion_v0",
        "status_surface_canonicalization_plan_result_review_no_seam_closure_v0",
        "status_surface_canonicalization_plan_result_review_no_phase2_readiness_v0",
        "status_surface_canonicalization_plan_result_review_no_empirical_adequacy_v0",
        "status_surface_canonicalization_plan_result_review_no_canonical_toe_claim_v0",
        "status_surface_canonicalization_plan_result_review_manifest_not_enrolled_v0",
        "lean_build_jobs_confirmed := 7981",
    }:
        assert token in text


def test_status_surface_result_review_report_records_review_and_candidates() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_result_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["review_surface"] == _rel(REVIEW_PATH)
    assert report["source_plan_surface"] == _rel(PLAN_PATH)
    assert report["source_plan_report"] == _rel(PLAN_REPORT_PATH)
    assert report["focused_gate"] == (
        "formal/python/tests/test_status_surface_canonicalization_plan_result_review_gate.py"
    )
    assert report["authorized_effect"] == (
        "CONSUME_STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_AND_ROTATE_TO_SELECTOR"
    )
    assert report["planning_result_consumed_only"] is True
    assert report["selector_choice_made_here"] is False
    assert report["broad_status_surface_rewrite_executed"] is False
    assert report["generated_output_mutation_executed"] is False
    assert report["historical_packet_edit_executed"] is False
    assert report["enforcement_packet_executed"] is False
    assert {
        row["candidate_target"] for row in report["selector_candidates_for_next_packet"]
    } == CANDIDATE_TARGETS
    recommended = [
        row for row in report["selector_candidates_for_next_packet"]
        if row["status"] == "recommended_for_next_selector"
    ]
    assert len(recommended) == 1
    assert recommended[0]["candidate_target"] == RECOMMENDED_CANDIDATE
    assert report["recommended_selector_candidate"] == RECOMMENDED_CANDIDATE
    assert {row["class_id"] for row in report["preserved_surface_classes"]} == (
        EXPECTED_CLASSES
    )
    assert set(report["preserved_drift_prevention_rules"]) == EXPECTED_RULES


def test_status_surface_result_review_report_preserves_boundaries() -> None:
    report = _json(REPORT_PATH)
    checkpoint = report["validation_checkpoint"]
    enforcement = report["preserved_enforcement"]

    assert checkpoint == {
        "full_pytest_passed": 6536,
        "full_pytest_skipped": 230,
        "full_pytest_is_prior_checkpoint_not_fresh_for_this_review": True,
        "ordinary_validation_mode": "read_only_by_default",
        "read_only_proof": "full pytest from clean commit followed by git diff --exit-code",
        "read_only_proof_passed": True,
        "lean_build_target": "ToeFormal",
        "lean_build_jobs": 7981,
        "governance_suite_passed": True,
    }
    assert enforcement["new_large_tracked_snapshots_frozen_by_default"] is True
    assert enforcement["ordinary_validation_mode"] == "read_only_by_default"
    assert enforcement["tracked_generated_output_mutation_forbidden_during_validation"] is True
    assert enforcement["snapshot_migration_or_deletion_deferred_to_future_packet"] is True
    assert enforcement["status_surface_rewrite_deferred_to_future_packet"] is True
    assert enforcement["status_surface_enforcement_deferred_to_future_packet"] is True
    assert report["preserved_posture"]["real_axiom_count"] == 60
    assert report["preserved_posture"]["qft_gr_source_map_closure_authorized"] is False
    assert report["nonclaim_boundaries"] == {
        "selector_choice_made_here": False,
        "broad_status_surface_rewrite_executed": False,
        "generated_output_mutation_executed": False,
        "historical_packet_edit_executed": False,
        "enforcement_packet_executed": False,
        "snapshot_migration_or_deletion_executed": False,
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }
    assert report["next_action_after_review_packet"] == NEXT_TARGET


def test_status_surface_result_review_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_status_surface_canonicalization_plan_result_review_gate.py"
    )
