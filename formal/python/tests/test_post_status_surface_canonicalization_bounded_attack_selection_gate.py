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
    / "PostStatusSurfaceCanonicalizationBoundedAttackSelection.lean"
)
RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "StatusSurfaceCanonicalizationPlanResultReview.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_STATUS_SURFACE_CANONICALIZATION_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
)
RESULT_REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_REVIEW_20260505_v0.json"
)

REPORT_ID = (
    "POST_STATUS_SURFACE_CANONICALIZATION_BOUNDED_ATTACK_SELECTION_20260505_v0"
)
SURFACE_ID = "post_status_surface_canonicalization_bounded_attack_selection_v0"
CONSUMED_TARGET = "select_next_post_status_surface_canonicalization_bounded_attack"
CONSUMED_TOKEN = "STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_REVIEW_CONSUMED"
RESULT_TOKEN = "POST_STATUS_SURFACE_CANONICALIZATION_NEXT_ATTACK_SELECTED"
SELECTED_TARGET = "prepare_status_surface_canonicalization_enforcement_packet"
CANDIDATE_TARGETS = {
    SELECTED_TARGET,
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


def test_post_status_selector_surface_selects_enforcement_packet() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        SELECTED_TARGET,
        "PostStatusSurfaceCanonicalizationBoundedAttackSelectionStatus",
        "PostStatusSurfaceCanonicalizationBoundedAttackSelectionDecision",
        "prepareStatusSurfaceCanonicalizationEnforcementPacket",
        "post_status_surface_canonicalization_bounded_attack_selection_consumes_live_target_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_consumes_review_token_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_result_token_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_exactly_one_target_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_selected_target_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_decision_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_candidate_count_v0",
    } | CANDIDATE_TARGETS:
        assert token in text

    assert (
        "import ToeFormal.Derivation.PostStatusSurfaceCanonicalizationBoundedAttackSelection"
        in aggregate_text
    )


def test_post_status_selector_preserves_status_surface_policy() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_status_surface_canonicalization_bounded_attack_selection_canonical_preserved_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_public_preserved_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_generated_preserved_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_historical_preserved_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_rules_preserved_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_canonical_hierarchy_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_public_mirror_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_no_stale_validation_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_read_only_preserved_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_freeze_preserved_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_migration_deferred_v0",
        "statusSurfaceCanonicalizationPlanResultReviewStatusReadoutV0",
    }:
        assert token in text


def test_post_status_selector_executes_no_enforcement_or_rewrite() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_status_surface_canonicalization_bounded_attack_selection_enforcement_packet_selected_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_does_not_execute_target_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_no_enforcement_here_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_no_surface_rewrite_here_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_no_generated_mutation_here_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_no_history_edit_here_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_no_snapshot_migration_here_v0",
        "selection_executes_target := False",
        "enforcement_packet_executed_here := False",
        "broad_status_surface_rewrite_executed_here := False",
        "generated_output_mutation_executed_here := False",
        "historical_packet_edit_executed_here := False",
        "snapshot_migration_or_deletion_executed_here := False",
    }:
        assert token in text


def test_post_status_selector_preserves_checkpoint_and_nonclaims() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_status_surface_canonicalization_bounded_attack_selection_full_pytest_count_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_full_pytest_skipped_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_lean_jobs_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_axiom_count_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_default_nonalias_absent_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_sample_rep32_retained_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_qft_gr_not_authorized_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_master_action_not_promoted_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_no_pillar_completion_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_no_seam_closure_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_no_phase2_readiness_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_no_empirical_adequacy_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_no_canonical_toe_claim_v0",
        "post_status_surface_canonicalization_bounded_attack_selection_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_post_status_selector_report_records_selection() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_selection_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_result_review_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selected_next_target_kind"] == (
        "status_surface_canonicalization_enforcement_packet_preparation"
    )
    assert report["selector_surface"] == _rel(SELECTION_PATH)
    assert report["source_result_review_surface"] == _rel(RESULT_REVIEW_PATH)
    assert report["source_result_review_report"] == _rel(RESULT_REVIEW_REPORT_PATH)
    assert report["focused_gate"] == (
        "formal/python/tests/"
        "test_post_status_surface_canonicalization_bounded_attack_selection_gate.py"
    )
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_TARGET"
    assert report["selection_executes_target"] is False
    assert report["enforcement_packet_executed"] is False
    assert report["broad_status_surface_rewrite_executed"] is False
    assert report["generated_output_mutation_executed"] is False
    assert report["historical_packet_edit_executed"] is False
    assert report["snapshot_migration_or_deletion_executed"] is False
    assert report["selection_count"] == 1
    assert report["candidate_target_count"] == 6
    assert {row["target"] for row in report["candidate_targets"]} == (
        CANDIDATE_TARGETS
    )

    selected = [row for row in report["candidate_targets"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["target"] == SELECTED_TARGET
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_post_status_selector_report_preserves_boundaries() -> None:
    report = _json(REPORT_PATH)
    checkpoint = report["validation_checkpoint"]
    enforcement = report["preserved_enforcement"]
    future_scope = report["future_enforcement_packet_scope"]

    assert checkpoint == {
        "full_pytest_passed": 6536,
        "full_pytest_skipped": 230,
        "full_pytest_is_prior_checkpoint_not_fresh_for_this_selector": True,
        "ordinary_validation_mode": "read_only_by_default",
        "read_only_proof": "full pytest from clean commit followed by git diff --exit-code",
        "read_only_proof_passed": True,
        "lean_build_target": "ToeFormal",
        "lean_build_jobs": 7981,
        "governance_suite_passed": True,
    }
    assert enforcement["canonical_source_hierarchy_preserved"] is True
    assert enforcement["public_summary_mirror_rules_preserved"] is True
    assert enforcement["tracked_generated_output_mutation_forbidden_during_validation"] is True
    assert enforcement["historical_packets_remain_immutable"] is True
    assert enforcement["artifact_migration_or_deletion_deferred_to_future_packet"] is True
    assert enforcement["status_surface_enforcement_deferred_to_future_packet"] is True
    assert future_scope["canonical_source_hierarchy_to_be_enforced"] is True
    assert future_scope["public_summary_mirror_checks_to_be_enforced"] is True
    assert future_scope["historical_packet_immutability_to_be_enforced"] is True
    assert future_scope["generated_output_read_only_rules_to_be_enforced"] is True
    assert future_scope["broad_status_surface_rewrite_authorized_here"] is False
    assert future_scope["generated_output_mutation_authorized_here"] is False
    assert {row["class_id"] for row in report["preserved_surface_classes"]} == (
        EXPECTED_CLASSES
    )
    assert set(report["preserved_drift_prevention_rules"]) == EXPECTED_RULES
    assert report["preserved_posture"]["real_axiom_count"] == 60
    assert report["preserved_posture"]["qft_gr_source_map_closure_authorized"] is False
    assert report["nonclaim_boundaries"] == {
        "selection_executes_target": False,
        "enforcement_packet_executed": False,
        "broad_status_surface_rewrite_executed": False,
        "generated_output_mutation_executed": False,
        "historical_packet_edit_executed": False,
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


def test_post_status_selector_regression_fixture_records_mirror_drift() -> None:
    report = _json(REPORT_PATH)
    fixture = report["future_enforcement_regression_fixture"]

    assert fixture["failure_mode"] == (
        "canonical live target differs from active public/current-state "
        "mirror declarations"
    )
    assert fixture["observed_stale_target"] == "review_read_only_validation_hygiene_result"
    assert fixture["expected_live_target"] == CONSUMED_TARGET
    assert set(fixture["known_repaired_gates"]) == {
        "formal/python/tests/test_em_qft_interface_alignment_semantic_bridge_gate.py",
        "formal/python/tests/test_em_qft_physics_blocker_protocol_row_gate.py",
        "formal/python/tests/test_em_qft_post_budget_cross_pillar_review_gate.py",
        "formal/python/tests/test_em_qft_shared_dynamics_residual_unification_bridge_gate.py",
    }


def test_post_status_selector_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_post_status_surface_canonicalization_bounded_attack_selection_gate.py"
    )
