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
    / "FullPillarTargetMapNextLaneSelectionAfterSampleRep32AxiomAudit.lean"
)
POST_SAMPLEREP32_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostSampleRep32AxiomAuditBoundedAttackSelection.lean"
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
    / "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_SAMPLEREP32_AXIOM_AUDIT_20260510_v0.json"
)
POST_SAMPLEREP32_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_SAMPLEREP32_AXIOM_AUDIT_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
)

REPORT_ID = (
    "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_SAMPLEREP32_AXIOM_AUDIT_20260510_v0"
)
SURFACE_ID = (
    "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_v0"
)
CONSUMED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
CONSUMED_TOKEN = "POST_SAMPLEREP32_AXIOM_AUDIT_NEXT_ATTACK_SELECTED"
RESULT_TOKEN = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_SAMPLEREP32_AXIOM_AUDIT"
SELECTED_LANE = "QM_STAT_THEOREM_GAP_RE_ENTRY_LANE"
SELECTED_TARGET = "prepare_qm_stat_theorem_gap_reentry"
QM_STAT_MAP_ACTION = "map_qm_stat_full_probability_entropy_transport_obligations"
CANDIDATE_CLASSES = {
    "NEXT_PROOF_DEBT_LEDGER_DISCHARGE_ITEM",
    SELECTED_LANE,
    "SR_COSMO_GLOBAL_OBSTRUCTION_FOLLOW_UP",
    "GR_WEAK_FIELD_SOURCE_SIDE_OBLIGATION_LANE",
    "MASTER_ACTION_DEPENDENCY_GAP_REDUCTION_PLAN",
    "QFT_GR_WITNESS_SEARCH_PLAN",
    "ARTIFACT_RETENTION_MIGRATION_PLAN",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_after_samplerep32_audit_full_pillar_selector_selects_qm_stat_reentry() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        SELECTED_LANE,
        SELECTED_TARGET,
        QM_STAT_MAP_ACTION,
        "FullPillarTargetMapNextLaneSelectionAfterSampleRep32AxiomAuditStatus",
        "FullPillarTargetMapNextLaneSelectionAfterSampleRep32AxiomAuditDecision",
        "selectQMSTATTheoremGapReEntryLane",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_consumes_return_target_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_consumes_selector_token_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_rows_evaluated_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_exactly_one_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_result_token_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_selected_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_selected_target_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_candidate_count_v0",
    } | CANDIDATE_CLASSES:
        assert token in text

    assert (
        "import ToeFormal.Derivation.FullPillarTargetMapNextLaneSelectionAfterSampleRep32AxiomAudit"
        in aggregate_text
    )


def test_after_samplerep32_audit_full_pillar_selector_records_qm_stat_readiness() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "FULL_SEAM_QM_STAT_TARGET_MAP_v0",
        "qm_stat_reentry_nonlive_governance_path_available",
        "bounded_theorem_gap_item_ready",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_qm_stat_row_ready_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_qm_stat_map_action_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_qm_stat_row_map_action_source_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_nonlive_governance_path_available_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_bounded_item_ready_v0",
    }:
        assert token in text


def test_after_samplerep32_audit_full_pillar_selector_preserves_axiom_posture() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_axiom_count_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_no_sorry_or_admit_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_file_count_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_default_nonalias_absent_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_default_nonalias_lean_backed_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_sample_rep32_absent_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_sample_rep32_lean_backed_v0",
    }:
        assert token in text


def test_after_samplerep32_audit_full_pillar_selector_preserves_nonclaims() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_qft_gr_not_authorized_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_does_not_execute_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_proof_debt_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_qm_stat_reentry_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_sr_cosmo_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_gr_weak_field_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_qft_gr_witness_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_gap_reduction_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_artifact_migration_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_master_action_not_promoted_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_no_pillar_completion_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_no_seam_closure_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_no_phase2_readiness_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_no_empirical_adequacy_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_no_canonical_toe_claim_v0",
        "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_after_samplerep32_audit_full_pillar_report_records_qm_stat_lane() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_lane"] == SELECTED_LANE
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selected_next_target_kind"] == "qm_stat_theorem_gap_reentry_preparation_only"
    assert report["selection_surface"] == _rel(SELECTION_PATH)
    assert report["post_samplerep32_axiom_audit_selection_surface"] == _rel(
        POST_SAMPLEREP32_SELECTION_PATH
    )
    assert report["post_samplerep32_axiom_audit_selection_report"] == _rel(
        POST_SAMPLEREP32_REPORT_PATH
    )
    assert report["target_map_surface"] == _rel(TARGET_MAP_PATH)
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_LANE"
    assert report["selection_executes_lane"] is False
    assert report["selection_count"] == 1
    assert report["candidate_lane_count"] == 7

    selected = [row for row in report["candidate_classes"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["class_id"] == SELECTED_LANE
    assert selected[0]["candidate_target"] == SELECTED_TARGET
    assert {row["class_id"] for row in report["candidate_classes"]} == CANDIDATE_CLASSES
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_after_samplerep32_audit_full_pillar_report_preserves_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["validation_checkpoint"] == {
        "full_pytest_passed": 6671,
        "full_pytest_skipped": 235,
        "full_pytest_is_prior_checkpoint_not_fresh_for_this_selector": True,
        "ordinary_validation_mode": "read_only_by_default",
        "read_only_proof": "prior full pytest checkpoint plus clean post-commit diff check",
        "read_only_proof_passed": True,
        "lean_build_target": "ToeFormal",
        "lean_build_jobs": 7993,
        "governance_suite_passed": True,
    }
    assert report["qm_stat_readiness_basis"] == {
        "target_map_row": "FULL_SEAM_QM_STAT_TARGET_MAP_v0",
        "target_map_next_admissible_action": QM_STAT_MAP_ACTION,
        "prior_reentry_authorization": "QM_STAT_REENTRY_SINGLE_GOVERNED_REVIEW_PATH_AUTHORIZED_NONLIVE_v0",
        "bounded_item_ready": True,
        "canonical_mutation_authorized": False,
        "seam_closure_authorized": False,
    }
    assert report["preserved_posture"]["real_axiom_count"] == 59
    assert report["preserved_posture"]["real_sorry_or_admit_count"] == 0
    assert report["preserved_posture"]["real_axiom_file_count"] == 14
    assert report["preserved_posture"][
        "defaultNonAlias_absent_from_unresolved_axiom_debt"
    ] is True
    assert report["preserved_posture"][
        "sampleRep32_absent_from_unresolved_axiom_debt"
    ] is True
    assert report["preserved_posture"]["qft_gr_source_map_closure_authorized"] is False
    assert report["nonclaim_boundaries"] == {
        "selection_executes_lane": False,
        "proof_debt_discharge_item_selected": False,
        "qm_stat_theorem_gap_reentry_selected": True,
        "sr_cosmo_obstruction_followup_selected": False,
        "gr_weak_field_source_side_selected": False,
        "qft_gr_witness_search_selected": False,
        "master_action_gap_reduction_selected": False,
        "artifact_retention_migration_plan_selected": False,
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }


def test_after_samplerep32_audit_full_pillar_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_gate.py"
    )
