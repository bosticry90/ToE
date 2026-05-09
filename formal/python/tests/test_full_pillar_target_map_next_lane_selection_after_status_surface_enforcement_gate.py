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
    / "FullPillarTargetMapNextLaneSelectionAfterStatusSurfaceEnforcement.lean"
)
POST_ENFORCEMENT_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostStatusSurfaceEnforcementBoundedAttackSelection.lean"
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
    / "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_STATUS_SURFACE_ENFORCEMENT_20260508_v0.json"
)
POST_ENFORCEMENT_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_STATUS_SURFACE_ENFORCEMENT_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
)

REPORT_ID = (
    "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_STATUS_SURFACE_ENFORCEMENT_20260508_v0"
)
SURFACE_ID = (
    "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_v0"
)
CONSUMED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
CONSUMED_TOKEN = "POST_STATUS_SURFACE_ENFORCEMENT_NEXT_ATTACK_SELECTED"
RESULT_TOKEN = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_STATUS_SURFACE_ENFORCEMENT"
SELECTED_LANE = "NEXT_PROOF_DEBT_LEDGER_DISCHARGE_ITEM"
SELECTED_TARGET = "prepare_next_proof_debt_ledger_discharge_item"
CANDIDATE_CLASSES = {
    SELECTED_LANE,
    "QM_STAT_THEOREM_GAP_RE_ENTRY_LANE",
    "SR_COSMO_GLOBAL_OBSTRUCTION_FOLLOW_UP",
    "QFT_GR_WITNESS_SEARCH_PLAN",
    "MASTER_ACTION_DEPENDENCY_GAP_REDUCTION_PLAN",
    "ARTIFACT_RETENTION_MIGRATION_PLAN",
    "STATUS_SURFACE_ENFORCEMENT_FOLLOWUP",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_after_status_enforcement_full_pillar_selector_selects_proof_debt_item() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        SELECTED_LANE,
        SELECTED_TARGET,
        "FullPillarTargetMapNextLaneSelectionAfterStatusSurfaceEnforcementStatus",
        "FullPillarTargetMapNextLaneSelectionAfterStatusSurfaceEnforcementDecision",
        "selectNextProofDebtLedgerDischargeItem",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_consumes_return_target_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_consumes_selector_token_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_rows_evaluated_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_exactly_one_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_result_token_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_selected_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_selected_target_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_candidate_count_v0",
    } | CANDIDATE_CLASSES:
        assert token in text

    assert (
        "import ToeFormal.Derivation.FullPillarTargetMapNextLaneSelectionAfterStatusSurfaceEnforcement"
        in aggregate_text
    )


def test_after_status_enforcement_full_pillar_selector_preserves_enforcement() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_infrastructure_closed_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_proof_debt_reentry_low_risk_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_read_only_preserved_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_freeze_preserved_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_mirror_parity_preserved_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_full_pytest_count_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_full_pytest_skipped_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_lean_jobs_v0",
        "read_only_validation_preserved",
        "artifact_freeze_preserved",
        "active_live_target_mirror_parity_preserved",
    }:
        assert token in text


def test_after_status_enforcement_full_pillar_selector_preserves_nonclaims() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_axiom_count_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_default_nonalias_absent_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_sample_rep32_retained_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_qft_gr_not_authorized_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_does_not_execute_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_proof_debt_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_qm_stat_reentry_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_sr_cosmo_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_qft_gr_witness_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_gap_reduction_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_artifact_migration_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_followup_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_master_action_not_promoted_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_no_pillar_completion_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_no_seam_closure_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_no_phase2_readiness_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_no_empirical_adequacy_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_no_canonical_toe_claim_v0",
        "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_after_status_enforcement_full_pillar_report_records_proof_debt_lane() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_lane"] == SELECTED_LANE
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selected_next_target_kind"] == "proof_debt_item_preparation_only"
    assert report["selection_surface"] == _rel(SELECTION_PATH)
    assert report["post_enforcement_selection_surface"] == _rel(
        POST_ENFORCEMENT_SELECTION_PATH
    )
    assert report["post_enforcement_selection_report"] == _rel(
        POST_ENFORCEMENT_REPORT_PATH
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


def test_after_status_enforcement_full_pillar_report_preserves_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["validation_checkpoint"] == {
        "full_pytest_passed": 6614,
        "full_pytest_skipped": 230,
        "full_pytest_is_prior_checkpoint_not_fresh_for_this_selector": True,
        "ordinary_validation_mode": "read_only_by_default",
        "read_only_proof": "prior full pytest checkpoint plus clean post-commit diff check",
        "read_only_proof_passed": True,
        "lean_build_target": "ToeFormal",
        "lean_build_jobs": 7985,
        "governance_suite_passed": True,
    }
    assert report["preserved_enforcement"] == {
        "active_live_target_mirror_parity_preserved": True,
        "loop_registry_canonical_source_preserved": True,
        "generated_output_read_only_preserved": True,
        "ordinary_validation_mode": "read_only_by_default",
        "artifact_freeze_preserved": True,
        "historical_packet_history_tokens_allowed": True,
    }
    assert report["preserved_posture"]["real_axiom_count"] == 60
    assert report["preserved_posture"][
        "defaultNonAlias_absent_from_unresolved_axiom_debt"
    ] is True
    assert report["preserved_posture"]["sampleRep32_retained"] is True
    assert report["preserved_posture"]["qft_gr_source_map_closure_authorized"] is False
    assert report["nonclaim_boundaries"] == {
        "selection_executes_lane": False,
        "qft_gr_witness_search_selected": False,
        "master_action_gap_reduction_selected": False,
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }


def test_after_status_enforcement_full_pillar_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_full_pillar_target_map_next_lane_selection_after_status_surface_enforcement_gate.py"
    )
