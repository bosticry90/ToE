from __future__ import annotations

import json
import re
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
    / "PostStatusSurfaceEnforcementBoundedAttackSelection.lean"
)
RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "StatusSurfaceCanonicalizationEnforcementPacketResultReview.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_STATUS_SURFACE_ENFORCEMENT_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
)
RESULT_REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_RESULT_REVIEW_20260505_v0.json"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SEAM_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
SEAM_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
)

REPORT_ID = "POST_STATUS_SURFACE_ENFORCEMENT_BOUNDED_ATTACK_SELECTION_20260505_v0"
SURFACE_ID = "post_status_surface_enforcement_bounded_attack_selection_v0"
CONSUMED_TARGET = "select_next_post_status_surface_enforcement_bounded_attack"
CONSUMED_TOKEN = "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_RESULT_REVIEW_CONSUMED"
RESULT_TOKEN = "POST_STATUS_SURFACE_ENFORCEMENT_NEXT_ATTACK_SELECTED"
SELECTED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
MIRROR_KEY = "MASTER_ACTION_CURRENT_CITATION_TARGET_v0"
ACTIVE_MIRRORS = (SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH)
CANDIDATE_TARGETS = {
    SELECTED_TARGET,
    "prepare_next_proof_debt_ledger_discharge_item",
    "prepare_artifact_retention_migration_plan",
    "prepare_qm_stat_theorem_gap_reentry",
    "prepare_sr_cosmo_global_obstruction_followup",
    "prepare_status_surface_enforcement_followup_packet",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _active_mirror_values(text: str) -> list[str]:
    return re.findall(rf"{MIRROR_KEY}:\s*([A-Za-z0-9_]+)", text)


def test_post_enforcement_selector_surface_selects_full_pillar_return() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        SELECTED_TARGET,
        "PostStatusSurfaceEnforcementBoundedAttackSelectionStatus",
        "PostStatusSurfaceEnforcementBoundedAttackSelectionDecision",
        "returnToFullPillarTargetMapNextLaneSelection",
        "post_status_surface_enforcement_bounded_attack_selection_consumes_live_target_v0",
        "post_status_surface_enforcement_bounded_attack_selection_consumes_review_token_v0",
        "post_status_surface_enforcement_bounded_attack_selection_result_token_v0",
        "post_status_surface_enforcement_bounded_attack_selection_selected_target_v0",
        "post_status_surface_enforcement_bounded_attack_selection_decision_v0",
        "post_status_surface_enforcement_bounded_attack_selection_candidate_count_v0",
        "post_status_surface_enforcement_bounded_attack_selection_exactly_one_target_v0",
    } | CANDIDATE_TARGETS:
        assert token in text

    assert (
        "import ToeFormal.Derivation.PostStatusSurfaceEnforcementBoundedAttackSelection"
        in aggregate_text
    )


def test_post_enforcement_selector_preserves_status_boundaries() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_status_surface_enforcement_bounded_attack_selection_mirror_parity_preserved_v0",
        "post_status_surface_enforcement_bounded_attack_selection_loop_registry_preserved_v0",
        "post_status_surface_enforcement_bounded_attack_selection_source_mirror_preserved_v0",
        "post_status_surface_enforcement_bounded_attack_selection_generated_read_only_v0",
        "post_status_surface_enforcement_bounded_attack_selection_read_only_preserved_v0",
        "post_status_surface_enforcement_bounded_attack_selection_freeze_preserved_v0",
        "post_status_surface_enforcement_bounded_attack_selection_historical_tokens_allowed_v0",
        "post_status_surface_enforcement_bounded_attack_selection_mirror_surface_count_v0",
        "statusSurfaceCanonicalizationEnforcementPacketResultReviewStatusV0",
    }:
        assert token in text


def test_post_enforcement_selector_records_selection_only_scope() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_status_surface_enforcement_bounded_attack_selection_does_not_execute_target_v0",
        "post_status_surface_enforcement_bounded_attack_selection_full_pillar_return_selected_v0",
        "post_status_surface_enforcement_bounded_attack_selection_proof_debt_not_selected_v0",
        "post_status_surface_enforcement_bounded_attack_selection_artifact_migration_not_selected_v0",
        "post_status_surface_enforcement_bounded_attack_selection_qm_stat_not_selected_v0",
        "post_status_surface_enforcement_bounded_attack_selection_sr_cosmo_not_selected_v0",
        "post_status_surface_enforcement_bounded_attack_selection_followup_not_selected_v0",
        "selection_executes_target := False",
        "full_pillar_target_map_return_selected := True",
        "proof_debt_discharge_item_selected := False",
        "artifact_retention_migration_plan_selected := False",
        "qm_stat_reentry_selected := False",
        "sr_cosmo_followup_selected := False",
        "status_surface_enforcement_followup_selected := False",
    }:
        assert token in text


def test_post_enforcement_selector_preserves_checkpoint_and_nonclaims() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_status_surface_enforcement_bounded_attack_selection_full_pytest_count_v0",
        "post_status_surface_enforcement_bounded_attack_selection_full_pytest_skipped_v0",
        "post_status_surface_enforcement_bounded_attack_selection_lean_jobs_v0",
        "post_status_surface_enforcement_bounded_attack_selection_axiom_count_v0",
        "post_status_surface_enforcement_bounded_attack_selection_default_nonalias_absent_v0",
        "post_status_surface_enforcement_bounded_attack_selection_sample_rep32_retained_v0",
        "post_status_surface_enforcement_bounded_attack_selection_qft_gr_not_authorized_v0",
        "post_status_surface_enforcement_bounded_attack_selection_master_action_not_promoted_v0",
        "post_status_surface_enforcement_bounded_attack_selection_no_pillar_completion_v0",
        "post_status_surface_enforcement_bounded_attack_selection_no_seam_closure_v0",
        "post_status_surface_enforcement_bounded_attack_selection_no_phase2_readiness_v0",
        "post_status_surface_enforcement_bounded_attack_selection_no_empirical_adequacy_v0",
        "post_status_surface_enforcement_bounded_attack_selection_no_canonical_toe_claim_v0",
        "post_status_surface_enforcement_bounded_attack_selection_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_post_enforcement_selector_report_records_selection() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_selection_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_result_review_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selected_next_target_kind"] == "full_pillar_target_map_next_lane_selection"
    assert report["selector_surface"] == _rel(SELECTION_PATH)
    assert report["source_result_review_surface"] == _rel(RESULT_REVIEW_PATH)
    assert report["source_result_review_report"] == _rel(RESULT_REVIEW_REPORT_PATH)
    assert report["focused_gate"] == (
        "formal/python/tests/"
        "test_post_status_surface_enforcement_bounded_attack_selection_gate.py"
    )
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_TARGET"
    assert report["selection_executes_target"] is False
    assert report["full_pillar_target_map_return_selected"] is True
    assert report["selection_count"] == 1
    assert report["candidate_target_count"] == 6
    assert {row["target"] for row in report["candidate_targets"]} == CANDIDATE_TARGETS

    selected = [row for row in report["candidate_targets"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["target"] == SELECTED_TARGET
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_post_enforcement_selector_report_preserves_boundaries() -> None:
    report = _json(REPORT_PATH)
    checkpoint = report["validation_checkpoint"]
    enforcement = report["preserved_enforcement"]

    assert checkpoint == {
        "full_pytest_passed": 6614,
        "full_pytest_skipped": 230,
        "full_pytest_is_prior_checkpoint_not_fresh_for_this_selector": False,
        "full_pytest_fresh_for_this_selector": True,
        "ordinary_validation_mode": "read_only_by_default",
        "read_only_proof": (
            "full pytest from selector implementation followed by clean diff checks"
        ),
        "read_only_proof_passed": True,
        "lean_build_target": "ToeFormal",
        "lean_build_jobs": 7985,
        "governance_suite_passed": True,
    }
    assert enforcement == {
        "active_live_target_mirror_parity_preserved": True,
        "loop_registry_canonical_source_preserved": True,
        "source_and_mirror_classification_preserved": True,
        "generated_output_read_only_preserved": True,
        "ordinary_validation_mode": "read_only_by_default",
        "read_only_validation_preserved": True,
        "artifact_freeze_preserved": True,
        "historical_packet_history_tokens_allowed": True,
    }
    assert report["preserved_posture"] == {
        "real_axiom_count": 60,
        "defaultNonAlias_absent_from_unresolved_axiom_debt": True,
        "sampleRep32_retained": True,
        "qft_gr_source_map_closure_authorized": False,
    }
    assert report["nonclaim_boundaries"] == {
        "selection_executes_target": False,
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }


def test_post_enforcement_selector_registry_records_historical_rotation() -> None:
    registry = _json(REGISTRY_PATH)
    state = registry["current_target_state"]
    report = _json(REPORT_PATH)
    parity = report["active_live_target_mirror_parity"]
    workstream = next(
        item
        for item in registry["workstreams"]
        if item["workstream_id"] == "post_status_surface_enforcement_bounded_attack_selection"
    )

    assert SELECTED_TARGET in registry["next_strict_target_coverage"]
    assert "prepare_next_proof_debt_ledger_discharge_item" in registry[
        "next_strict_target_coverage"
    ]
    if state["live_next_target"] == "prepare_next_proof_debt_ledger_discharge_item":
        assert state["previous_live_next_target"] == SELECTED_TARGET
    assert workstream["status"] == "paused"
    assert workstream["authorization_evidence"] == _rel(SELECTION_PATH)
    assert workstream["selected_next_target"] == SELECTED_TARGET
    assert workstream["result_token"] == RESULT_TOKEN
    assert parity["canonical_source"] == _rel(REGISTRY_PATH)
    assert parity["canonical_json_pointer"] == "/current_target_state/live_next_target"
    assert parity["expected_live_target_after_selection"] == SELECTED_TARGET
    assert {
        row["surface"] for row in parity["active_public_mirror_fields"]
    } == {_rel(path) for path in ACTIVE_MIRRORS}
    assert {row["field"] for row in parity["active_public_mirror_fields"]} == {MIRROR_KEY}

    for path in ACTIVE_MIRRORS:
        text = _read(path)
        values = _active_mirror_values(text)
        assert values == [
            state["live_next_target"]
        ], f"{path} active mirror values: {values!r}"


def test_post_enforcement_selector_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_post_status_surface_enforcement_bounded_attack_selection_gate.py"
    )
