from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_historical_target_recorded,
    assert_public_surfaces_match_registry,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_index_result_review_report import (
    DEFAULT_OUT as INDEX_REVIEW_OUT,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as INDEX_REVIEW_OUTCOME,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_index_report import (
    BLOCKED_CLAIMS,
    CONTROLLED_STATUS_LABELS,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    LIKELY_FIRST_PRIORITY_CANDIDATE,
    LIKELY_PRIORITY_CANDIDATES,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OBLIGATION_ROW_FIELDS,
    OBLIGATION_ROW_IDS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RECOMMENDED_FIRST_PRIORITY_ROW,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_FOLLOW_ON_TARGET,
    SELECTED_FOLLOW_ON_TARGET_KIND,
    SELECTED_PACKET_EXECUTION_STATUS,
    SELECTED_PACKET_LABEL,
    SELECTED_PACKET_STATUS,
    SELECTED_PROOF_TARGET,
    SELECTED_THEOREM_ROW,
    SELECTION_RESULT,
    build_ck_family_theorem_linkage_obligation_selection_after_index,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "ck_family_theorem_linkage_obligation_selection_after_index_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
CURRENT_TARGET_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "CurrentTarget.lean"
)
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8-sig")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_ck_family_theorem_linkage_obligation_selection_after_index_files_exist() -> None:
    for path in [
        INDEX_REVIEW_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_ck_family_theorem_linkage_obligation_selection_after_index_selects_packet_only() -> None:
    prior_review = _json(INDEX_REVIEW_OUT)
    selection = _json(DEFAULT_OUT)

    assert prior_review["outcome_id"] == INDEX_REVIEW_OUTCOME
    assert prior_review["selected_next_target"] == CONSUMED_TARGET

    assert selection["artifact_id"] == SCHEMA_ID
    assert selection["schema_id"] == SCHEMA_ID
    assert selection["packet_id"] == PACKET_ID
    assert selection["prepared"] is True
    assert selection["accepted"] is True
    assert selection["outcome_id"] == OUTCOME_ID
    assert selection["selection_result"] == SELECTION_RESULT
    assert selection["packet_result"] == OUTCOME_ID
    assert selection["packet_classification"] == PACKET_CLASSIFICATION
    assert selection["consumed_target"] == CONSUMED_TARGET
    assert selection["selected_next_target"] == NEXT_TARGET
    assert selection["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert selection["selected_follow_on_target_after_review"] == SELECTED_FOLLOW_ON_TARGET
    assert selection["selected_follow_on_target_kind"] == SELECTED_FOLLOW_ON_TARGET_KIND
    assert selection["selected_packet_label"] == SELECTED_PACKET_LABEL
    assert selection["selected_packet_status"] == SELECTED_PACKET_STATUS
    assert selection["selected_packet_execution_status"] == SELECTED_PACKET_EXECUTION_STATUS
    assert build_ck_family_theorem_linkage_obligation_selection_after_index() == selection


def test_ck_family_theorem_linkage_obligation_selection_after_index_records_candidates_without_selecting_proof() -> None:
    selection = _json(DEFAULT_OUT)

    assert selection["proof_obligation_row_ids"] == OBLIGATION_ROW_IDS
    assert selection["proof_obligation_row_count"] == 13
    assert selection["obligation_row_fields"] == OBLIGATION_ROW_FIELDS
    assert selection["obligation_row_field_count"] == 10
    assert selection["controlled_status_labels"] == CONTROLLED_STATUS_LABELS
    assert selection["controlled_status_label_count"] == 7
    assert selection["likely_priority_candidates"] == LIKELY_PRIORITY_CANDIDATES
    assert selection["likely_priority_candidate_count"] == 4
    assert selection["likely_first_priority_candidate"] == LIKELY_FIRST_PRIORITY_CANDIDATE
    assert selection["recommended_first_priority_row"] == RECOMMENDED_FIRST_PRIORITY_ROW
    assert selection["selected_proof_target"] == SELECTED_PROOF_TARGET
    assert selection["selected_theorem_row"] == SELECTED_THEOREM_ROW
    assert selection["selection_option_count"] == 4
    assert selection["selection_options_selected_count"] == 1
    assert selection["selection_options_deferred_count"] == 3
    assert selection["selection_criteria_count"] == 11
    assert selection["selection_criteria_accepted_count"] == 11


def test_ck_family_theorem_linkage_obligation_selection_after_index_preserves_nonclaims() -> None:
    selection = _json(DEFAULT_OUT)

    assert selection["blocked_claims"] == BLOCKED_CLAIMS
    assert selection["blocked_claim_count"] == 16
    assert selection["gap_count"] == 8
    assert selection["open_gap_count"] == 8
    assert selection["closed_gap_count"] == 0

    for key in [
        "selector_target_prepared",
        "selector_target_accepted",
        "selection_executed",
        "obligation_after_index_selector_executed",
        "priority_selection_packet_selected",
        "priority_selection_packet_authorized_after_review",
        "selector_result_review_authorized",
        "theorem_linkage_obligation_index_reviewed",
        "obligation_index_reviewed",
        "proof_obligation_rows_indexed",
        "row_index_only",
        "gap_1_through_gap_8_indexed",
        "all_gaps_remain_open",
        "no_gap_discharged",
        "no_gap_closed",
        "no_rule_promoted",
        "no_C_k_functionalization_occurs",
        "no_C_k_variation_occurs",
        "no_seam_closure_occurs",
        "no_master_action_promotion_occurs",
    ]:
        assert selection[key] is True, key

    for key in [
        "priority_selection_packet_prepared",
        "priority_selection_packet_executed",
        "priority_selection_prepared",
        "priority_selection_executed",
        "selector_result_review_prepared",
        "selector_result_review_accepted",
        "proof_debt_target_selected",
        "proof_target_selected",
        "priority_row_selected",
        "theorem_row_selected",
        "proof_execution_authorized",
        "proof_target_execution_authorized",
        "proof_attempt_executed",
        "proof_debt_reduced",
        "proof_debt_discharged",
        "theorem_linkage_proof_attempt_authorized",
        "obligation_rows_discharged",
        "gap_1_through_gap_8_discharged",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "multiplier_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "empirical_validation_claimed",
        "master_action_promoted",
        "master_action_promotion",
    ]:
        assert selection[key] is False, key

    for phrase in [
        "selects only the C_k family theorem-linkage priority-selection packet",
        "does not prepare that packet",
        "select a theorem row for proof execution",
        "execute any proof target",
        "discharge GAP-1 through GAP-8",
        "promote any C_k rule",
        "embed C_k in an action",
        "vary C_k",
        "close EM-QFT",
        "close QFT-GR",
        "close GR-QM",
        "promote the master action",
        "working-form, noncanonical, non-promoted organizing surface",
        "full ToeFormal aggregate is kept as NOT_RUN",
    ]:
        assert phrase in selection["non_claim_boundary"], phrase


def test_ck_family_theorem_linkage_obligation_selection_after_index_rotates_to_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert is_current
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET not in registry["completed_targets"]
    assert NEXT_TARGET not in registry["consumed_targets"]
    assert NEXT_TARGET not in registry["paused_lanes"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == _rel(DEFAULT_OUT)
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["selection_result"] == OUTCOME_ID
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["selected_follow_on_target_after_review"] == SELECTED_FOLLOW_ON_TARGET
    assert consumed["priority_selection_packet_selected"] == "yes"
    assert consumed["priority_selection_packet_prepared"] == "no"
    assert consumed["selected_proof_target"] == "NONE_SELECTED"
    assert consumed["selected_theorem_row"] == "NONE_SELECTED"
    assert consumed["proof_execution_authorized"] == "no"
    assert consumed["obligation_rows_discharged"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active = _workstream(registry, NEXT_TARGET)
    assert active["status"] == "active"
    assert active["workstream_id"] == NEXT_TARGET
    assert active["active_lane"] == NEXT_TARGET
    assert active["authorized_next_strict_target"] == NEXT_TARGET
    assert active["authorized_target"] == NEXT_TARGET
    assert active["authorization_evidence"] == evidence
    assert active["report"] == _rel(DEFAULT_OUT)
    assert active["consumed_target"] == CONSUMED_TARGET
    assert active["packet_result"] == "PENDING"
    assert active["review_result"] == "PENDING"
    assert active["outcome_id"] == OUTCOME_ID
    assert active["selected_next_target"] == NEXT_TARGET
    assert active["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert active["selected_follow_on_target_after_review"] == SELECTED_FOLLOW_ON_TARGET
    assert active["priority_selection_packet_selected"] == "yes"
    assert active["priority_selection_packet_prepared"] == "no"
    assert active["selected_proof_target"] == "NONE_SELECTED"
    assert active["selected_theorem_row"] == "NONE_SELECTED"
    assert active["proof_execution_authorized"] == "no"
    assert active["proof_attempt_executed"] == "no"
    assert active["proof_debt_target_selected"] == "no"
    assert active["obligation_rows_discharged"] == "no"
    assert active["master_action_promoted"] == "no"


def test_ck_family_theorem_linkage_obligation_selection_after_index_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_AGGREGATE_PATH,
            CURRENT_TARGET_PATH,
            RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
            TOE_FORMAL_PATH,
            REGISTRY_PATH,
            SURFACES_PATH,
            FRONTIER_PATH,
            README_PATH,
            STATE_PATH,
            ROADMAP_PATH,
            STRICT_MAP_PATH,
        ]
    )
    for token in [
        PACKET_ID,
        OUTCOME_ID,
        SELECTION_RESULT,
        PACKET_CLASSIFICATION,
        "CKFamilyTheoremLinkageObligationSelectionAfterIndex",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SELECTED_FOLLOW_ON_TARGET,
        SELECTED_FOLLOW_ON_TARGET_KIND,
        LIKELY_FIRST_PRIORITY_CANDIDATE,
        RECOMMENDED_FIRST_PRIORITY_ROW,
        SELECTED_PROOF_TARGET,
        SELECTED_THEOREM_ROW,
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_OUTCOME_v0",
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_NONCLAIM_BOUNDARY_v0",
        "no theorem row selected",
        "no proof execution",
        "no GAP discharge",
        "no C_k rule promotion",
        "no action embedding",
        "no variation",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_ck_family_theorem_linkage_obligation_selection_after_index_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_ck_family_theorem_linkage_obligation_selection_after_index_gate.py"
    )
