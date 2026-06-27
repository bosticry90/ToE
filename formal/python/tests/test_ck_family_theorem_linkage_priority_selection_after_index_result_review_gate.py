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
from formal.python.tools.ck_family_theorem_linkage_priority_selection_after_index_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    BLOCKED_CLAIMS,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OBLIGATION_ROW_FIELDS,
    OBLIGATION_ROW_IDS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PRIORITY_CRITERIA,
    PRIORITY_SELECTION_PATH,
    QFTGR_AGGREGATE_PATH,
    RANKED_ROW_IDS,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SELECTED_PROOF_TARGET,
    SELECTED_THEOREM_ROW,
    STRICT_REVIEW_RESULT,
    TOP_FIVE_PRIORITY_THEMES,
    TOP_OBLIGATION_CANDIDATE,
    TOP_OBLIGATION_PACKET_PLAIN_MEANING,
    TOP_OBLIGATION_PACKET_SCOPE,
    TOP_OBLIGATION_ROW_ID,
    build_ck_family_theorem_linkage_priority_selection_after_index_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "ck_family_theorem_linkage_priority_selection_after_index_result_review_report.py"
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


def test_ck_family_theorem_linkage_priority_selection_result_review_files_exist() -> None:
    for path in [
        PRIORITY_SELECTION_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_ck_family_theorem_linkage_priority_selection_result_review_accepts_ranking() -> None:
    review = _json(DEFAULT_OUT)

    assert review["artifact_id"] == SCHEMA_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == OUTCOME_ID
    assert review["packet_result"] == OUTCOME_ID
    assert review["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["post_review_target"] == NEXT_TARGET
    assert build_ck_family_theorem_linkage_priority_selection_after_index_result_review() == review


def test_ck_family_theorem_linkage_priority_selection_result_review_records_acceptance() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["accepted_review_finding_count"] == 12
    assert review["priority_criteria"] == PRIORITY_CRITERIA
    assert review["priority_criterion_count"] == 5
    assert review["proof_obligation_row_ids"] == OBLIGATION_ROW_IDS
    assert review["proof_obligation_row_count"] == 13
    assert review["obligation_row_fields"] == OBLIGATION_ROW_FIELDS
    assert review["obligation_row_field_count"] == 10
    assert review["ranked_row_ids"] == RANKED_ROW_IDS
    assert review["ranked_row_count"] == 13
    assert review["priority_ranking_count"] == 13
    assert review["top_five_priority_themes"] == TOP_FIVE_PRIORITY_THEMES
    assert review["top_obligation_candidate"] == TOP_OBLIGATION_CANDIDATE
    assert review["top_obligation_row_id"] == TOP_OBLIGATION_ROW_ID
    assert review["top_obligation_candidate_selected"] is True
    assert review["top_obligation_packet_scope"] == TOP_OBLIGATION_PACKET_SCOPE
    assert (
        review["top_obligation_packet_plain_meaning"]
        == TOP_OBLIGATION_PACKET_PLAIN_MEANING
    )
    assert review["top_obligation_packet_preparation_authorized"] is True
    assert review["selected_proof_target"] == SELECTED_PROOF_TARGET
    assert review["selected_theorem_row"] == SELECTED_THEOREM_ROW


def test_ck_family_theorem_linkage_priority_selection_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)

    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["blocked_claim_count"] == 16
    assert review["gap_count"] == 8
    assert review["open_gap_count"] == 8
    assert review["closed_gap_count"] == 0

    for key in [
        "result_review_prepared",
        "result_review_accepted",
        "priority_selection_packet_reviewed",
        "priority_selection_packet_prepared",
        "priority_selection_prepared",
        "priority_selection_executed",
        "priority_rows_ranked",
        "priority_row_selected",
        "priority_ranking_accepted",
        "ranking_only_review",
        "top_obligation_candidate_selected",
        "top_obligation_packet_preparation_authorized",
        "theorem_linkage_obligation_index_reviewed",
        "obligation_index_reviewed",
        "proof_obligation_rows_indexed",
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
        assert review[key] is True, key

    for key in [
        "proof_debt_target_selected",
        "proof_target_selected",
        "theorem_row_selected",
        "proof_execution_authorized",
        "proof_target_execution_authorized",
        "proof_attempt_executed",
        "proof_debt_reduced",
        "proof_debt_discharged",
        "theorem_linkage_proof_attempt_authorized",
        "theorem_linkage_completed",
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
        "empirical_prediction_claimed",
        "empirical_validation_claimed",
        "master_action_promoted",
        "master_action_promotion",
    ]:
        assert review[key] is False, key

    for phrase in [
        "accepts only that 13 obligation rows were ranked",
        "C_exchange is the top candidate",
        "does not execute any proof",
        "discharge any theorem row",
        "discharge GAP-1 through GAP-8",
        "promote any C_k rule",
        "embed C_k in an action",
        "vary C_k",
        "claim empirical prediction or validation",
        "promote the master action",
        "below seam closure",
        "working-form, noncanonical organizing surface",
        "not a promoted final law",
    ]:
        assert phrase in review["non_claim_boundary"], phrase


def test_ck_family_theorem_linkage_priority_selection_result_review_records_lean_status() -> None:
    review = _json(DEFAULT_OUT)

    assert review["lean_status_wording"] == LEAN_STATUS_WORDING
    assert (
        review["full_toeformal_aggregate_status_for_review"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
    )
    assert (
        review["scoped_lean_targets_status_for_review"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
    )
    assert review["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(review)


def test_ck_family_theorem_linkage_priority_selection_result_review_rotates_to_top_packet() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert not is_current
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == _rel(DEFAULT_OUT)
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["priority_rows_ranked"] == "yes"
    assert consumed["top_obligation_candidate"] == TOP_OBLIGATION_CANDIDATE
    assert consumed["top_obligation_row_id"] == TOP_OBLIGATION_ROW_ID
    assert consumed["top_obligation_packet_scope"] == TOP_OBLIGATION_PACKET_SCOPE
    assert consumed["selected_proof_target"] == "NONE_SELECTED"
    assert consumed["selected_theorem_row"] == "NONE_SELECTED"
    assert consumed["proof_execution_authorized"] == "no"
    assert consumed["obligation_rows_discharged"] == "no"
    assert consumed["master_action_promoted"] == "no"

    packet = _workstream(registry, NEXT_TARGET)
    assert packet["status"] == "paused"
    assert packet["workstream_id"] == NEXT_TARGET
    assert packet["active_lane"] == NEXT_TARGET
    assert packet["authorization_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "CKFamilyTopTheoremLinkageObligationPacket.lean"
    )
    assert packet["authorized_next_strict_target"] == NEXT_TARGET
    assert packet["packet_result"] == (
        "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_CEXCHANGE_"
        "THEOREM_LINKAGE_OBLIGATION_SCOPED_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
    )
    assert packet["strict_packet_result"] == (
        "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_CEXCHANGE_FROM_"
        "TOTAL_CONSERVATION_THEOREM_TARGET_INDEXED_NO_ACTION_VARIATION_OR_MASTER_"
        "ACTION_PROMOTION"
    )
    assert packet["selected_next_target"] == (
        "review_ck_family_top_theorem_linkage_obligation_packet_result"
    )
    assert packet["selected_next_target_kind"] == (
        "ck_family_top_theorem_linkage_obligation_packet_result_review"
    )
    assert packet["top_obligation_packet_scope"] == TOP_OBLIGATION_PACKET_SCOPE
    assert packet["top_obligation_packet_prepared"] == "yes"
    assert packet["theorem_target_id"] == "cexchange_from_total_conservation"
    assert packet["theorem_target_indexed"] == "yes"
    assert packet["selected_proof_target"] == "NONE_SELECTED"
    assert packet["proof_execution_authorized"] == "no"
    assert packet["proof_attempt_executed"] == "no"
    assert packet["theorem_discharged"] == "no"
    assert packet["master_action_promoted"] == "no"


def test_ck_family_theorem_linkage_priority_selection_result_review_mirrors() -> None:
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
        STRICT_REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        "CKFamilyTheoremLinkagePrioritySelectionAfterIndexResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        TOP_OBLIGATION_CANDIDATE,
        TOP_OBLIGATION_ROW_ID,
        TOP_OBLIGATION_PACKET_SCOPE,
        TOP_OBLIGATION_PACKET_PLAIN_MEANING,
        SELECTED_PROOF_TARGET,
        SELECTED_THEOREM_ROW,
        LEAN_STATUS_WORDING,
        "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_RESULT_REVIEW_OUTCOME_v0",
        "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_SCOPE_v0",
        "no theorem discharge",
        "no proof execution",
        "no GAP discharge",
        "no C_k rule promotion",
        "no action embedding",
        "no variation",
        "no seam closure",
        "no empirical validation",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_ck_family_theorem_linkage_priority_selection_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_ck_family_theorem_linkage_priority_selection_after_index_result_review_gate.py"
    )
