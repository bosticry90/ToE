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
from formal.python.tools.ck_family_theorem_linkage_priority_selection_after_index_report import (
    BLOCKED_CLAIMS,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    INDEX_PATH,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OBLIGATION_ROW_FIELDS,
    OBLIGATION_ROW_IDS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PRIORITY_CRITERIA,
    PRIORITY_SELECTION_RESULT,
    QFTGR_AGGREGATE_PATH,
    RANKED_ROW_IDS,
    RECOMMENDED_POST_REVIEW_TARGET,
    RECOMMENDED_PRIORITY_SELECTION_RESULT,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_PROOF_TARGET,
    SELECTED_THEOREM_ROW,
    SELECTOR_REVIEW_PATH,
    TOP_FIVE_PRIORITY_THEMES,
    TOP_OBLIGATION_CANDIDATE,
    TOP_OBLIGATION_ROW_ID,
    build_ck_family_theorem_linkage_priority_selection_after_index,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "ck_family_theorem_linkage_priority_selection_after_index_report.py"
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


def test_ck_family_theorem_linkage_priority_selection_after_index_files_exist() -> None:
    for path in [
        SELECTOR_REVIEW_PATH,
        INDEX_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_ck_family_theorem_linkage_priority_selection_after_index_ranks_rows() -> None:
    priority = _json(DEFAULT_OUT)

    assert priority["artifact_id"] == SCHEMA_ID
    assert priority["schema_id"] == SCHEMA_ID
    assert priority["packet_id"] == PACKET_ID
    assert priority["prepared"] is True
    assert priority["accepted"] is True
    assert priority["outcome_id"] == OUTCOME_ID
    assert priority["priority_selection_result"] == PRIORITY_SELECTION_RESULT
    assert priority["packet_result"] == OUTCOME_ID
    assert priority["recommended_priority_selection_result"] == (
        RECOMMENDED_PRIORITY_SELECTION_RESULT
    )
    assert priority["packet_classification"] == PACKET_CLASSIFICATION
    assert priority["consumed_target"] == CONSUMED_TARGET
    assert priority["selected_next_target"] == NEXT_TARGET
    assert priority["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert priority["recommended_post_review_target"] == RECOMMENDED_POST_REVIEW_TARGET
    assert build_ck_family_theorem_linkage_priority_selection_after_index() == priority


def test_ck_family_theorem_linkage_priority_selection_after_index_records_ranking() -> None:
    priority = _json(DEFAULT_OUT)

    assert priority["priority_criteria"] == PRIORITY_CRITERIA
    assert priority["priority_criterion_count"] == 5
    assert priority["proof_obligation_row_ids"] == OBLIGATION_ROW_IDS
    assert priority["proof_obligation_row_count"] == 13
    assert priority["obligation_row_fields"] == OBLIGATION_ROW_FIELDS
    assert priority["obligation_row_field_count"] == 10
    assert priority["ranked_row_ids"] == RANKED_ROW_IDS
    assert priority["ranked_row_count"] == 13
    assert priority["priority_ranking_count"] == 13
    assert priority["top_five_priority_themes"] == TOP_FIVE_PRIORITY_THEMES
    assert priority["top_obligation_candidate"] == TOP_OBLIGATION_CANDIDATE
    assert priority["top_obligation_row_id"] == TOP_OBLIGATION_ROW_ID
    assert priority["top_obligation_candidate_selected"] is True
    assert priority["ranking_selects_top_obligation_candidate"] is True
    assert priority["selected_proof_target"] == SELECTED_PROOF_TARGET
    assert priority["selected_theorem_row"] == SELECTED_THEOREM_ROW

    ranking = priority["priority_ranking"]
    assert ranking[0]["row_id"] == "C_exchange^{Apsi}"
    assert ranking[0]["priority_label"] == "C_exchange theorem-linkage gap"
    assert ranking[0]["top_obligation_candidate"] is True
    assert ranking[1]["row_id"] == "psi-A total conservation"
    assert ranking[2]["row_id"] == "psi-A matter-sector exchange"
    assert ranking[3]["row_id"] == "psi-A gauge-sector exchange"
    assert ranking[4]["row_id"] == "C_source^A"
    assert ranking[5]["row_id"] == "C_source^phi"
    assert all(row["selected_for_proof_execution"] is False for row in ranking)
    assert all(row["theorem_discharged"] is False for row in ranking)
    assert all(row["gap_discharged"] is False for row in ranking)
    assert all(row["rule_promoted"] is False for row in ranking)


def test_ck_family_theorem_linkage_priority_selection_after_index_preserves_nonclaims() -> None:
    priority = _json(DEFAULT_OUT)

    assert priority["blocked_claims"] == BLOCKED_CLAIMS
    assert priority["blocked_claim_count"] == 16
    assert priority["gap_count"] == 8
    assert priority["open_gap_count"] == 8
    assert priority["closed_gap_count"] == 0

    for key in [
        "priority_selection_packet_prepared",
        "priority_selection_prepared",
        "priority_selection_executed",
        "priority_rows_ranked",
        "priority_row_selected",
        "top_obligation_candidate_selected",
        "ranking_selects_top_obligation_candidate",
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
        assert priority[key] is True, key

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
        assert priority[key] is False, key

    for phrase in [
        "ranks the indexed C_k theorem-linkage proof debts",
        "selects only the top obligation candidate",
        "does not execute any proof",
        "discharge any theorem row",
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
        assert phrase in priority["non_claim_boundary"], phrase


def test_ck_family_theorem_linkage_priority_selection_after_index_rotates_to_review() -> None:
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

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == _rel(DEFAULT_OUT)
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["priority_selection_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["priority_rows_ranked"] == "yes"
    assert consumed["top_obligation_candidate"] == TOP_OBLIGATION_CANDIDATE
    assert consumed["top_obligation_row_id"] == TOP_OBLIGATION_ROW_ID
    assert consumed["selected_proof_target"] == "NONE_SELECTED"
    assert consumed["selected_theorem_row"] == "NONE_SELECTED"
    assert consumed["proof_execution_authorized"] == "no"
    assert consumed["obligation_rows_discharged"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active = _workstream(registry, NEXT_TARGET)
    assert active["status"] == "active"
    assert active["workstream_id"] == NEXT_TARGET
    assert active["active_lane"] == NEXT_TARGET
    assert active["authorization_evidence"] == evidence
    assert active["authorized_next_strict_target"] == NEXT_TARGET
    assert active["packet_result"] == "PENDING"
    assert active["review_result"] == "PENDING"
    assert active["priority_rows_ranked"] == "yes"
    assert active["top_obligation_candidate"] == TOP_OBLIGATION_CANDIDATE
    assert active["selected_proof_target"] == "NONE_SELECTED"
    assert active["selected_theorem_row"] == "NONE_SELECTED"
    assert active["proof_execution_authorized"] == "no"
    assert active["proof_attempt_executed"] == "no"
    assert active["obligation_rows_discharged"] == "no"
    assert active["master_action_promoted"] == "no"


def test_ck_family_theorem_linkage_priority_selection_after_index_mirrors() -> None:
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
        PRIORITY_SELECTION_RESULT,
        RECOMMENDED_PRIORITY_SELECTION_RESULT,
        PACKET_CLASSIFICATION,
        "CKFamilyTheoremLinkagePrioritySelectionAfterIndex",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        RECOMMENDED_POST_REVIEW_TARGET,
        TOP_OBLIGATION_CANDIDATE,
        TOP_OBLIGATION_ROW_ID,
        "psi-A total conservation",
        "psi-A matter-sector exchange",
        "psi-A gauge-sector exchange",
        "C_source^A",
        "C_source^phi",
        SELECTED_PROOF_TARGET,
        SELECTED_THEOREM_ROW,
        "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_OUTCOME_v0",
        "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_NONCLAIM_BOUNDARY_v0",
        "no theorem discharge",
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


def test_ck_family_theorem_linkage_priority_selection_after_index_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_ck_family_theorem_linkage_priority_selection_after_index_gate.py"
    )
