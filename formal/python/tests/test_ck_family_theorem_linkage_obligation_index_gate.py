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
from formal.python.tools.ck_family_theorem_linkage_obligation_index_report import (
    BLOCKED_CLAIMS,
    CONTROLLED_STATUS_LABELS,
    DEFAULT_OUT,
    INDEX_RESULT,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OBLIGATION_ROW_FIELDS,
    OBLIGATION_ROW_IDS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    build_ck_family_theorem_linkage_obligation_index,
)
from formal.python.tools.master_action_surface_selection_after_ck_family_gap_review_result_review_report import (
    DEFAULT_OUT as PRIOR_REVIEW_OUT,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as PRIOR_REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "ck_family_theorem_linkage_obligation_index_report.py"
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


def test_ck_family_theorem_linkage_obligation_index_files_exist() -> None:
    for path in [
        PRIOR_REVIEW_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_ck_family_theorem_linkage_obligation_index_prepared() -> None:
    prior_review = _json(PRIOR_REVIEW_OUT)
    index = _json(DEFAULT_OUT)

    assert prior_review["outcome_id"] == PRIOR_REVIEW_OUTCOME
    assert prior_review["selected_next_target"] == CONSUMED_TARGET

    assert index["artifact_id"] == SCHEMA_ID
    assert index["schema_id"] == SCHEMA_ID
    assert index["packet_id"] == PACKET_ID
    assert index["prepared"] is True
    assert index["accepted"] is True
    assert index["outcome_id"] == OUTCOME_ID
    assert index["index_result"] == INDEX_RESULT
    assert index["packet_result"] == OUTCOME_ID
    assert index["packet_classification"] == PACKET_CLASSIFICATION
    assert index["consumed_target"] == CONSUMED_TARGET
    assert index["selected_next_target"] == NEXT_TARGET
    assert index["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_ck_family_theorem_linkage_obligation_index() == index


def test_ck_family_theorem_linkage_obligation_index_rows_and_statuses() -> None:
    index = _json(DEFAULT_OUT)
    rows = index["proof_obligation_rows"]

    assert index["proof_obligation_row_ids"] == OBLIGATION_ROW_IDS
    assert index["proof_obligation_row_count"] == 13
    assert index["obligation_row_fields"] == OBLIGATION_ROW_FIELDS
    assert index["obligation_row_field_count"] == 10
    assert index["controlled_status_labels"] == CONTROLLED_STATUS_LABELS
    assert index["controlled_status_label_count"] == 7
    assert [row["row_id"] for row in rows] == OBLIGATION_ROW_IDS

    expected_main_counts = {
        "POLICY_LINKED_ADMISSIBILITY_ONLY": 7,
        "ROUTE_CONSTRUCTED_UNDER_ASSUMPTIONS": 2,
        "THEOREM_LINKED_CONDITIONAL": 4,
    }
    for key, value in expected_main_counts.items():
        assert index["theorem_linkage_status_counts"][key] == value

    controlled = set(CONTROLLED_STATUS_LABELS)
    required_keys = {
        "rule_family",
        "field_or_interaction_scope",
        "current_evidence_pointer",
        "theorem_linkage_status",
        "supplied_assumptions",
        "open_proof_debt",
        "functionalization_blocker",
        "variation_blocker",
        "seam_closure_blocker",
        "next_possible_theorem_slice",
    }
    for row in rows:
        assert required_keys.issubset(row), row["row_id"]
        assert row["required_fields_recorded"] == OBLIGATION_ROW_FIELDS
        assert row["theorem_linkage_status"] in controlled
        assert set(row["controlled_statuses"]).issubset(controlled)
        assert "NOT_FUNCTIONALIZED" in row["controlled_statuses"]
        assert "NOT_VARIED" in row["controlled_statuses"]
        assert "OPEN_PROOF_DEBT" in row["controlled_statuses"]
        assert (REPO_ROOT / row["current_evidence_pointer"]).exists()
        for evidence in row["supporting_evidence_pointers"]:
            assert (REPO_ROOT / evidence).exists(), evidence
        for key in [
            "proof_attempt_executed",
            "proof_obligation_discharged",
            "gap_discharged",
            "rule_promoted",
            "functionalized",
            "varied",
            "seam_closed",
        ]:
            assert row[key] is False, (row["row_id"], key)


def test_ck_family_theorem_linkage_obligation_index_preserves_nonclaims() -> None:
    index = _json(DEFAULT_OUT)

    assert index["blocked_claims"] == BLOCKED_CLAIMS
    assert index["blocked_claim_count"] == 16
    assert index["gap_count"] == 8
    assert index["open_gap_count"] == 8
    assert index["closed_gap_count"] == 0

    for key in [
        "theorem_linkage_obligation_index_prepared",
        "theorem_linkage_obligation_index_executed",
        "obligation_index_prepared",
        "obligation_index_executed",
        "proof_obligation_rows_indexed",
        "rule_family_theorem_linkage_and_proof_debt_rows_indexed",
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
        assert index[key] is True, key

    for key in [
        "theorem_linkage_obligation_index_reviewed",
        "obligation_index_reviewed",
        "proof_attempt_executed",
        "proof_debt_reduced",
        "proof_debt_discharged",
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
        "seam_closure_claim",
        "master_action_promoted",
        "master_action_promotion",
    ]:
        assert index[key] is False, key

    for phrase in [
        "prepares only the C_k family theorem-linkage obligation index",
        "discharges no GAP-1 through GAP-8 item",
        "proves no row",
        "promotes no C_k rule",
        "embeds no C_k rule in an action",
        "varies no C_k rule",
        "selects no multiplier route",
        "selects no penalty route",
        "makes no direct dynamical-law claim",
        "promotes no master action",
        "working-form, noncanonical, non-promoted organizing surface",
        "full ToeFormal aggregate is kept as NOT_RUN",
    ]:
        assert phrase in index["non_claim_boundary"], phrase


def test_ck_family_theorem_linkage_obligation_index_rotates_to_result_review() -> None:
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
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["theorem_linkage_obligation_index_prepared"] == "yes"
    assert consumed["proof_obligation_row_count"] == "13"
    assert consumed["obligation_rows_discharged"] == "no"
    assert consumed["no_gap_discharged"] == "yes"
    assert consumed["no_rule_promoted"] == "yes"
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
    assert active["theorem_linkage_obligation_index_prepared"] == "yes"
    assert active["proof_obligation_row_count"] == "13"
    assert active["obligation_rows_discharged"] == "no"
    assert active["master_action_promoted"] == "no"


def test_ck_family_theorem_linkage_obligation_index_mirrors() -> None:
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
        INDEX_RESULT,
        PACKET_CLASSIFICATION,
        "CKFamilyTheoremLinkageObligationIndex",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_OUTCOME_v0",
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_NONCLAIM_BOUNDARY_v0",
        "C_source^phi",
        "C_bridge^phi",
        "C_transport^phi",
        "C_source^A",
        "C_bridge^A",
        "C_transport^A",
        "psi-A current route",
        "psi-A current conservation",
        "psi-A sourced gauge route",
        "psi-A gauge-sector exchange",
        "psi-A matter-sector exchange",
        "psi-A total conservation",
        "C_exchange^{Apsi}",
        "THEOREM_LINKED_CONDITIONAL",
        "ROUTE_CONSTRUCTED_UNDER_ASSUMPTIONS",
        "POLICY_LINKED_ADMISSIBILITY_ONLY",
        "SUPPLIED_ASSUMPTION_DEPENDENT",
        "NOT_FUNCTIONALIZED",
        "NOT_VARIED",
        "OPEN_PROOF_DEBT",
        "no C_k action embedding",
        "no C_k action variation",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_ck_family_theorem_linkage_obligation_index_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_ck_family_theorem_linkage_obligation_index_gate.py"
    )
