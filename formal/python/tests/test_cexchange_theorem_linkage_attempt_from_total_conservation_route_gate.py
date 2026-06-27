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
from formal.python.tools.cexchange_theorem_linkage_attempt_from_total_conservation_route_report import (
    ACCEPTED_PACKET_FINDINGS,
    ATTEMPT_TYPE,
    BASIS,
    BLOCKED_CLAIMS,
    CLAIM_BOUNDARY,
    C_EXCHANGE_RESIDUAL_DEFINITION,
    C_EXCHANGE_TARGET_CONCLUSION,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    GOAL,
    INPUT_ROUTE,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LIKELY_FOLLOW_ON_TARGET,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PROOF_STYLE,
    RULE_FAMILY,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    SCOPE_REVIEW_PATH,
    STRICT_PACKET_RESULT,
    TARGET_RULE,
    THEOREM_TARGET_ID,
    THEOREM_TARGET_STATEMENT,
    TOP_OBLIGATION,
    TOP_OBLIGATION_PACKET_SCOPE,
    TOP_OBLIGATION_ROW_ID,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_DEFINITION,
    build_cexchange_theorem_linkage_attempt_from_total_conservation_route,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "cexchange_theorem_linkage_attempt_from_total_conservation_route_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
CURRENT_TARGET_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "CurrentTarget.lean"
)
QFTGR_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
CURRENT_AUTHORITY_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
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


def test_cexchange_theorem_linkage_attempt_packet_files_exist() -> None:
    for path in [
        SCOPE_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_cexchange_theorem_linkage_attempt_packet_prepares_route() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["artifact_id"] == SCHEMA_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == OUTCOME_ID
    assert packet["strict_packet_result"] == STRICT_PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["likely_follow_on_target_after_review"] == LIKELY_FOLLOW_ON_TARGET
    assert build_cexchange_theorem_linkage_attempt_from_total_conservation_route() == packet


def test_cexchange_theorem_linkage_attempt_packet_records_exact_logical_shape() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["accepted_packet_findings"] == ACCEPTED_PACKET_FINDINGS
    assert packet["top_obligation"] == TOP_OBLIGATION
    assert packet["top_obligation_row_id"] == TOP_OBLIGATION_ROW_ID
    assert packet["top_obligation_packet_scope"] == TOP_OBLIGATION_PACKET_SCOPE
    assert packet["attempt_type"] == ATTEMPT_TYPE
    assert packet["input_route"] == INPUT_ROUTE
    assert packet["target_rule"] == TARGET_RULE
    assert packet["proof_style"] == PROOF_STYLE
    assert packet["claim_boundary"] == CLAIM_BOUNDARY
    assert packet["basis"] == BASIS
    assert packet["rule_family"] == RULE_FAMILY
    assert packet["goal"] == GOAL
    assert packet["theorem_target_id"] == THEOREM_TARGET_ID
    assert packet["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert packet["total_stress_energy_definition"] == TOTAL_STRESS_ENERGY_DEFINITION
    assert (
        packet["total_stress_energy_conservation_identity"]
        == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    assert packet["C_exchange_residual_definition"] == C_EXCHANGE_RESIDUAL_DEFINITION
    assert packet["C_exchange_target_conclusion"] == C_EXCHANGE_TARGET_CONCLUSION
    assert packet["plain_meaning"] == PLAIN_MEANING

    rows = packet["attempt_route_rows"]
    assert len(rows) == 1
    assert rows[0]["row_id"] == THEOREM_TARGET_ID
    assert rows[0]["attempt_type"] == ATTEMPT_TYPE
    assert rows[0]["input_route"] == INPUT_ROUTE
    assert rows[0]["target_rule"] == TARGET_RULE
    assert rows[0]["proof_style"] == PROOF_STYLE
    assert rows[0]["given"] == [
        TOTAL_STRESS_ENERGY_DEFINITION,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        C_EXCHANGE_RESIDUAL_DEFINITION,
    ]
    assert rows[0]["therefore"] == C_EXCHANGE_TARGET_CONCLUSION
    assert rows[0]["proof_attempt_executed"] is False
    assert rows[0]["theorem_discharged"] is False
    assert rows[0]["rule_promoted"] is False


def test_cexchange_theorem_linkage_attempt_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    assert packet["blocked_claim_count"] == 16
    assert packet["gap_count"] == 8
    assert packet["open_gap_count"] == 8
    assert packet["closed_gap_count"] == 0
    assert packet["selected_proof_target"] == THEOREM_TARGET_ID
    assert packet["proof_target_selected"] is True
    assert packet["theorem_row_selected"] is True

    for key in [
        "definition_linkage_route_indexed",
        "definition_linkage_attempt_prepared",
        "total_conservation_to_cexchange_zero_linkage_target_indexed",
        "attempt_preparation_packet_prepared",
        "attempt_execution_authorized_after_review_only",
        "all_gaps_remain_open",
        "no_gap_discharged",
        "no_gap_closed",
    ]:
        assert packet[key] is True, key

    for key in [
        "proof_execution_authorized",
        "proof_target_execution_authorized",
        "proof_attempt_executed",
        "proof_debt_reduced",
        "proof_debt_discharged",
        "theorem_row_selected_for_execution",
        "theorem_discharged",
        "theorem_linkage_completed",
        "theorem_linkage_proof_attempt_authorized",
        "rule_promoted",
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
        assert packet[key] is False, key

    for phrase in [
        "prepares only the C_exchange definitional theorem-linkage attempt",
        "accepted psi-A total stress-energy conservation route",
        "definition expansion plus the accepted total-conservation route",
        "does not execute the proof",
        "discharge the theorem",
        "promote any C_k rule",
        "embed C_k in an action",
        "vary C_k",
        "select a multiplier route",
        "select a penalty route",
        "claim empirical validation",
        "promote the master action",
        "not a promoted final law",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_cexchange_theorem_linkage_attempt_packet_records_lean_status() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_PACKET
    assert (
        packet["full_toeformal_aggregate_status_for_packet"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
    )
    assert (
        packet["scoped_lean_targets_status_for_packet"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
    )
    assert packet["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(packet)


def test_cexchange_theorem_linkage_attempt_packet_rotates_to_result_review() -> None:
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
    assert consumed["strict_packet_result"] == STRICT_PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["attempt_type"] == ATTEMPT_TYPE
    assert consumed["proof_style"] == PROOF_STYLE
    assert consumed["theorem_target_id"] == THEOREM_TARGET_ID
    assert consumed["selected_proof_target"] == THEOREM_TARGET_ID
    assert consumed["proof_target_selected"] == "yes"
    assert consumed["theorem_row_selected"] == "yes"
    assert consumed["proof_attempt_executed"] == "no"
    assert consumed["theorem_discharged"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    review_result = (
        "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_RESULT_REVIEW_"
        "ACCEPTS_DEFINITIONAL_LINKAGE_ROUTE_PREPARATION_NO_THEOREM_DISCHARGE_OR_"
        "CK_RULE_PROMOTION"
    )
    execution_target = (
        "execute_cexchange_theorem_linkage_attempt_from_total_conservation_route"
    )
    review = _workstream(registry, NEXT_TARGET)
    assert review["status"] == "paused"
    assert review["workstream_id"] == NEXT_TARGET
    assert review["authorization_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "CExchangeTheoremLinkageAttemptFromTotalConservationRouteResultReview.lean"
    )
    assert review["review_result"] == review_result
    assert review["result_token"] == review_result
    assert review["selected_next_target"] == execution_target
    assert (
        review["selected_next_target_kind"]
        == "cexchange_theorem_linkage_attempt_from_total_conservation_route_execution"
    )
    assert review["attempt_type"] == ATTEMPT_TYPE
    assert review["proof_style"] == PROOF_STYLE
    assert review["theorem_target_id"] == THEOREM_TARGET_ID
    assert review["selected_proof_target"] == THEOREM_TARGET_ID
    assert review["proof_target_selected"] == "yes"
    assert review["theorem_row_selected"] == "yes"
    assert review["proof_attempt_executed"] == "no"
    assert review["theorem_discharged"] == "no"
    assert review["rule_promoted"] == "no"
    assert review["master_action_promoted"] == "no"

    active = _workstream(registry, execution_target)
    assert active["status"] == "active"
    assert active["workstream_id"] == execution_target
    assert active["proof_execution_authorized"] == "yes"
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["rule_promoted"] == "no"


def test_cexchange_theorem_linkage_attempt_packet_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_PATH,
            CURRENT_TARGET_PATH,
            CURRENT_AUTHORITY_PATH,
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
        STRICT_PACKET_RESULT,
        PACKET_CLASSIFICATION,
        "CExchangeTheoremLinkageAttemptFromTotalConservationRoute",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_FOLLOW_ON_TARGET,
        ATTEMPT_TYPE,
        INPUT_ROUTE,
        TARGET_RULE,
        PROOF_STYLE,
        CLAIM_BOUNDARY,
        TOP_OBLIGATION,
        TOP_OBLIGATION_ROW_ID,
        BASIS,
        RULE_FAMILY,
        GOAL,
        THEOREM_TARGET_ID,
        THEOREM_TARGET_STATEMENT,
        PLAIN_MEANING,
        TOTAL_STRESS_ENERGY_DEFINITION,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        C_EXCHANGE_RESIDUAL_DEFINITION,
        C_EXCHANGE_TARGET_CONCLUSION,
        LEAN_STATUS_WORDING_FOR_PACKET,
        "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_OUTCOME_v0",
        "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_NONCLAIM_BOUNDARY_v0",
        "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_PROOF_STYLE_v0",
        "no theorem discharge",
        "no C_k rule promotion",
        "no action embedding",
        "no variation",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no empirical validation",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_cexchange_theorem_linkage_attempt_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_cexchange_theorem_linkage_attempt_from_total_conservation_route_gate.py"
    )
