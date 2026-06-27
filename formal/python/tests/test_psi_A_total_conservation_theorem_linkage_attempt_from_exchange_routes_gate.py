from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    active_workstream,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
    workstream,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_report import (
    ACCEPTED_PACKET_FINDINGS,
    ATTEMPT_PREPARATION_RESULT,
    ATTEMPT_WATCH_ITEMS,
    BLOCKED_CLAIMS,
    DEFAULT_OUT,
    EXPANDED_CANCELLATION_CHAIN,
    EXPANDED_CANCELLATION_CHAIN_STATEMENT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    GAUGE_EXCHANGE_ROUTE,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LIKELY_POST_REVIEW_TARGET,
    MATTER_EXCHANGE_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    ROUTE_STEPS,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_ATTEMPT_PREPARATION_RESULT,
    THEOREM_TARGET_STATEMENT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_STRESS_ENERGY_DEFINITION,
    build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_packet_result_review_report import (
    DEFAULT_OUT as REVIEW_OUT,
    LEAN_PACKET_PATH as REVIEW_LEAN_PACKET_PATH,
    OUTCOME_ID as REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_report.py"
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


def consumed_target() -> str:
    return "prepare_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes"


def review_target() -> str:
    return "review_psi_A_total_conservation_theorem_linkage_obligation_packet_result"


def test_psi_A_total_conservation_attempt_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_total_conservation_attempt_indexes_exchange_cancellation_route() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["artifact_id"] == SCHEMA_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == ATTEMPT_PREPARATION_RESULT
    assert packet["attempt_preparation_result"] == ATTEMPT_PREPARATION_RESULT
    assert (
        packet["strict_attempt_preparation_result"]
        == STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == consumed_target()
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["likely_post_review_target"] == LIKELY_POST_REVIEW_TARGET
    assert packet["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert packet["route_steps"] == ROUTE_STEPS
    assert packet["watch_items"] == ATTEMPT_WATCH_ITEMS
    assert packet["accepted_packet_findings"] == ACCEPTED_PACKET_FINDINGS
    assert (
        build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes()
        == packet
    )


def test_psi_A_total_conservation_attempt_preserves_route_and_boundary() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["theorem_shape"] == {
        "given": [
            GAUGE_EXCHANGE_ROUTE,
            MATTER_EXCHANGE_ROUTE,
            TOTAL_STRESS_ENERGY_DEFINITION,
        ],
        "then": TOTAL_CONSERVATION_CONCLUSION,
        "expanded": EXPANDED_CANCELLATION_CHAIN,
        "expanded_statement": EXPANDED_CANCELLATION_CHAIN_STATEMENT,
        "route_steps": ROUTE_STEPS,
        "plain_meaning": PLAIN_MEANING,
    }
    assert packet["expanded_cancellation_chain_statement"] == (
        EXPANDED_CANCELLATION_CHAIN_STATEMENT
    )
    assert packet["watch_items"] == [
        "same F object",
        "same J object",
        "same index placement",
        "same sign convention",
        "same covariant derivative",
        "linearity of nabla over addition",
        "valid T_total definition",
        "shared domain and boundary assumptions",
    ]
    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    assert packet["preparation_executes_proof"] is False
    assert packet["proof_execution_authorized"] is False
    assert packet["proof_attempt_executed"] is False
    assert packet["theorem_discharged"] is False
    assert packet["theorem_linkage_obligation_discharged"] is False
    assert packet["gap_1_through_gap_8_discharged"] is False
    assert packet["rule_promoted"] is False
    assert packet["C_k_action_embedding_claimed"] is False
    assert packet["C_k_action_variation_executed"] is False
    assert packet["full_maxwell_closure_claimed"] is False
    assert packet["em_qft_closure_claimed"] is False
    assert packet["qft_gr_closure_claimed"] is False
    assert packet["gr_qm_closure_claimed"] is False
    assert packet["seam_closure_claim"] is False
    assert packet["empirical_validation_claimed"] is False
    assert packet["master_action_promoted"] is False


def test_psi_A_total_conservation_attempt_records_lean_status() -> None:
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


def test_psi_A_total_conservation_attempt_rotates_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert registry["PREVIOUS_LIVE_NEXT_TARGET_v0"] == consumed_target()
    assert registry["CURRENT_LIVE_NEXT_TARGET_v0"] == NEXT_TARGET
    assert registry["CURRENT_LIVE_TARGET_EVIDENCE_v0"] == evidence
    assert registry["CURRENT_LIVE_TARGET_REPORT_v0"] == _rel(DEFAULT_OUT)
    assert registry["CURRENT_LIVE_TARGET_OUTCOME_v0"] == OUTCOME_ID
    assert consumed_target() in registry["completed_targets"]
    assert consumed_target() in registry["consumed_targets"]
    assert consumed_target() in registry["paused_lanes"]
    assert NEXT_TARGET not in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    prior_review = workstream(review_target(), registry)
    assert prior_review["status"] == "paused"
    assert prior_review["authorization_evidence"] == _rel(REVIEW_LEAN_PACKET_PATH)
    assert prior_review["report"] == _rel(REVIEW_OUT)
    assert prior_review["review_result"] == REVIEW_OUTCOME

    attempt = workstream(consumed_target(), registry)
    assert attempt["status"] == "paused"
    assert attempt["authorization_evidence"] == evidence
    assert attempt["report"] == _rel(DEFAULT_OUT)
    assert attempt["packet_result"] == OUTCOME_ID
    assert attempt["attempt_preparation_result"] == OUTCOME_ID
    assert attempt["strict_attempt_preparation_result"] == (
        STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert attempt["selected_next_target"] == NEXT_TARGET
    assert attempt["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert attempt["watch_items"] == ATTEMPT_WATCH_ITEMS
    assert attempt["proof_attempt_executed"] == "no"
    assert attempt["theorem_discharged"] == "no"
    assert attempt["rule_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == NEXT_TARGET
    assert active["active_lane"] == NEXT_TARGET
    assert active["authorization_evidence"] == evidence
    assert active["authorized_next_strict_target"] == NEXT_TARGET
    assert active["consumed_target"] == consumed_target()
    assert active["packet_result"] == OUTCOME_ID
    assert active["review_result"] == "PENDING"
    assert active["watch_items"] == ATTEMPT_WATCH_ITEMS
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_total_conservation_attempt_mirrors() -> None:
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
        STRICT_ATTEMPT_PREPARATION_RESULT,
        PACKET_CLASSIFICATION,
        "PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutes",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_POST_REVIEW_TARGET,
        THEOREM_TARGET_STATEMENT,
        EXPANDED_CANCELLATION_CHAIN_STATEMENT,
        LEAN_STATUS_WORDING_FOR_PACKET,
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_OUTCOME_v0",
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_NONCLAIM_BOUNDARY_v0",
        "same F object",
        "same J object",
        "same index placement",
        "same sign convention",
        "same covariant derivative",
        "linearity of nabla over addition",
        "valid T_total definition",
        "shared domain and boundary assumptions",
        "no proof execution during preparation",
        "no theorem discharge during preparation",
        "no GAP-1 through GAP-8 discharge",
        "no C_k rule promotion",
        "no C_k action embedding",
        "no C_k variation",
        "no full Maxwell closure",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_total_conservation_attempt_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_gate.py"
    )
