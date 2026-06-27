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
    ATTEMPT_PREPARATION_RESULT,
    ATTEMPT_WATCH_ITEMS,
    DEFAULT_OUT as ATTEMPT_PACKET_PATH,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    STRICT_ATTEMPT_PREPARATION_RESULT,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    ATTEMPT_TYPE,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    EXPANDED_CANCELLATION_CHAIN,
    EXPANDED_CANCELLATION_CHAIN_STATEMENT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    GAUGE_EXCHANGE_ROUTE,
    INPUT_ROUTE,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    MATTER_EXCHANGE_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PROOF_STYLE,
    REVIEW_BLOCKED_CLAIMS,
    REVIEW_RESULT,
    ROUTE_STEPS,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_EXECUTION_OUTCOME,
    SUGGESTED_EXECUTION_OUTCOME,
    THEOREM_TARGET_STATEMENT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_STRESS_ENERGY_DEFINITION,
    build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result_review_report.py"
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


def test_psi_A_total_conservation_attempt_result_review_files_exist() -> None:
    for path in [
        ATTEMPT_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_total_conservation_attempt_result_review_accepts_preparation() -> None:
    review = _json(DEFAULT_OUT)

    assert review["artifact_id"] == SCHEMA_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_result"] == OUTCOME_ID
    assert review["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["suggested_execution_outcome"] == SUGGESTED_EXECUTION_OUTCOME
    assert (
        review["strict_suggested_execution_outcome"]
        == STRICT_SUGGESTED_EXECUTION_OUTCOME
    )
    assert (
        build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result_review()
        == review
    )


def test_psi_A_total_conservation_attempt_result_review_preserves_route() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["attempt_type"] == ATTEMPT_TYPE
    assert review["input_route"] == INPUT_ROUTE
    assert review["target_rule"] == TOTAL_CONSERVATION_CONCLUSION
    assert review["proof_style"] == PROOF_STYLE
    assert review["claim_boundary"] == "theorem-linkage only, not physics closure"
    assert review["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review["gauge_exchange_route"] == GAUGE_EXCHANGE_ROUTE
    assert review["matter_exchange_route"] == MATTER_EXCHANGE_ROUTE
    assert review["total_stress_energy_definition"] == TOTAL_STRESS_ENERGY_DEFINITION
    assert review["expanded_cancellation_chain"] == EXPANDED_CANCELLATION_CHAIN
    assert review["route_steps"] == ROUTE_STEPS
    assert review["watch_items"] == ATTEMPT_WATCH_ITEMS
    assert review["plain_meaning"] == PLAIN_MEANING
    assert review["theorem_target_shape"]["given"] == [
        GAUGE_EXCHANGE_ROUTE,
        MATTER_EXCHANGE_ROUTE,
        TOTAL_STRESS_ENERGY_DEFINITION,
    ]
    assert review["theorem_target_shape"]["then"] == TOTAL_CONSERVATION_CONCLUSION


def test_psi_A_total_conservation_attempt_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)

    assert review["blocked_claims"] == REVIEW_BLOCKED_CLAIMS
    assert review["blocked_claim_count"] == 15
    assert review["gap_count"] == 8
    assert review["open_gap_count"] == 8
    assert review["closed_gap_count"] == 0
    assert review["proof_target_selected"] is True
    assert review["theorem_row_selected"] is True
    assert review["theorem_row_selected_for_execution"] is True
    assert review["proof_execution_authorized_by_review_for_next_target"] is True
    assert review["theorem_linkage_proof_attempt_authorized_for_next_target"] is True

    for key in [
        "attempt_packet_consumed",
        "exchange_cancellation_route_prepared",
        "gauge_sector_exchange_input_preserved",
        "matter_sector_exchange_input_preserved",
        "total_stress_energy_definition_preserved",
        "watch_items_preserved",
        "execution_target_selected_after_review",
        "attempt_execution_authorized_after_review_only",
        "attempt_execution_authorized_as_next_target",
        "all_gaps_remain_open",
        "no_gap_discharged",
        "no_gap_closed",
    ]:
        assert review[key] is True, key

    for key in [
        "proof_execution_authorized",
        "proof_target_execution_authorized",
        "proof_attempt_executed",
        "proof_debt_reduced",
        "proof_debt_discharged",
        "theorem_discharged",
        "theorem_linkage_completed",
        "theorem_linkage_obligation_discharged",
        "theorem_linkage_proof_attempt_authorized",
        "review_executes_attempt",
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "multiplier_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_claimed",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert review[key] is False, key


def test_psi_A_total_conservation_attempt_result_review_records_lean_status() -> None:
    review = _json(DEFAULT_OUT)

    assert review["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_REVIEW
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


def test_psi_A_total_conservation_attempt_result_review_rotates_to_execution() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert registry["PREVIOUS_LIVE_NEXT_TARGET_v0"] == CONSUMED_TARGET
    assert registry["CURRENT_LIVE_NEXT_TARGET_v0"] == NEXT_TARGET
    assert registry["CURRENT_LIVE_TARGET_EVIDENCE_v0"] == evidence
    assert registry["CURRENT_LIVE_TARGET_REPORT_v0"] == _rel(DEFAULT_OUT)
    assert registry["CURRENT_LIVE_TARGET_OUTCOME_v0"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET not in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    attempt = workstream(
        "prepare_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes",
        registry,
    )
    assert attempt["status"] == "paused"
    assert attempt["authorization_evidence"] == _rel(ATTEMPT_LEAN_PACKET_PATH)
    assert attempt["report"] == _rel(ATTEMPT_PACKET_PATH)
    assert attempt["attempt_preparation_result"] == ATTEMPT_PREPARATION_RESULT
    assert (
        attempt["strict_attempt_preparation_result"]
        == STRICT_ATTEMPT_PREPARATION_RESULT
    )

    reviewed = workstream(CONSUMED_TARGET, registry)
    assert reviewed["status"] == "paused"
    assert reviewed["authorization_evidence"] == evidence
    assert reviewed["report"] == _rel(DEFAULT_OUT)
    assert reviewed["review_result"] == OUTCOME_ID
    assert reviewed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert reviewed["selected_next_target"] == NEXT_TARGET
    assert reviewed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert reviewed["proof_attempt_executed"] == "no"
    assert reviewed["theorem_discharged"] == "no"
    assert reviewed["rule_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == NEXT_TARGET
    assert active["active_lane"] == NEXT_TARGET
    assert active["authorization_evidence"] == evidence
    assert active["authorized_next_strict_target"] == NEXT_TARGET
    assert active["consumed_target"] == CONSUMED_TARGET
    assert active["packet_result"] == OUTCOME_ID
    assert active["review_result"] == OUTCOME_ID
    assert active["execution_result"] == "PENDING"
    assert active["suggested_execution_outcome"] == SUGGESTED_EXECUTION_OUTCOME
    assert (
        active["strict_suggested_execution_outcome"]
        == STRICT_SUGGESTED_EXECUTION_OUTCOME
    )
    assert active["proof_execution_authorized"] == "yes"
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_total_conservation_attempt_result_review_mirrors() -> None:
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
        STRICT_REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        "PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutesResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_EXECUTION_OUTCOME,
        STRICT_SUGGESTED_EXECUTION_OUTCOME,
        ATTEMPT_TYPE,
        INPUT_ROUTE,
        TOTAL_CONSERVATION_CONCLUSION,
        PROOF_STYLE,
        THEOREM_TARGET_STATEMENT,
        PLAIN_MEANING,
        GAUGE_EXCHANGE_ROUTE,
        MATTER_EXCHANGE_ROUTE,
        TOTAL_STRESS_ENERGY_DEFINITION,
        EXPANDED_CANCELLATION_CHAIN_STATEMENT,
        LEAN_STATUS_WORDING_FOR_REVIEW,
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "no proof execution",
        "no theorem discharge",
        "no C_k rule promotion",
        "no action embedding",
        "no variation",
        "no seam closure",
        "no empirical validation",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_psi_A_total_conservation_attempt_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result_review_gate.py"
    )
