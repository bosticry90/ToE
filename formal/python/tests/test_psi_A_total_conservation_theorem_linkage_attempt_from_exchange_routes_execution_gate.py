from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    active_workstream,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_historical_target_recorded,
    assert_public_surfaces_match_registry,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution_report import (
    ATTEMPT_WATCH_ITEMS,
    CONSUMED_EXECUTION_TARGET,
    DEFAULT_OUT,
    EXECUTION_BLOCKED_CLAIMS,
    EXECUTION_FINDINGS,
    EXECUTION_RESULT,
    EXPANDED_CANCELLATION_CHAIN,
    EXPANDED_CANCELLATION_CHAIN_STATEMENT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION,
    GAUGE_EXCHANGE_CONCLUSION,
    GAUGE_EXCHANGE_ROUTE,
    INPUT_ROUTE,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_EXECUTION,
    LEAN_THEOREM_NAME,
    MATTER_EXCHANGE_CONCLUSION,
    MATTER_EXCHANGE_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PROOF_STYLE,
    RESULT_REVIEW_PATH,
    ROUTE_STEPS,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION,
    STRICT_EXECUTION_RESULT,
    THEOREM_TARGET_STATEMENT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_STRESS_ENERGY_DEFINITION,
    build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_closeout_report import (
    DEFAULT_OUT as CLOSEOUT_OUT,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    NEXT_TARGET as CLOSEOUT_REVIEW_TARGET,
    OUTCOME_ID as CLOSEOUT_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution_report.py"
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


def test_psi_A_total_conservation_attempt_execution_files_exist() -> None:
    for path in [
        RESULT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_total_conservation_attempt_execution_report_matches_builder() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["artifact_id"] == SCHEMA_ID
    assert execution["schema_id"] == SCHEMA_ID
    assert execution["packet_id"] == PACKET_ID
    assert execution["prepared"] is True
    assert execution["accepted"] is True
    assert execution["executed"] is True
    assert execution["outcome_id"] == OUTCOME_ID
    assert execution["packet_result"] == EXECUTION_RESULT
    assert execution["execution_result"] == EXECUTION_RESULT
    assert execution["strict_execution_result"] == STRICT_EXECUTION_RESULT
    assert execution["packet_classification"] == PACKET_CLASSIFICATION
    assert execution["consumed_target"] == CONSUMED_EXECUTION_TARGET
    assert execution["selected_next_target"] == NEXT_TARGET
    assert execution["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert (
        build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution()
        == execution
    )


def test_psi_A_total_conservation_attempt_execution_constructs_cancellation() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["execution_findings"] == EXECUTION_FINDINGS
    assert execution["attempt_type"] == "exchange-cancellation theorem-linkage attempt"
    assert execution["input_route"] == INPUT_ROUTE
    assert execution["target_rule"] == TOTAL_CONSERVATION_CONCLUSION
    assert execution["proof_style"] == PROOF_STYLE
    assert execution["claim_boundary"] == "theorem-linkage only, not physics closure"
    assert execution["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert execution["gauge_exchange_route"] == GAUGE_EXCHANGE_ROUTE
    assert execution["matter_exchange_route"] == MATTER_EXCHANGE_ROUTE
    assert execution["gauge_exchange_conclusion"] == GAUGE_EXCHANGE_CONCLUSION
    assert execution["matter_exchange_conclusion"] == MATTER_EXCHANGE_CONCLUSION
    assert execution["total_stress_energy_definition"] == TOTAL_STRESS_ENERGY_DEFINITION
    assert execution["total_conservation_conclusion"] == TOTAL_CONSERVATION_CONCLUSION
    assert execution["expanded_cancellation_chain"] == EXPANDED_CANCELLATION_CHAIN
    assert (
        execution["expanded_cancellation_chain_statement"]
        == EXPANDED_CANCELLATION_CHAIN_STATEMENT
    )
    assert execution["route_steps"] == ROUTE_STEPS
    assert execution["watch_items"] == ATTEMPT_WATCH_ITEMS
    assert execution["plain_meaning"] == PLAIN_MEANING
    assert execution["lean_theorem_name"] == LEAN_THEOREM_NAME
    assert execution["exchange_cancellation_route_constructed"] is True
    assert execution["total_conservation_derived"] is True
    assert execution["local_theorem_linkage_reduced"] is True
    assert execution["theorem_target_shape"]["given"] == [
        GAUGE_EXCHANGE_ROUTE,
        MATTER_EXCHANGE_ROUTE,
        TOTAL_STRESS_ENERGY_DEFINITION,
    ]
    assert execution["theorem_target_shape"]["therefore"] == TOTAL_CONSERVATION_CONCLUSION


def test_psi_A_total_conservation_attempt_execution_preserves_boundaries() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["blocked_claims"] == EXECUTION_BLOCKED_CLAIMS
    assert execution["blocked_claim_count"] == 12
    assert execution["gap_count"] == 8
    assert execution["open_gap_count"] == 8
    assert execution["closed_gap_count"] == 0
    assert execution["proof_execution_authorized"] is True
    assert execution["proof_target_execution_authorized"] is True
    assert execution["proof_attempt_executed"] is True
    assert execution["proof_debt_reduced"] is True
    assert execution["proof_debt_discharged"] is False
    assert execution["theorem_discharged"] is True
    assert execution["theorem_linkage_completed"] is True
    assert execution["theorem_linkage_proof_attempt_authorized"] is True
    assert execution["theorem_linkage_obligation_discharged"] is True

    for key in [
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
        assert execution[key] is False, key


def test_psi_A_total_conservation_attempt_execution_records_lean_status() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_EXECUTION
    assert (
        execution["full_toeformal_aggregate_status_for_execution"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
    )
    assert (
        execution["scoped_lean_targets_status_for_execution"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
    )
    assert execution["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(execution)


def test_psi_A_total_conservation_attempt_execution_rotates_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    result_review_evidence = (
        "formal/toe_formal/ToeFormal/Derivation/"
        "PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutesExecutionResultReview.lean"
    )
    result_review_report = (
        "formal/docs/release/"
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
        "EXECUTION_RESULT_REVIEW_20260627_v0.json"
    )
    result_review_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
        "RESULT_REVIEW_ACCEPTS_EXCHANGE_CANCELLATION_CONSTRUCTED_NO_CK_RULE_"
        "PROMOTION_OR_MASTER_ACTION_PROMOTION"
    )
    closeout_target = (
        "prepare_psi_A_total_conservation_theorem_linkage_obligation_closeout"
    )
    closeout_review_evidence = _rel(CLOSEOUT_LEAN_PACKET_PATH)
    closeout_review_report = _rel(CLOSEOUT_OUT)

    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_EXECUTION_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert not is_current
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert registry["PREVIOUS_LIVE_NEXT_TARGET_v0"] == closeout_target
    assert registry["CURRENT_LIVE_NEXT_TARGET_v0"] == CLOSEOUT_REVIEW_TARGET
    assert registry["ACTIVE_LANE_v0"] == CLOSEOUT_REVIEW_TARGET
    assert registry["CURRENT_LIVE_TARGET_EVIDENCE_v0"] == closeout_review_evidence
    assert registry["CURRENT_LIVE_TARGET_REPORT_v0"] == closeout_review_report
    assert registry["CURRENT_LIVE_TARGET_OUTCOME_v0"] == CLOSEOUT_RESULT
    assert CONSUMED_EXECUTION_TARGET in registry["completed_targets"]
    assert CONSUMED_EXECUTION_TARGET in registry["consumed_targets"]
    assert CONSUMED_EXECUTION_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["paused_lanes"]
    assert closeout_target in registry["paused_lanes"]
    assert CLOSEOUT_REVIEW_TARGET not in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CLOSEOUT_REVIEW_TARGET in registry["next_strict_target_coverage"]

    executed = _workstream(registry, CONSUMED_EXECUTION_TARGET)
    assert executed["status"] == "paused"
    assert executed["authorization_evidence"] == evidence
    assert executed["report"] == _rel(DEFAULT_OUT)
    assert executed["execution_result"] == OUTCOME_ID
    assert executed["strict_execution_result"] == STRICT_EXECUTION_RESULT
    assert executed["selected_next_target"] == NEXT_TARGET
    assert executed["proof_attempt_executed"] == "yes"
    assert executed["theorem_discharged"] == "yes"
    assert executed["rule_promoted"] == "no"
    assert executed["master_action_promoted"] == "no"

    reviewed = _workstream(registry, NEXT_TARGET)
    assert reviewed["status"] == "paused"
    assert reviewed["authorization_evidence"] == result_review_evidence
    assert reviewed["report"] == result_review_report
    assert reviewed["execution_result"] == OUTCOME_ID
    assert reviewed["review_result"] == result_review_outcome
    assert reviewed["selected_next_target"] == closeout_target
    assert reviewed["review_executes_attempt"] == "no"
    assert reviewed["rule_promoted"] == "no"

    closeout = _workstream(registry, closeout_target)
    assert closeout["status"] == "paused"
    assert closeout["authorization_evidence"] == closeout_review_evidence
    assert closeout["report"] == closeout_review_report
    assert closeout["closeout_result"] == CLOSEOUT_RESULT
    assert closeout["selected_next_target"] == CLOSEOUT_REVIEW_TARGET
    assert closeout["local_psi_A_total_conservation_obligation_closed"] == "yes"
    assert closeout["rule_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == CLOSEOUT_REVIEW_TARGET
    assert active["active_lane"] == CLOSEOUT_REVIEW_TARGET
    assert active["authorization_evidence"] == closeout_review_evidence
    assert active["authorized_next_strict_target"] == CLOSEOUT_REVIEW_TARGET
    assert active["consumed_target"] == closeout_target
    assert active["packet_result"] == CLOSEOUT_RESULT
    assert active["closeout_result"] == CLOSEOUT_RESULT
    assert active["review_result"] == "PENDING"
    assert active["proof_attempt_executed"] == "yes"
    assert active["theorem_discharged"] == "yes"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_total_conservation_attempt_execution_mirrors() -> None:
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
        STRICT_EXECUTION_RESULT,
        PACKET_CLASSIFICATION,
        "PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutesExecution",
        CONSUMED_EXECUTION_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        INPUT_ROUTE,
        TOTAL_CONSERVATION_CONCLUSION,
        PROOF_STYLE,
        THEOREM_TARGET_STATEMENT,
        PLAIN_MEANING,
        GAUGE_EXCHANGE_ROUTE,
        MATTER_EXCHANGE_ROUTE,
        TOTAL_STRESS_ENERGY_DEFINITION,
        EXPANDED_CANCELLATION_CHAIN_STATEMENT,
        LEAN_STATUS_WORDING_FOR_EXECUTION,
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_EXECUTION_OUTCOME_v0",
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_EXECUTION_NONCLAIM_BOUNDARY_v0",
        "psi_A_total_conservation_from_exchange_cancellation",
        "total conservation derived from accepted gauge/matter exchange halves",
        "no C_k rule promotion",
        "no C_k action embedding",
        "no C_k action variation",
        "no seam closure",
        "no empirical validation",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_psi_A_total_conservation_attempt_execution_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution_gate.py"
    )
