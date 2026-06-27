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
from formal.python.tools.cexchange_theorem_linkage_attempt_from_total_conservation_route_execution_report import (
    ATTEMPT_TYPE,
    BASIS,
    BLOCKED_CLAIMS,
    C_EXCHANGE_RESIDUAL_DEFINITION,
    C_EXCHANGE_TARGET_CONCLUSION,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    EXECUTION_FINDINGS,
    EXECUTION_RESULT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION,
    GOAL,
    INPUT_ROUTE,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_EXECUTION,
    LEAN_THEOREM_NAME,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PROOF_STYLE,
    RESULT_REVIEW_PATH,
    RULE_FAMILY,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION,
    STRICT_EXECUTION_RESULT,
    TARGET_RULE,
    THEOREM_TARGET_ID,
    THEOREM_TARGET_STATEMENT,
    TOP_OBLIGATION,
    TOP_OBLIGATION_PACKET_SCOPE,
    TOP_OBLIGATION_ROW_ID,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_DEFINITION,
    build_cexchange_theorem_linkage_attempt_from_total_conservation_route_execution,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "cexchange_theorem_linkage_attempt_from_total_conservation_route_execution_report.py"
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


def test_cexchange_theorem_linkage_attempt_execution_files_exist() -> None:
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


def test_cexchange_theorem_linkage_attempt_execution_report_matches_builder() -> None:
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
    assert execution["consumed_target"] == CONSUMED_TARGET
    assert execution["selected_next_target"] == NEXT_TARGET
    assert execution["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert (
        build_cexchange_theorem_linkage_attempt_from_total_conservation_route_execution()
        == execution
    )


def test_cexchange_theorem_linkage_attempt_execution_constructs_bridge() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["execution_findings"] == EXECUTION_FINDINGS
    assert execution["top_obligation"] == TOP_OBLIGATION
    assert execution["top_obligation_row_id"] == TOP_OBLIGATION_ROW_ID
    assert execution["top_obligation_packet_scope"] == TOP_OBLIGATION_PACKET_SCOPE
    assert execution["attempt_type"] == ATTEMPT_TYPE
    assert execution["input_route"] == INPUT_ROUTE
    assert execution["target_rule"] == TARGET_RULE
    assert execution["proof_style"] == PROOF_STYLE
    assert execution["basis"] == BASIS
    assert execution["rule_family"] == RULE_FAMILY
    assert execution["goal"] == GOAL
    assert execution["theorem_target_id"] == THEOREM_TARGET_ID
    assert execution["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert execution["total_stress_energy_definition"] == TOTAL_STRESS_ENERGY_DEFINITION
    assert (
        execution["total_stress_energy_conservation_identity"]
        == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    assert execution["C_exchange_residual_definition"] == C_EXCHANGE_RESIDUAL_DEFINITION
    assert execution["C_exchange_target_conclusion"] == C_EXCHANGE_TARGET_CONCLUSION
    assert execution["plain_meaning"] == PLAIN_MEANING
    assert execution["lean_theorem_name"] == LEAN_THEOREM_NAME
    assert execution["C_exchange_zero_derived"] is True
    assert execution["definition_linkage_constructed"] is True
    assert execution["top_theorem_linkage_obligation_locally_reduced"] is True
    assert execution["theorem_target_shape"]["given"] == [
        TOTAL_STRESS_ENERGY_DEFINITION,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        C_EXCHANGE_RESIDUAL_DEFINITION,
    ]
    assert execution["theorem_target_shape"]["therefore"] == C_EXCHANGE_TARGET_CONCLUSION


def test_cexchange_theorem_linkage_attempt_execution_preserves_boundaries() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["blocked_claims"] == BLOCKED_CLAIMS
    assert execution["blocked_claim_count"] == 16
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
    assert execution["C_exchange_admissibility_status"] == "admissibility-only"

    for key in [
        "rule_promoted",
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
    ]:
        assert execution[key] is False, key


def test_cexchange_theorem_linkage_attempt_execution_records_lean_status() -> None:
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


def test_cexchange_theorem_linkage_attempt_execution_rotates_to_result_review() -> None:
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
    assert NEXT_TARGET not in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == _rel(DEFAULT_OUT)
    assert consumed["execution_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["proof_attempt_executed"] == "yes"
    assert consumed["theorem_discharged"] == "yes"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == NEXT_TARGET
    assert active["active_lane"] == NEXT_TARGET
    assert active["authorization_evidence"] == evidence
    assert active["authorized_next_strict_target"] == NEXT_TARGET
    assert active["consumed_target"] == CONSUMED_TARGET
    assert active["packet_result"] == "PENDING"
    assert active["review_result"] == "PENDING"
    assert active["execution_result"] == OUTCOME_ID
    assert active["outcome_id"] == OUTCOME_ID
    assert active["result_token"] == OUTCOME_ID
    assert active["selected_next_target"] == NEXT_TARGET
    assert active["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert active["proof_attempt_executed"] == "yes"
    assert active["theorem_discharged"] == "yes"
    assert active["C_exchange_zero_derived"] == "yes"
    assert active["definition_linkage_constructed"] == "yes"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_cexchange_theorem_linkage_attempt_execution_mirrors() -> None:
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
        "CExchangeTheoremLinkageAttemptFromTotalConservationRouteExecution",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        ATTEMPT_TYPE,
        INPUT_ROUTE,
        TARGET_RULE,
        PROOF_STYLE,
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
        LEAN_THEOREM_NAME,
        LEAN_STATUS_WORDING_FOR_EXECUTION,
        "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_EXECUTION_OUTCOME_v0",
        "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_EXECUTION_NONCLAIM_BOUNDARY_v0",
        "definitional linkage constructed",
        "C_exchange zero follows",
        "no C_k rule promotion",
        "no action embedding",
        "no variation",
        "no seam closure",
        "no empirical validation",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_cexchange_theorem_linkage_attempt_execution_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_cexchange_theorem_linkage_attempt_from_total_conservation_route_execution_gate.py"
    )
