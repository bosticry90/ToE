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
from formal.python.tools.psi_A_interaction_exchange_theorem_linkage_chain_closeout_report import (
    C_EXCHANGE_LINKAGE_CONCLUSION,
    C_EXCHANGE_LINKAGE_DEFINITION,
    C_EXCHANGE_LINKAGE_INPUT,
    CLAIM_BOUNDARY,
    CLOSEOUT_CLAIMS,
    CLOSEOUT_RESULT,
    CLOSEOUT_STATEMENT,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT,
    GAUGE_SECTOR_CONCLUSION,
    GAUGE_SECTOR_INPUT_ROUTE,
    GAUGE_STRESS_DIVERGENCE_IDENTITY,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_CLOSEOUT,
    LIKELY_SELECTOR_AFTER_REVIEW,
    LOCAL_DEPENDENCY_CHAIN,
    MATTER_SECTOR_CONCLUSION,
    MATTER_SECTOR_INPUT_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    NONCLAIMS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    QFTGR_AGGREGATE_PATH,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT,
    SOURCED_MAXWELL_ROUTE,
    STRICT_CLOSEOUT_RESULT,
    SUGGESTED_REVIEW_OUTCOME,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_CONSERVATION_GAUGE_INPUT,
    TOTAL_CONSERVATION_MATTER_INPUT,
    build_psi_A_interaction_exchange_theorem_linkage_chain_closeout,
)
from formal.python.tools.psi_A_interaction_exchange_theorem_linkage_chain_synthesis_result_review_report import (
    DEFAULT_OUT as SYNTHESIS_RESULT_REVIEW_OUT,
    LEAN_PACKET_PATH as SYNTHESIS_RESULT_REVIEW_LEAN_PACKET_PATH,
    OUTCOME_ID as SYNTHESIS_RESULT_REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_interaction_exchange_theorem_linkage_chain_closeout_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
CURRENT_TARGET_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "CurrentTarget.lean"
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


def _workstreams(target: str, registry: dict, *, status: str | None = None) -> list[dict]:
    rows = [
        row
        for row in registry["workstreams"]
        if row.get("workstream_id") == target
        and (status is None or row.get("status") == status)
    ]
    assert rows, f"missing workstream {target!r} with status {status!r}"
    return rows


def test_psi_A_interaction_exchange_chain_closeout_files_exist() -> None:
    for path in [
        SYNTHESIS_RESULT_REVIEW_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_interaction_exchange_chain_closeout_accepts_local_chain() -> None:
    review = _json(SYNTHESIS_RESULT_REVIEW_OUT)
    closeout = _json(DEFAULT_OUT)

    assert review["outcome_id"] == SYNTHESIS_RESULT_REVIEW_OUTCOME
    assert review["selected_next_target"] == CONSUMED_TARGET

    assert closeout["artifact_id"] == SCHEMA_ID
    assert closeout["schema_id"] == SCHEMA_ID
    assert closeout["packet_id"] == PACKET_ID
    assert closeout["prepared"] is True
    assert closeout["accepted"] is True
    assert closeout["closed"] is True
    assert closeout["outcome_id"] == OUTCOME_ID
    assert closeout["closeout_result"] == CLOSEOUT_RESULT
    assert closeout["packet_result"] == OUTCOME_ID
    assert closeout["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
    assert closeout["packet_classification"] == PACKET_CLASSIFICATION
    assert closeout["consumed_target"] == CONSUMED_TARGET
    assert closeout["selected_next_target"] == NEXT_TARGET
    assert closeout["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert closeout["suggested_review_outcome"] == SUGGESTED_REVIEW_OUTCOME
    assert closeout["likely_selector_after_review"] == LIKELY_SELECTOR_AFTER_REVIEW
    assert closeout["closeout_statement"] == CLOSEOUT_STATEMENT
    assert closeout["plain_meaning"] == PLAIN_MEANING
    assert build_psi_A_interaction_exchange_theorem_linkage_chain_closeout() == closeout


def test_psi_A_interaction_exchange_chain_closeout_records_chain() -> None:
    closeout = _json(DEFAULT_OUT)

    assert closeout["closeout_claims"] == CLOSEOUT_CLAIMS
    assert closeout["closeout_claim_count"] == 7
    assert closeout["nonclaims"] == NONCLAIMS
    assert closeout["nonclaim_count"] == 12
    assert closeout["claim_boundary"] == CLAIM_BOUNDARY
    assert closeout["local_dependency_chain"] == LOCAL_DEPENDENCY_CHAIN
    assert closeout["local_dependency_chain_step_count"] == 4
    assert closeout["linkage_chain_count"] == 4
    assert [row["linkage_id"] for row in closeout["linkage_chain"]] == [
        "C_exchange_linkage",
        "total_conservation_linkage",
        "matter_sector_exchange_linkage",
        "gauge_sector_exchange_linkage",
    ]
    assert closeout["C_exchange_linkage_definition"] == C_EXCHANGE_LINKAGE_DEFINITION
    assert closeout["C_exchange_linkage_input"] == C_EXCHANGE_LINKAGE_INPUT
    assert closeout["C_exchange_linkage_conclusion"] == C_EXCHANGE_LINKAGE_CONCLUSION
    assert closeout["total_conservation_gauge_input"] == TOTAL_CONSERVATION_GAUGE_INPUT
    assert closeout["total_conservation_matter_input"] == TOTAL_CONSERVATION_MATTER_INPUT
    assert closeout["total_conservation_conclusion"] == TOTAL_CONSERVATION_CONCLUSION
    assert closeout["matter_sector_input_route"] == MATTER_SECTOR_INPUT_ROUTE
    assert closeout["matter_sector_conclusion"] == MATTER_SECTOR_CONCLUSION
    assert closeout["gauge_sector_input_route"] == GAUGE_SECTOR_INPUT_ROUTE
    assert closeout["gauge_stress_divergence_identity"] == GAUGE_STRESS_DIVERGENCE_IDENTITY
    assert closeout["sourced_maxwell_route"] == SOURCED_MAXWELL_ROUTE
    assert closeout["gauge_sector_conclusion"] == GAUGE_SECTOR_CONCLUSION

    for key in [
        "C_exchange_linkage_locally_closed",
        "total_conservation_linkage_locally_closed",
        "matter_sector_exchange_linkage_locally_closed",
        "gauge_sector_exchange_linkage_locally_closed",
        "dependency_order_synthesized_and_accepted",
        "local_psi_A_interaction_exchange_support_chain_closed",
        "all_linkages_remain_local_and_bounded",
        "theorem_linkage_chain_closed",
    ]:
        assert closeout[key] is True, key


def test_psi_A_interaction_exchange_chain_closeout_preserves_boundary() -> None:
    closeout = _json(DEFAULT_OUT)

    for key in [
        "closeout_executes_new_proof",
        "new_proof_execution_in_closeout",
        "proof_execution_authorized",
        "proof_attempt_executed",
        "proof_debt_discharged",
        "general_C_k_theorem_linkage_closure",
        "general_C_k_closure",
        "gap_1_through_gap_8_discharged",
        "global_gap_discharge_claimed",
        "C_k_dynamical_law_status",
        "C_k_action_embedding_claimed",
        "C_k_action_embedding_selected",
        "C_k_action_embedding_authorized",
        "C_k_action_variation_executed",
        "C_k_action_variation_authorized",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "standard_model_derivation_claimed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "rule_promoted",
    ]:
        assert closeout[key] is False, key


def test_psi_A_interaction_exchange_chain_closeout_lean_status() -> None:
    closeout = _json(DEFAULT_OUT)

    assert closeout["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_CLOSEOUT
    assert (
        closeout["full_toeformal_aggregate_status_for_closeout"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
    )
    assert (
        closeout["scoped_lean_targets_status_for_closeout"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
    )
    assert closeout["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(closeout)


def test_psi_A_interaction_exchange_chain_closeout_rotates_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    report = _rel(DEFAULT_OUT)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert is_current is True
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed_review = _workstreams(
        "review_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_cexchange_total_matter_and_gauge_closeouts_result",
        registry,
        status="paused",
    )[-1]
    assert consumed_review["authorization_evidence"] == _rel(
        SYNTHESIS_RESULT_REVIEW_LEAN_PACKET_PATH
    )
    assert consumed_review["report"] == _rel(SYNTHESIS_RESULT_REVIEW_OUT)
    assert consumed_review["selected_next_target"] == CONSUMED_TARGET

    consumed = _workstreams(CONSUMED_TARGET, registry, status="paused")[-1]
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["C_exchange_linkage_locally_closed"] == "yes"
    assert consumed["total_conservation_linkage_locally_closed"] == "yes"
    assert consumed["matter_sector_exchange_linkage_locally_closed"] == "yes"
    assert consumed["gauge_sector_exchange_linkage_locally_closed"] == "yes"
    assert consumed["local_psi_A_interaction_exchange_support_chain_closed"] == "yes"
    assert consumed["new_proof_execution_in_closeout"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == NEXT_TARGET
    assert active["active_lane"] == NEXT_TARGET
    assert active["authorization_evidence"] == evidence
    assert active["report"] == report
    assert active["authorized_next_strict_target"] == NEXT_TARGET
    assert active["consumed_target"] == CONSUMED_TARGET
    assert active["closeout_result"] == OUTCOME_ID
    assert active["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
    assert active["review_result"] == "PENDING"
    assert active["selected_next_target"] == "PENDING"
    assert active["local_psi_A_interaction_exchange_support_chain_closed"] == "yes"
    assert active["new_proof_execution_in_closeout"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_interaction_exchange_chain_closeout_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_AGGREGATE_PATH,
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
        STRICT_CLOSEOUT_RESULT,
        PACKET_CLASSIFICATION,
        "PsiAInteractionExchangeTheoremLinkageChainCloseout",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_REVIEW_OUTCOME,
        LIKELY_SELECTOR_AFTER_REVIEW,
        CLOSEOUT_STATEMENT,
        C_EXCHANGE_LINKAGE_CONCLUSION,
        TOTAL_CONSERVATION_CONCLUSION,
        MATTER_SECTOR_CONCLUSION,
        GAUGE_SECTOR_CONCLUSION,
        LEAN_STATUS_WORDING_FOR_CLOSEOUT,
        "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_OUTCOME_v0",
        "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_NONCLAIM_BOUNDARY_v0",
        "C_exchange linkage locally closed",
        "total-conservation linkage locally closed",
        "matter-sector exchange linkage locally closed",
        "gauge-sector exchange linkage locally closed",
        "dependency order synthesized and accepted",
        "local psi-A interaction exchange support chain closed",
        "no new proof execution in closeout",
        "no general C_k closure",
        "no GAP-1 through GAP-8 global discharge",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_interaction_exchange_chain_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_interaction_exchange_theorem_linkage_chain_closeout_gate.py"
    )
