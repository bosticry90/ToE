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
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_result_review_report import (
    DEFAULT_OUT as GAUGE_CLOSEOUT_REVIEW_OUT,
    LEAN_PACKET_PATH as GAUGE_CLOSEOUT_REVIEW_LEAN_PACKET_PATH,
    OUTCOME_ID as GAUGE_CLOSEOUT_REVIEW_OUTCOME,
)
from formal.python.tools.psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_cexchange_total_matter_and_gauge_closeouts_report import (
    C_EXCHANGE_LINKAGE_CONCLUSION,
    C_EXCHANGE_LINKAGE_DEFINITION,
    C_EXCHANGE_LINKAGE_INPUT,
    CLAIM_BOUNDARY,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SYNTHESIS,
    GAUGE_SECTOR_CONCLUSION,
    GAUGE_SECTOR_INPUT_ROUTE,
    GAUGE_STRESS_DIVERGENCE_IDENTITY,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_SYNTHESIS,
    LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW,
    LOCAL_DEPENDENCY_CHAIN,
    MATTER_SECTOR_CONCLUSION,
    MATTER_SECTOR_INPUT_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    NONCLAIMS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PACKET_RESULT,
    PLAIN_MEANING,
    QFTGR_AGGREGATE_PATH,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_SYNTHESIS,
    SOURCED_MAXWELL_ROUTE,
    STRICT_PACKET_RESULT,
    SYNTHESIS_CLAIMS,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_CONSERVATION_GAUGE_INPUT,
    TOTAL_CONSERVATION_MATTER_INPUT,
    build_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_cexchange_total_matter_and_gauge_closeouts,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_cexchange_total_matter_and_gauge_closeouts_report.py"
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


def test_psi_A_interaction_exchange_chain_synthesis_files_exist() -> None:
    for path in [
        GAUGE_CLOSEOUT_REVIEW_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_interaction_exchange_chain_synthesis_accepts_source_review() -> None:
    source_review = _json(GAUGE_CLOSEOUT_REVIEW_OUT)
    packet = _json(DEFAULT_OUT)

    assert source_review["outcome_id"] == GAUGE_CLOSEOUT_REVIEW_OUTCOME
    assert source_review["selected_next_target"] == CONSUMED_TARGET

    assert packet["artifact_id"] == SCHEMA_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == PACKET_RESULT
    assert packet["strict_packet_result"] == STRICT_PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["likely_follow_on_target_after_review"] == (
        LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW
    )
    assert (
        build_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_cexchange_total_matter_and_gauge_closeouts()
        == packet
    )


def test_psi_A_interaction_exchange_chain_synthesis_records_dependency_chain() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["plain_meaning"] == PLAIN_MEANING
    assert packet["claim_boundary"] == CLAIM_BOUNDARY
    assert packet["synthesis_claims"] == SYNTHESIS_CLAIMS
    assert packet["nonclaims"] == NONCLAIMS
    assert packet["local_dependency_chain"] == LOCAL_DEPENDENCY_CHAIN
    assert packet["linkage_chain_count"] == 4
    assert [row["linkage_id"] for row in packet["linkage_chain"]] == [
        "C_exchange_linkage",
        "total_conservation_linkage",
        "matter_sector_exchange_linkage",
        "gauge_sector_exchange_linkage",
    ]
    assert packet["C_exchange_linkage_definition"] == C_EXCHANGE_LINKAGE_DEFINITION
    assert packet["C_exchange_linkage_input"] == C_EXCHANGE_LINKAGE_INPUT
    assert packet["C_exchange_linkage_conclusion"] == C_EXCHANGE_LINKAGE_CONCLUSION
    assert packet["total_conservation_gauge_input"] == TOTAL_CONSERVATION_GAUGE_INPUT
    assert packet["total_conservation_matter_input"] == TOTAL_CONSERVATION_MATTER_INPUT
    assert packet["total_conservation_conclusion"] == TOTAL_CONSERVATION_CONCLUSION
    assert packet["matter_sector_input_route"] == MATTER_SECTOR_INPUT_ROUTE
    assert packet["matter_sector_conclusion"] == MATTER_SECTOR_CONCLUSION
    assert packet["gauge_sector_input_route"] == GAUGE_SECTOR_INPUT_ROUTE
    assert packet["gauge_stress_divergence_identity"] == GAUGE_STRESS_DIVERGENCE_IDENTITY
    assert packet["sourced_maxwell_route"] == SOURCED_MAXWELL_ROUTE
    assert packet["gauge_sector_conclusion"] == GAUGE_SECTOR_CONCLUSION

    for key in [
        "local_psi_A_interaction_exchange_theorem_linkage_chain_synthesized",
        "C_exchange_total_matter_and_gauge_linkages_synthesized",
        "C_exchange_linkage_recorded",
        "total_conservation_linkage_recorded",
        "matter_sector_exchange_linkage_recorded",
        "gauge_sector_exchange_linkage_recorded",
        "bounded_local_linkages_only",
        "synthesis_packet_prepared",
        "result_review_authorized",
    ]:
        assert packet[key] is True, key


def test_psi_A_interaction_exchange_chain_synthesis_preserves_boundary() -> None:
    packet = _json(DEFAULT_OUT)

    for key in [
        "new_proof_execution_in_packet",
        "proof_execution_authorized",
        "proof_attempt_executed",
        "theorem_discharged",
        "theorem_linkage_obligation_discharged",
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
        "multiplier_route_selected",
        "multiplier_action_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_claimed",
        "direct_dynamical_law_interpretation_selected",
        "functional_action_embedding_claimed",
        "functionalization_authorized",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
        "master_action_promotion_authorized",
    ]:
        assert packet[key] is False, key


def test_psi_A_interaction_exchange_chain_synthesis_records_lean_status() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_SYNTHESIS
    assert (
        packet["full_toeformal_aggregate_status_for_synthesis"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SYNTHESIS
    )
    assert (
        packet["scoped_lean_targets_status_for_synthesis"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_SYNTHESIS
    )
    assert packet["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(packet)


def test_psi_A_interaction_exchange_chain_synthesis_rotates_to_review() -> None:
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

    source_review = _workstreams(
        "review_psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_result",
        registry,
        status="paused",
    )[-1]
    assert source_review["authorization_evidence"] == _rel(
        GAUGE_CLOSEOUT_REVIEW_LEAN_PACKET_PATH
    )
    assert source_review["report"] == _rel(GAUGE_CLOSEOUT_REVIEW_OUT)
    assert source_review["selected_next_target"] == CONSUMED_TARGET

    consumed = _workstreams(CONSUMED_TARGET, registry, status="paused")[-1]
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["strict_packet_result"] == STRICT_PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["synthesis_packet_prepared"] == "yes"
    assert consumed["new_proof_execution_in_packet"] == "no"
    assert consumed["proof_execution_authorized"] == "no"
    assert consumed["theorem_discharged"] == "no"
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
    assert active["packet_result"] == OUTCOME_ID
    assert active["strict_packet_result"] == STRICT_PACKET_RESULT
    assert active["review_result"] == "PENDING"
    assert active["selected_next_target"] == "PENDING"
    assert active["synthesis_packet_prepared"] == "yes"
    assert active["proof_execution_authorized"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_interaction_exchange_chain_synthesis_mirrors() -> None:
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
        STRICT_PACKET_RESULT,
        PACKET_CLASSIFICATION,
        "PsiAInteractionExchangeTheoremLinkageChainSynthesisAfterCexchangeTotalMatterAndGaugeCloseouts",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW,
        C_EXCHANGE_LINKAGE_DEFINITION,
        C_EXCHANGE_LINKAGE_CONCLUSION,
        TOTAL_CONSERVATION_CONCLUSION,
        MATTER_SECTOR_CONCLUSION,
        GAUGE_SECTOR_CONCLUSION,
        LEAN_STATUS_WORDING_FOR_SYNTHESIS,
        "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_AFTER_CEXCHANGE_TOTAL_MATTER_AND_GAUGE_CLOSEOUTS_OUTCOME_v0",
        "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_NONCLAIM_BOUNDARY_v0",
        "local psi-A interaction exchange theorem-linkage chain synthesized",
        "C_exchange, total conservation, matter exchange, and gauge exchange linked in dependency order",
        "no new proof execution in this synthesis packet",
        "no C_k rule promotion",
        "no seam closure",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_interaction_exchange_chain_synthesis_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_cexchange_total_matter_and_gauge_closeouts_gate.py"
    )
