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
from formal.python.tools.psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_cexchange_total_matter_and_gauge_closeouts_report import (
    DEFAULT_OUT as SYNTHESIS_PACKET_OUT,
    LEAN_PACKET_PATH as SYNTHESIS_LEAN_PACKET_PATH,
    OUTCOME_ID as SYNTHESIS_PACKET_OUTCOME,
)
from formal.python.tools.psi_A_interaction_exchange_theorem_linkage_chain_synthesis_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    BOUNDARY_NONCLAIMS,
    C_EXCHANGE_LINKAGE_CONCLUSION,
    C_EXCHANGE_LINKAGE_DEFINITION,
    C_EXCHANGE_LINKAGE_INPUT,
    CLAIM_BOUNDARY,
    CLOSEOUT_OUTCOME_HINT,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    GAUGE_SECTOR_CONCLUSION,
    GAUGE_SECTOR_INPUT_ROUTE,
    GAUGE_STRESS_DIVERGENCE_IDENTITY,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LIKELY_SELECTOR_AFTER_CLOSEOUT,
    LOCAL_DEPENDENCY_CHAIN,
    MATTER_SECTOR_CONCLUSION,
    MATTER_SECTOR_INPUT_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SOURCED_MAXWELL_ROUTE,
    STRICT_REVIEW_RESULT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_CONSERVATION_GAUGE_INPUT,
    TOTAL_CONSERVATION_MATTER_INPUT,
    build_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_interaction_exchange_theorem_linkage_chain_synthesis_result_review_report.py"
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


def test_psi_A_interaction_exchange_chain_synthesis_result_review_files_exist() -> None:
    for path in [
        SYNTHESIS_PACKET_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_interaction_exchange_chain_synthesis_result_review_accepts_packet() -> None:
    packet = _json(SYNTHESIS_PACKET_OUT)
    review = _json(DEFAULT_OUT)

    assert packet["outcome_id"] == SYNTHESIS_PACKET_OUTCOME
    assert packet["selected_next_target"] == CONSUMED_TARGET

    assert review["artifact_id"] == SCHEMA_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["reviewed"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_result"] == OUTCOME_ID
    assert review["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["closeout_outcome_hint"] == CLOSEOUT_OUTCOME_HINT
    assert review["likely_selector_after_closeout"] == LIKELY_SELECTOR_AFTER_CLOSEOUT
    assert build_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_result_review() == (
        review
    )


def test_psi_A_interaction_exchange_chain_synthesis_result_review_accepts_chain() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["accepted_review_findings_count"] == 13
    assert review["boundary_nonclaims"] == BOUNDARY_NONCLAIMS
    assert review["claim_boundary"] == CLAIM_BOUNDARY
    assert review["local_dependency_chain"] == LOCAL_DEPENDENCY_CHAIN
    assert review["linkage_chain_count"] == 4
    assert [row["linkage_id"] for row in review["linkage_chain"]] == [
        "C_exchange_linkage",
        "total_conservation_linkage",
        "matter_sector_exchange_linkage",
        "gauge_sector_exchange_linkage",
    ]
    assert review["C_exchange_linkage_definition"] == C_EXCHANGE_LINKAGE_DEFINITION
    assert review["C_exchange_linkage_input"] == C_EXCHANGE_LINKAGE_INPUT
    assert review["C_exchange_linkage_conclusion"] == C_EXCHANGE_LINKAGE_CONCLUSION
    assert review["total_conservation_gauge_input"] == TOTAL_CONSERVATION_GAUGE_INPUT
    assert review["total_conservation_matter_input"] == TOTAL_CONSERVATION_MATTER_INPUT
    assert review["total_conservation_conclusion"] == TOTAL_CONSERVATION_CONCLUSION
    assert review["matter_sector_input_route"] == MATTER_SECTOR_INPUT_ROUTE
    assert review["matter_sector_conclusion"] == MATTER_SECTOR_CONCLUSION
    assert review["gauge_sector_input_route"] == GAUGE_SECTOR_INPUT_ROUTE
    assert review["gauge_stress_divergence_identity"] == GAUGE_STRESS_DIVERGENCE_IDENTITY
    assert review["sourced_maxwell_route"] == SOURCED_MAXWELL_ROUTE
    assert review["gauge_sector_conclusion"] == GAUGE_SECTOR_CONCLUSION

    for key in [
        "C_exchange_linkage_included",
        "total_conservation_linkage_included",
        "matter_sector_exchange_linkage_included",
        "gauge_sector_exchange_linkage_included",
        "dependency_order_preserved",
        "all_linkages_remain_local_and_bounded",
        "local_dependency_chain_synthesis_accepted",
        "closeout_preparation_authorized",
    ]:
        assert review[key] is True, key
    assert review["closeout_prepared"] is False


def test_psi_A_interaction_exchange_chain_synthesis_result_review_preserves_boundary() -> None:
    review = _json(DEFAULT_OUT)

    for key in [
        "new_proof_execution_in_review",
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
        "standard_model_derivation_claimed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
        "master_action_promotion_authorized",
    ]:
        assert review[key] is False, key


def test_psi_A_interaction_exchange_chain_synthesis_result_review_lean_status() -> None:
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


def test_psi_A_interaction_exchange_chain_synthesis_result_review_rotates_to_closeout() -> None:
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
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    packet_row = _workstreams(
        "prepare_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_cexchange_total_matter_and_gauge_closeouts",
        registry,
        status="paused",
    )[-1]
    assert packet_row["authorization_evidence"] == _rel(SYNTHESIS_LEAN_PACKET_PATH)
    assert packet_row["report"] == _rel(SYNTHESIS_PACKET_OUT)
    assert packet_row["selected_next_target"] == CONSUMED_TARGET

    consumed = _workstreams(CONSUMED_TARGET, registry, status="paused")[-1]
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["C_exchange_linkage_included"] == "yes"
    assert consumed["total_conservation_linkage_included"] == "yes"
    assert consumed["matter_sector_exchange_linkage_included"] == "yes"
    assert consumed["gauge_sector_exchange_linkage_included"] == "yes"
    assert consumed["new_proof_execution_in_review"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    if is_current:
        active = active_workstream(registry)
        assert active["status"] == "active"
        assert active["workstream_id"] == NEXT_TARGET
        assert active["active_lane"] == NEXT_TARGET
        assert active["authorization_evidence"] == evidence
        assert active["report"] == report
        assert active["authorized_next_strict_target"] == NEXT_TARGET
        assert active["consumed_target"] == CONSUMED_TARGET
        assert active["review_result"] == OUTCOME_ID
        assert active["closeout_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["closeout_preparation_authorized"] == "yes"
        assert active["closeout_prepared"] == "no"
        assert active["proof_execution_authorized"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]


def test_psi_A_interaction_exchange_chain_synthesis_result_review_mirrors() -> None:
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
        STRICT_REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        "PsiAInteractionExchangeTheoremLinkageChainSynthesisResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        CLOSEOUT_OUTCOME_HINT,
        LIKELY_SELECTOR_AFTER_CLOSEOUT,
        C_EXCHANGE_LINKAGE_CONCLUSION,
        TOTAL_CONSERVATION_CONCLUSION,
        MATTER_SECTOR_CONCLUSION,
        GAUGE_SECTOR_CONCLUSION,
        LEAN_STATUS_WORDING_FOR_REVIEW,
        "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "C_exchange linkage included",
        "total-conservation linkage included",
        "matter-sector exchange linkage included",
        "gauge-sector exchange linkage included",
        "all linkages remain local and bounded",
        "no new proof execution in the synthesis review",
        "no C_k rule promotion",
        "no Standard Model derivation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_interaction_exchange_chain_synthesis_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_result_review_gate.py"
    )
