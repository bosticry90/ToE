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
from formal.python.tools.toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_packet_report import (
    ARTIFACT_ID,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CLOSEOUT_REVIEW_OUTCOME,
    CLOSEOUT_REVIEW_PATH,
    CLOSEOUT_REVIEW_RESULT,
    CONSUMED_TARGET,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    EXCHANGE_TERM_CANCELLATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RULE_CLASSIFICATION,
    RULE_EPISTEMIC_STATUS,
    RULE_FAMILY_CLASSIFICATION,
    RULE_FAMILY_EPISTEMIC_STATUS,
    RULE_FAMILY_ID,
    SCHEMA_ID,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
    build_toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_packet_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
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


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_psi_a_u1_interaction_exchange_synthesis_files_exist() -> None:
    for path in [
        CLOSEOUT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_interaction_exchange_synthesis_accepts_review() -> None:
    closeout_review = _json(CLOSEOUT_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert closeout_review["outcome_id"] == CLOSEOUT_REVIEW_OUTCOME
    assert closeout_review["review_result"] == CLOSEOUT_REVIEW_RESULT
    assert closeout_review["selected_next_target"] == CONSUMED_TARGET

    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_packet() == (
        packet
    )


def test_psi_a_u1_interaction_exchange_synthesis_preserves_chain() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["rule_family_id"] == RULE_FAMILY_ID
    assert packet["rule_family_classification"] == RULE_FAMILY_CLASSIFICATION
    assert packet["rule_family_epistemic_status"] == RULE_FAMILY_EPISTEMIC_STATUS
    assert packet["route_family_chain_count"] == 7
    assert [row["route_id"] for row in packet["route_family_chain"]] == [
        "A_variation_current_candidate",
        "current_conservation",
        "sourced_maxwell_route",
        "gauge_sector_exchange",
        "matter_sector_exchange",
        "total_stress_energy_conservation",
        "C_exchange_rule",
    ]
    assert packet["current_candidate"] == CURRENT_CANDIDATE
    assert packet["source_current"] == SOURCE_CURRENT
    assert packet["current_conservation_result"] == CURRENT_CONSERVATION_RESULT
    assert packet["sourced_gauge_route"] == SOURCED_GAUGE_ROUTE
    assert packet["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert packet["matter_sector_exchange_identity"] == MATTER_SECTOR_EXCHANGE_IDENTITY
    assert packet["exchange_term_cancellation"] == EXCHANGE_TERM_CANCELLATION
    assert packet["total_stress_energy_object"] == TOTAL_STRESS_ENERGY_OBJECT
    assert packet["total_stress_energy_conservation_identity"] == (
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    assert packet["C_exchange_constraint_id"] == C_EXCHANGE_CONSTRAINT_ID
    assert packet["C_exchange_constraint_form"] == C_EXCHANGE_CONSTRAINT_FORM
    assert packet["C_exchange_total_stress_energy_form"] == (
        C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
    )
    assert packet["C_exchange_admissibility_condition"] == (
        C_EXCHANGE_ADMISSIBILITY_CONDITION
    )
    assert packet["C_exchange_candidate_scope"] == C_EXCHANGE_CANDIDATE_SCOPE
    assert packet["C_exchange_plain_meaning"] == C_EXCHANGE_PLAIN_MEANING
    assert packet["C_exchange_rule_classification"] == RULE_CLASSIFICATION
    assert packet["C_exchange_rule_epistemic_status"] == RULE_EPISTEMIC_STATUS


def test_psi_a_u1_interaction_exchange_synthesis_accepts_required_points() -> None:
    packet = _json(DEFAULT_OUT)
    assert {row["row_id"] for row in packet["synthesis_criteria"]} == {
        "closeout_result_review_consumed",
        "current_candidate_and_conservation_preserved",
        "sourced_gauge_route_preserved",
        "exchange_halves_preserved",
        "total_conservation_preserved",
        "cexchange_rule_preserved",
        "no_em_qft_or_ck_action_closure",
        "result_review_selected_next",
    }
    assert packet["synthesis_criteria_count"] == 8
    assert packet["synthesis_criteria_accepted_count"] == 8
    for key in [
        "synthesis_packet_prepared",
        "interaction_exchange_rule_family_synthesis_packet_prepared",
        "interaction_exchange_rule_family_synthesized",
        "current_source_exchange_and_total_conservation_routes_synthesized",
        "C_exchange_rule_preserved",
        "C_exchange_remains_admissibility_only",
        "C_exchange_closeout_accepted",
        "result_review_authorized",
    ]:
        assert packet[key] is True, key


def test_psi_a_u1_interaction_exchange_synthesis_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "functional_action_embedding_claimed",
        "C_exchange_functional_embedding_claimed",
        "multiplier_action_route_selected",
        "penalty_route_selected",
        "C_k_action_embedding_selected",
        "C_k_action_variation_executed",
        "C_k_action_variation_authorized",
        "candidate_varied",
        "direct_dynamical_law_interpretation_selected",
        "direct_force_law_claimed",
        "new_force_law_claimed",
        "full_maxwell_closure_claimed",
        "full_Maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "quantized_electromagnetism_claimed",
        "anomaly_analysis_performed",
        "standard_model_derivation_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "pillar_completion_inferred",
        "seam_closure_claim",
        "EM_QFT_closure",
        "QFT_GR_closure",
        "master_action_promotion",
    ]:
        assert packet[key] is False, key


def test_psi_a_u1_interaction_exchange_synthesis_nonclaim_boundary() -> None:
    boundary = _json(DEFAULT_OUT)["non_claim_boundary"]
    for phrase in [
        "current, source, exchange, total-conservation, and C_exchange route family only",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no full Maxwell closure",
        "no C_k action closure",
        "no C_k action variation",
        "no functional action embedding",
        "no multiplier/action route",
        "no penalty route",
        "no direct dynamical-law interpretation",
        "no quantized electromagnetism",
        "no anomaly analysis",
        "no Standard Model derivation",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
        "working-form, noncanonical organizing surface",
    ]:
        assert phrase in boundary, phrase


def test_psi_a_u1_interaction_exchange_synthesis_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert packet["full_toeformal_aggregate_passed"] is False
    assert packet["full_toeformal_aggregate_failed"] is False
    assert packet["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_interaction_exchange_synthesis_rotates_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = str(LEAN_PACKET_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
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
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["result_token"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["interaction_exchange_rule_family_synthesis_packet_prepared"] == "yes"
    assert consumed["interaction_exchange_rule_family_synthesized"] == "yes"
    assert consumed["current_source_exchange_and_total_conservation_routes_synthesized"] == (
        "yes"
    )
    assert consumed["C_exchange_remains_admissibility_only"] == "yes"
    assert consumed["C_k_action_variation_executed"] == "no"
    assert consumed["em_qft_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = _workstream(registry, NEXT_TARGET)
    assert active_row["status"] == "active"
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["active_lane"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["authorization_evidence"] == evidence
    assert active_row["report"] == str(DEFAULT_OUT.relative_to(REPO_ROOT)).replace(
        "\\", "/"
    )
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["packet_result"] == "PENDING"
    assert active_row["review_result"] == "PENDING"
    assert active_row["result_review_prepared"] == "no"
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["result_token"] == OUTCOME_ID
    assert active_row["selected_next_target"] == NEXT_TARGET
    assert active_row["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert active_row["interaction_exchange_rule_family_synthesis_packet_prepared"] == "yes"
    assert active_row["interaction_exchange_rule_family_synthesized"] == "yes"
    assert active_row["current_source_exchange_and_total_conservation_routes_synthesized"] == (
        "yes"
    )
    assert active_row["C_exchange_rule_family_closed"] == "no"
    assert active_row["C_exchange_closeout_accepted"] == "yes"
    assert active_row["C_exchange_remains_admissibility_only"] == "yes"
    assert active_row["C_exchange_rule_preserved"] == "yes"
    assert active_row["functional_action_embedding_claimed"] == "no"
    assert active_row["multiplier_action_route_selected"] == "no"
    assert active_row["penalty_route_selected"] == "no"
    assert active_row["C_k_action_variation_executed"] == "no"
    assert active_row["em_qft_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_psi_a_u1_interaction_exchange_synthesis_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_AGGREGATE_PATH,
            CURRENT_TARGET_AGGREGATE_PATH,
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
        PACKET_RESULT,
        PACKET_CLASSIFICATION,
        "ToeNativePsiAU1InteractionExchangeRuleFamilySynthesisPacket",
        CONSUMED_TARGET,
        NEXT_TARGET,
        f"CURRENT_LIVE_NEXT_TARGET_v0: {NEXT_TARGET}",
        f"PREVIOUS_LIVE_NEXT_TARGET_v0: {CONSUMED_TARGET}",
        f"CURRENT_LIVE_TARGET_REPORT_v0: {str(DEFAULT_OUT.relative_to(REPO_ROOT)).replace(chr(92), '/')}",
        f"CURRENT_LIVE_TARGET_OUTCOME_v0: {OUTCOME_ID}",
        CURRENT_CANDIDATE,
        CURRENT_CONSERVATION_RESULT,
        SOURCE_CURRENT,
        SOURCED_GAUGE_ROUTE,
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        EXCHANGE_TERM_CANCELLATION,
        TOTAL_STRESS_ENERGY_OBJECT,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        C_EXCHANGE_CONSTRAINT_ID,
        C_EXCHANGE_CONSTRAINT_FORM,
        C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
        C_EXCHANGE_ADMISSIBILITY_CONDITION,
        RULE_FAMILY_ID,
        RULE_FAMILY_CLASSIFICATION,
        "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_PACKET_OUTCOME_v0",
        "PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_PACKET_NONCLAIM_BOUNDARY_v0",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no C_k action closure",
        "no C_k action variation",
        "no master-action promotion",
        "working-form, noncanonical organizing surface",
    ]:
        assert token in joined, token


def test_psi_a_u1_interaction_exchange_synthesis_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_packet_gate.py"
    )
