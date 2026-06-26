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
from formal.python.tools.toe_native_psi_a_u1_cexchange_constraint_candidate_packet_result_review_report import (
    DEFAULT_OUT as CANDIDATE_REVIEW_PATH,
    OUTCOME_ID as CANDIDATE_REVIEW_OUTCOME,
)
from formal.python.tools.toe_native_psi_a_u1_cexchange_functional_embedding_packet_report import (
    ADMISSIBILITY_CONSTRAINT_FORM,
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ARTIFACT_ID,
    BLOCKED_CLAIMS,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MULTIPLIER_ACTION_FORM,
    MULTIPLIER_ACTION_ROUTE_ID,
    MULTIPLIER_BLOCKING_REASONS,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PENALTY_ACTION_FORM,
    PENALTY_BLOCKING_REASONS,
    PENALTY_ROUTE_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    build_toe_native_psi_a_u1_cexchange_functional_embedding_packet,
)
from formal.python.tools.toe_native_psi_a_u1_cexchange_functional_embedding_packet_result_review_report import (
    NEXT_TARGET as CEXCHANGE_CLOSEOUT_TARGET,
    OUTCOME_ID as FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
)
from formal.python.tools.toe_native_psi_a_u1_cexchange_admissibility_rule_closeout_report import (
    NEXT_TARGET as CEXCHANGE_CLOSEOUT_REVIEW_TARGET,
    OUTCOME_ID as CEXCHANGE_CLOSEOUT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_cexchange_functional_embedding_packet_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
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


def test_psi_a_u1_cexchange_functional_embedding_packet_files_exist() -> None:
    for path in [
        CANDIDATE_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_cexchange_functional_embedding_packet_builds() -> None:
    candidate_review = _json(CANDIDATE_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert candidate_review["outcome_id"] == CANDIDATE_REVIEW_OUTCOME
    assert candidate_review["selected_next_target"] == CONSUMED_TARGET

    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_toe_native_psi_a_u1_cexchange_functional_embedding_packet() == (
        packet
    )


def test_psi_a_u1_cexchange_functional_embedding_packet_records_options() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["C_exchange_constraint_id"] == C_EXCHANGE_CONSTRAINT_ID
    assert packet["C_exchange_constraint_form"] == C_EXCHANGE_CONSTRAINT_FORM
    assert packet["C_exchange_total_stress_energy_form"] == (
        C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
    )
    assert packet["C_exchange_admissibility_condition"] == (
        C_EXCHANGE_ADMISSIBILITY_CONDITION
    )
    assert packet["C_exchange_candidate_scope"] == C_EXCHANGE_CANDIDATE_SCOPE
    assert packet["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert packet["matter_sector_exchange_identity"] == MATTER_SECTOR_EXCHANGE_IDENTITY
    assert packet["total_stress_energy_conservation_identity"] == (
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )

    routes = packet["embedding_routes"]
    assert packet["embedding_route_count"] == 3
    assert [route["route_id"] for route in routes] == [
        ADMISSIBILITY_ONLY_ROUTE_ID,
        MULTIPLIER_ACTION_ROUTE_ID,
        PENALTY_ROUTE_ID,
    ]
    assert packet["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert routes[0]["constraint_form"] == ADMISSIBILITY_CONSTRAINT_FORM
    assert routes[0]["selected_for_current_packet"] is True
    assert routes[0]["action_term_selected"] is False
    assert routes[1]["action_form"] == MULTIPLIER_ACTION_FORM
    assert routes[1]["blocking_reasons"] == MULTIPLIER_BLOCKING_REASONS
    assert routes[2]["action_form"] == PENALTY_ACTION_FORM
    assert routes[2]["blocking_reasons"] == PENALTY_BLOCKING_REASONS
    assert packet["multiplier_blocking_reason_count"] == 8
    assert packet["penalty_blocking_reason_count"] == 3
    assert packet["allowed_claim_count"] == 6
    assert packet["blocked_claim_count"] == 14
    assert packet["review_row_count"] == 10
    assert packet["review_row_accepted_count"] == 10


def test_psi_a_u1_cexchange_functional_embedding_packet_preserves_boundaries() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    for key in [
        "C_exchange_functional_embedding_packet_prepared",
        "functional_embedding_packet_prepared",
        "functional_embedding_options_recorded",
        "C_exchange_functional_embedding_options_recorded",
        "admissibility_only_route_selected",
        "admissibility_only_interpretation_retained",
        "interaction_admissibility_rule_selected",
        "constraint_as_admissibility_rule_selected",
        "candidate_based_on_accepted_total_conservation_route",
        "C_exchange_candidate_carried_forward",
        "C_exchange_constraint_candidate_result_review_consumed",
        "total_exchange_conservation_residual_candidate_consumed",
        "total_stress_energy_object_preserved",
        "gauge_matter_exchange_balance_context_preserved",
        "multiplier_action_route_recorded",
        "multiplier_action_route_blocked",
        "penalty_route_recorded",
        "penalty_route_unlicensed",
        "direct_dynamical_law_interpretation_blocked",
        "C_exchange_functional_embedding_packet_result_review_selected",
        "C_exchange_functional_embedding_packet_result_review_authorized",
    ]:
        assert packet[key] is True, key

    for key in [
        "C_exchange_closeout",
        "C_exchange_definition_closeout",
        "C_exchange_rule_family_closed",
        "C_exchange_functional_embedding_claimed",
        "C_exchange_functional_embedding_selected",
        "C_exchange_functional_embedding_constructed",
        "multiplier_action_route_selected",
        "multiplier_action_route_constructed",
        "multiplier_field_type_selected",
        "multiplier_index_placement_selected",
        "multiplier_units_fixed",
        "boundary_terms_controlled",
        "metric_tetrad_variation_behavior_analyzed",
        "higher_derivative_risk_resolved",
        "circularity_control_established",
        "stability_analysis_completed",
        "penalty_route_selected",
        "penalty_route_constructed",
        "penalty_route_licensed",
        "direct_dynamical_law_interpretation_selected",
        "direct_force_law_claimed",
        "varied_dynamical_equation_claimed",
        "C_k_action_variation_executed",
        "C_k_action_variation_authorized",
        "candidate_varied",
        "action_embedding_claimed",
        "full_maxwell_closure_claimed",
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
    ]:
        assert packet[key] is False, key

    for phrase in [
        "bounded C_exchange functional-embedding options packet only",
        "admissibility-only route C_exchange^{Apsi,nu} = 0",
        "selects it as a rule for accepting or rejecting",
        "multiplier/action route",
        "blocked by unresolved multiplier field type",
        "index placement",
        "units",
        "boundary terms",
        "metric/tetrad variation behavior",
        "higher-derivative risk",
        "circularity control",
        "stability analysis",
        "penalty route",
        "unlicensed",
        "no C_exchange closeout",
        "no multiplier/action route",
        "no penalty route",
        "no C_k action variation",
        "no direct dynamical-law interpretation",
        "no full Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no quantized electromagnetism",
        "no anomaly analysis",
        "no Standard Model derivation",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_psi_a_u1_cexchange_functional_embedding_packet_validation_policy_is_bounded() -> None:
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


def test_psi_a_u1_cexchange_functional_embedding_packet_rotates_to_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = str(LEAN_PACKET_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    if is_current:
        assert_current_target_consistent()
        assert_frontier_matches_registry()
        assert_public_surfaces_match_registry()

    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    if is_current:
        assert NEXT_TARGET not in registry["paused_lanes"]
    else:
        assert NEXT_TARGET in registry["paused_lanes"]
        if CEXCHANGE_CLOSEOUT_TARGET in registry["paused_lanes"]:
            assert CEXCHANGE_CLOSEOUT_REVIEW_TARGET not in registry["paused_lanes"]
        else:
            assert CEXCHANGE_CLOSEOUT_TARGET not in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["C_exchange_functional_embedding_packet_result"] == OUTCOME_ID
    assert consumed["C_exchange_functional_embedding_packet_result_review_result"] in {
        "PENDING",
        FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
    }
    assert consumed["functional_embedding_options_recorded"] == "yes"
    assert consumed["admissibility_only_route_selected"] == "yes"
    assert consumed["multiplier_action_route_recorded"] == "yes"
    assert consumed["multiplier_action_route_blocked"] == "yes"
    assert consumed["multiplier_action_route_selected"] == "no"
    assert consumed["penalty_route_recorded"] == "yes"
    assert consumed["penalty_route_unlicensed"] == "yes"
    assert consumed["penalty_route_selected"] == "no"
    assert consumed["direct_dynamical_law_interpretation_blocked"] == "yes"
    assert consumed["C_k_action_variation_executed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = _workstream(registry, NEXT_TARGET)
    if is_current:
        assert active_row["status"] == "active"
        assert active_row["workstream_id"] == NEXT_TARGET
        assert active_row["active_lane"] == NEXT_TARGET
        assert active_row["authorized_next_strict_target"] == NEXT_TARGET
        assert active_row["authorized_target"] == NEXT_TARGET
        assert active_row["consumed_target"] == CONSUMED_TARGET
        assert active_row["packet_result"] == "PENDING"
        assert active_row["outcome_id"] == OUTCOME_ID
        assert active_row["result_token"] == OUTCOME_ID
    else:
        assert active_row["status"] == "paused"
        assert active_row["packet_result"] == FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME
        assert active_row["selected_next_target"] == CEXCHANGE_CLOSEOUT_TARGET
        assert active_row["outcome_id"] == FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME
        assert active_row["result_token"] == FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME

        if CEXCHANGE_CLOSEOUT_TARGET in registry["paused_lanes"]:
            closeout_row = _workstream(registry, CEXCHANGE_CLOSEOUT_TARGET)
            assert closeout_row["status"] == "paused"
            assert closeout_row["packet_result"] == "CLOSEOUT_ACCEPTED"
            assert closeout_row["outcome_id"] == CEXCHANGE_CLOSEOUT_OUTCOME
            assert closeout_row["selected_next_target"] == CEXCHANGE_CLOSEOUT_REVIEW_TARGET

            review_row = _workstream(registry, CEXCHANGE_CLOSEOUT_REVIEW_TARGET)
            assert review_row["status"] == "active"
            assert review_row["packet_result"] == "PENDING"
            assert review_row["outcome_id"] == CEXCHANGE_CLOSEOUT_OUTCOME
    assert active_row["C_exchange_functional_embedding_packet_result"] == OUTCOME_ID
    assert active_row["C_exchange_functional_embedding_packet_result_review_result"] in {
        "PENDING",
        FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
    }
    assert active_row["functional_embedding_packet_prepared"] == "yes"
    assert active_row["functional_embedding_options_recorded"] == "yes"
    assert active_row["admissibility_only_route_selected"] == "yes"
    assert active_row["multiplier_action_route_selected"] == "no"
    assert active_row["penalty_route_selected"] == "no"
    assert active_row["direct_dynamical_law_interpretation_blocked"] == "yes"
    assert active_row["C_exchange_functional_embedding_claimed"] == "no"
    assert active_row["C_k_action_variation_executed"] == "no"


def test_psi_a_u1_cexchange_functional_embedding_packet_mirrors() -> None:
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
        PACKET_CLASSIFICATION,
        "ToeNativePsiAU1CExchangeFunctionalEmbeddingPacket",
        CONSUMED_TARGET,
        NEXT_TARGET,
        f"CURRENT_LIVE_NEXT_TARGET_v0: {NEXT_TARGET}",
        f"PREVIOUS_LIVE_NEXT_TARGET_v0: {CONSUMED_TARGET}",
        C_EXCHANGE_CONSTRAINT_ID,
        C_EXCHANGE_CONSTRAINT_FORM,
        C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
        C_EXCHANGE_ADMISSIBILITY_CONDITION,
        C_EXCHANGE_CANDIDATE_SCOPE,
        ADMISSIBILITY_ONLY_ROUTE_ID,
        MULTIPLIER_ACTION_ROUTE_ID,
        MULTIPLIER_ACTION_FORM,
        PENALTY_ROUTE_ID,
        PENALTY_ACTION_FORM,
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_OUTCOME_v0",
        "PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_NONCLAIM_BOUNDARY_v0",
        "bounded C_exchange functional-embedding options packet only",
        "admissibility-only route C_exchange^{Apsi,nu} = 0",
        "multiplier field type",
        "index placement",
        "unit/sign issues",
        "no C_exchange closeout",
        "no multiplier/action route",
        "no penalty route",
        "no C_k action variation",
        "no direct dynamical-law interpretation",
        "no full Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no quantized electromagnetism",
        "no anomaly analysis",
        "no Standard Model derivation",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined, token


def test_psi_a_u1_cexchange_functional_embedding_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_cexchange_functional_embedding_packet_gate.py"
    )
