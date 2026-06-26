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
from formal.python.tools.toe_native_psi_a_u1_cexchange_admissibility_rule_closeout_report import (
    ACCEPTED_CLOSEOUT_FINDINGS,
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ADMISSIBILITY_ONLY_ROUTE_STATUS,
    ARTIFACT_ID,
    BLOCKED_CLAIMS,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CLOSEOUT_RESULT,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    EXCHANGE_TERM_CANCELLATION,
    FOLLOW_ON_SYNTHESIS_OUTCOME,
    FOLLOW_ON_SYNTHESIS_TARGET,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
    FUNCTIONAL_EMBEDDING_REVIEW_PATH,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MULTIPLIER_ACTION_FORM,
    MULTIPLIER_ACTION_ROUTE_ID,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PENALTY_ACTION_FORM,
    PENALTY_ROUTE_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RULE_CLASSIFICATION,
    RULE_EPISTEMIC_STATUS,
    RULE_SCOPE,
    SCHEMA_ID,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
    build_toe_native_psi_a_u1_cexchange_admissibility_rule_closeout,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_cexchange_admissibility_rule_closeout_report.py"
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


def test_psi_a_u1_cexchange_admissibility_rule_closeout_files_exist() -> None:
    for path in [
        FUNCTIONAL_EMBEDDING_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_cexchange_admissibility_rule_closeout_accepts_rule() -> None:
    previous = _json(FUNCTIONAL_EMBEDDING_REVIEW_PATH)
    closeout = _json(DEFAULT_OUT)
    assert previous["outcome_id"] == FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME
    assert previous["selected_next_target"] == CONSUMED_TARGET

    assert closeout["artifact_id"] == ARTIFACT_ID
    assert closeout["schema_id"] == SCHEMA_ID
    assert closeout["packet_id"] == PACKET_ID
    assert closeout["prepared"] is True
    assert closeout["accepted"] is True
    assert closeout["outcome_id"] == OUTCOME_ID
    assert closeout["closeout_result"] == CLOSEOUT_RESULT
    assert closeout["packet_result"] == "CLOSEOUT_ACCEPTED"
    assert closeout["packet_classification"] == PACKET_CLASSIFICATION
    assert closeout["consumed_target"] == CONSUMED_TARGET
    assert closeout["selected_next_target"] == NEXT_TARGET
    assert closeout["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert closeout["functional_embedding_review_outcome"] == (
        FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME
    )
    assert build_toe_native_psi_a_u1_cexchange_admissibility_rule_closeout() == closeout


def test_psi_a_u1_cexchange_admissibility_rule_closeout_preserves_forms() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["C_exchange_constraint_id"] == C_EXCHANGE_CONSTRAINT_ID
    assert closeout["C_exchange_constraint_form"] == C_EXCHANGE_CONSTRAINT_FORM
    assert closeout["C_exchange_total_stress_energy_form"] == (
        C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
    )
    assert closeout["C_exchange_admissibility_condition"] == (
        C_EXCHANGE_ADMISSIBILITY_CONDITION
    )
    assert closeout["C_exchange_candidate_scope"] == C_EXCHANGE_CANDIDATE_SCOPE
    assert closeout["C_exchange_plain_meaning"] == C_EXCHANGE_PLAIN_MEANING
    assert closeout["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert closeout["admissibility_only_route_status"] == ADMISSIBILITY_ONLY_ROUTE_STATUS
    assert closeout["rule_classification"] == RULE_CLASSIFICATION
    assert closeout["rule_epistemic_status"] == RULE_EPISTEMIC_STATUS
    assert closeout["rule_scope"] == RULE_SCOPE
    assert closeout["source_current"] == SOURCE_CURRENT
    assert closeout["sourced_gauge_route"] == SOURCED_GAUGE_ROUTE
    assert closeout["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert closeout["matter_sector_exchange_identity"] == MATTER_SECTOR_EXCHANGE_IDENTITY
    assert closeout["exchange_term_cancellation"] == EXCHANGE_TERM_CANCELLATION
    assert closeout["total_stress_energy_object"] == TOTAL_STRESS_ENERGY_OBJECT
    assert closeout["total_stress_energy_conservation_identity"] == (
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    assert closeout["multiplier_action_route_id"] == MULTIPLIER_ACTION_ROUTE_ID
    assert closeout["multiplier_action_form"] == MULTIPLIER_ACTION_FORM
    assert closeout["penalty_route_id"] == PENALTY_ROUTE_ID
    assert closeout["penalty_action_form"] == PENALTY_ACTION_FORM
    assert closeout["accepted_closeout_findings"] == ACCEPTED_CLOSEOUT_FINDINGS
    assert closeout["accepted_closeout_findings_count"] == 10
    assert closeout["blocked_claims"] == BLOCKED_CLAIMS
    assert closeout["blocked_claim_count"] == 14
    assert closeout["closeout_criteria_count"] == 12
    assert closeout["closeout_criteria_accepted_count"] == 12


def test_psi_a_u1_cexchange_admissibility_rule_closeout_accepts_required_points() -> None:
    closeout = _json(DEFAULT_OUT)
    assert {row["row_id"] for row in closeout["closeout_criteria"]} == {
        "functional_embedding_review_consumed",
        "cexchange_rule_closed_as_interaction_exchange_balance",
        "cexchange_candidate_form_preserved",
        "total_stress_energy_form_preserved",
        "admissibility_condition_preserved",
        "accepted_total_conservation_route_basis_preserved",
        "exchange_halves_context_preserved",
        "admissibility_only_not_force_law",
        "multiplier_penalty_and_action_routes_blocked",
        "no_ck_action_variation_or_functionalization",
        "closure_quantization_phase_validation_and_promotion_blocked",
        "closeout_result_review_selected_next",
    }
    for key in [
        "admissibility_rule_closeout_prepared",
        "admissibility_rule_closeout_accepted",
        "C_exchange_admissibility_rule_closed",
        "C_exchange_definition_closeout",
        "C_exchange_rule_closed_as_interaction_exchange_balance_rule",
        "interaction_exchange_balance_rule_closed",
        "candidate_recorded_as_rule_only",
        "admissibility_only_route_selected",
        "admissibility_only_interpretation_retained",
        "constraint_as_admissibility_rule_selected",
        "based_on_accepted_total_stress_energy_conservation_route",
        "C_exchange_candidate_preserved",
        "T_total_preserved",
        "exchange_halves_context_preserved",
        "closeout_result_review_selected_next",
    ]:
        assert closeout[key] is True, key


def test_psi_a_u1_cexchange_admissibility_rule_closeout_preserves_nonclaims() -> None:
    closeout = _json(DEFAULT_OUT)
    for key in [
        "closeout_result_review_prepared",
        "follow_on_synthesis_prepared",
        "interaction_exchange_rule_family_synthesized",
        "interaction_exchange_rule_family_synthesis_packet_prepared",
        "C_exchange_functional_embedding_claimed",
        "C_exchange_functional_embedding_selected",
        "C_exchange_functional_embedding_constructed",
        "functional_action_embedding_claimed",
        "functional_action_embedding_selected",
        "functional_action_embedding_constructed",
        "C_k_action_embedding_selected",
        "C_k_action_embedding_constructed",
        "multiplier_field_selected",
        "multiplier_field_type_selected",
        "multiplier_action_route_selected",
        "multiplier_action_route_constructed",
        "penalty_functional_selected",
        "penalty_functional_defined",
        "penalty_route_selected",
        "penalty_route_constructed",
        "penalty_route_licensed",
        "direct_dynamical_law_interpretation_selected",
        "direct_force_law_claimed",
        "new_force_law_claimed",
        "varied_dynamical_equation_claimed",
        "C_k_action_variation_executed",
        "C_k_action_variation_authorized",
        "candidate_varied",
        "total_interaction_theorem_beyond_accepted_route_scope_claimed",
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
    ]:
        assert closeout[key] is False, key


def test_psi_a_u1_cexchange_admissibility_rule_closeout_nonclaim_boundary() -> None:
    closeout = _json(DEFAULT_OUT)
    for phrase in [
        "interaction exchange-balance admissibility rule",
        "C_exchange^{Apsi,nu}[g,A,psi] := nabla_mu T_total^{mu nu}",
        "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}",
        "C_exchange^{Apsi,nu} = 0",
        "admissibility-only",
        "not functionalized",
        "not action embedded",
        "not varied",
        "not a new force law",
        "not Maxwell closure",
        "not EM-QFT closure",
        "not QFT-GR closure",
        "not master-action promotion",
        "multiplier/action route blocked",
        "penalty route unlicensed",
        "no C_k action variation",
        "no direct dynamical-law interpretation",
        "no quantized electromagnetism",
        "no anomaly analysis",
        "no Standard Model derivation",
        "no Phase 2 authorization",
        "no empirical validation",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in closeout["non_claim_boundary"], phrase


def test_psi_a_u1_cexchange_admissibility_rule_closeout_validation_policy_is_bounded() -> None:
    closeout = _json(DEFAULT_OUT)
    policy = closeout["validation_policy"]
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
    assert closeout["full_toeformal_aggregate_passed"] is False
    assert closeout["full_toeformal_aggregate_failed"] is False
    assert closeout["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_cexchange_admissibility_rule_closeout_rotates_to_result_review() -> None:
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

    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET not in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert registry["C_exchange_admissibility_rule_closed"] == "yes"
    assert registry["interaction_exchange_balance_rule_closed"] == "yes"
    assert registry["C_exchange_rule_family_closed"] == "no"

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == "CLOSEOUT_ACCEPTED"
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["C_exchange_admissibility_rule_closeout_result"] == OUTCOME_ID
    assert consumed["C_exchange_admissibility_rule_closeout_result_review_result"] == (
        "PENDING"
    )
    assert consumed["admissibility_rule_closeout_prepared"] == "yes"
    assert consumed["C_exchange_admissibility_rule_closed"] == "yes"
    assert consumed["interaction_exchange_balance_rule_closed"] == "yes"
    assert consumed["C_exchange_rule_family_closed"] == "no"
    assert consumed["C_exchange_functional_embedding_claimed"] == "no"
    assert consumed["C_k_action_variation_executed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = _workstream(registry, NEXT_TARGET)
    assert active_row["status"] == "active"
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["active_lane"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["authorization_evidence"] == evidence
    assert active_row["report"] == str(DEFAULT_OUT.relative_to(REPO_ROOT)).replace("\\", "/")
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["packet_result"] == "PENDING"
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["result_token"] == OUTCOME_ID
    assert active_row["selected_next_target"] == NEXT_TARGET
    assert active_row["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert active_row["C_exchange_admissibility_rule_closeout_result"] == OUTCOME_ID
    assert active_row["C_exchange_admissibility_rule_closeout_result_review_result"] == (
        "PENDING"
    )
    assert active_row["admissibility_rule_closeout_prepared"] == "yes"
    assert active_row["closeout_result_review_prepared"] == "no"
    assert active_row["C_exchange_admissibility_rule_closed"] == "yes"
    assert active_row["interaction_exchange_balance_rule_closed"] == "yes"
    assert active_row["C_exchange_rule_family_closed"] == "no"
    assert active_row["C_exchange_functional_embedding_claimed"] == "no"
    assert active_row["functional_action_embedding_claimed"] == "no"
    assert active_row["multiplier_action_route_selected"] == "no"
    assert active_row["penalty_route_selected"] == "no"
    assert active_row["direct_dynamical_law_interpretation_selected"] == "no"
    assert active_row["C_k_action_variation_executed"] == "no"
    assert active_row["em_qft_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_psi_a_u1_cexchange_admissibility_rule_closeout_mirrors() -> None:
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
        CLOSEOUT_RESULT,
        PACKET_CLASSIFICATION,
        "ToeNativePsiAU1CExchangeAdmissibilityRuleCloseout",
        CONSUMED_TARGET,
        NEXT_TARGET,
        f"CURRENT_LIVE_NEXT_TARGET_v0: {NEXT_TARGET}",
        f"PREVIOUS_LIVE_NEXT_TARGET_v0: {CONSUMED_TARGET}",
        C_EXCHANGE_CONSTRAINT_ID,
        C_EXCHANGE_CONSTRAINT_FORM,
        C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
        C_EXCHANGE_ADMISSIBILITY_CONDITION,
        RULE_CLASSIFICATION,
        RULE_EPISTEMIC_STATUS,
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        EXCHANGE_TERM_CANCELLATION,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        MULTIPLIER_ACTION_FORM,
        PENALTY_ACTION_FORM,
        FOLLOW_ON_SYNTHESIS_TARGET,
        FOLLOW_ON_SYNTHESIS_OUTCOME,
        "TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_OUTCOME_v0",
        "PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_NONCLAIM_BOUNDARY_v0",
        "interaction exchange-balance admissibility rule",
        "not functionalized",
        "not action embedded",
        "not varied",
        "not a new force law",
        "no C_k action variation",
        "no direct dynamical-law interpretation",
        "no quantized electromagnetism",
        "no anomaly analysis",
        "no Standard Model derivation",
        "no Phase 2 authorization",
        "no empirical validation",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined, token


def test_psi_a_u1_cexchange_admissibility_rule_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_cexchange_admissibility_rule_closeout_gate.py"
    )
