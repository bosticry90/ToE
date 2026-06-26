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
from formal.python.tools.toe_native_psi_a_u1_cexchange_admissibility_rule_closeout_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
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
    CLOSEOUT_OUTCOME,
    CLOSEOUT_PATH,
    CLOSEOUT_RESULT,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    EXCHANGE_TERM_CANCELLATION,
    FOLLOW_ON_SYNTHESIS_OUTCOME,
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
    REVIEW_RESULT,
    RULE_CLASSIFICATION,
    RULE_EPISTEMIC_STATUS,
    SCHEMA_ID,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
    build_toe_native_psi_a_u1_cexchange_admissibility_rule_closeout_result_review,
)
from formal.python.tools.toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_packet_report import (
    NEXT_TARGET as SYNTHESIS_REVIEW_TARGET,
    OUTCOME_ID as SYNTHESIS_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_cexchange_admissibility_rule_closeout_result_review_report.py"
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


def test_psi_a_u1_cexchange_closeout_result_review_files_exist() -> None:
    for path in [
        CLOSEOUT_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_cexchange_closeout_result_review_accepts_closeout() -> None:
    closeout = _json(CLOSEOUT_PATH)
    review = _json(DEFAULT_OUT)
    assert closeout["outcome_id"] == CLOSEOUT_OUTCOME
    assert closeout["closeout_result"] == CLOSEOUT_RESULT
    assert closeout["selected_next_target"] == CONSUMED_TARGET

    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_result"] == OUTCOME_ID
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_toe_native_psi_a_u1_cexchange_admissibility_rule_closeout_result_review() == (
        review
    )


def test_psi_a_u1_cexchange_closeout_result_review_preserves_forms() -> None:
    review = _json(DEFAULT_OUT)
    assert review["C_exchange_constraint_id"] == C_EXCHANGE_CONSTRAINT_ID
    assert review["C_exchange_constraint_form"] == C_EXCHANGE_CONSTRAINT_FORM
    assert review["C_exchange_total_stress_energy_form"] == (
        C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
    )
    assert review["C_exchange_admissibility_condition"] == (
        C_EXCHANGE_ADMISSIBILITY_CONDITION
    )
    assert review["C_exchange_candidate_scope"] == C_EXCHANGE_CANDIDATE_SCOPE
    assert review["C_exchange_plain_meaning"] == C_EXCHANGE_PLAIN_MEANING
    assert review["admissibility_only_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert review["admissibility_only_route_status"] == ADMISSIBILITY_ONLY_ROUTE_STATUS
    assert review["rule_classification"] == RULE_CLASSIFICATION
    assert review["rule_epistemic_status"] == RULE_EPISTEMIC_STATUS
    assert review["source_current"] == SOURCE_CURRENT
    assert review["sourced_gauge_route"] == SOURCED_GAUGE_ROUTE
    assert review["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert review["matter_sector_exchange_identity"] == MATTER_SECTOR_EXCHANGE_IDENTITY
    assert review["exchange_term_cancellation"] == EXCHANGE_TERM_CANCELLATION
    assert review["total_stress_energy_object"] == TOTAL_STRESS_ENERGY_OBJECT
    assert review["total_stress_energy_conservation_identity"] == (
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    assert review["multiplier_action_route_id"] == MULTIPLIER_ACTION_ROUTE_ID
    assert review["multiplier_action_form"] == MULTIPLIER_ACTION_FORM
    assert review["penalty_route_id"] == PENALTY_ROUTE_ID
    assert review["penalty_action_form"] == PENALTY_ACTION_FORM
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["accepted_review_findings_count"] == 10
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["blocked_claim_count"] == 14
    assert review["review_criteria_count"] == 9
    assert review["review_criteria_accepted_count"] == 9


def test_psi_a_u1_cexchange_closeout_result_review_accepts_required_points() -> None:
    review = _json(DEFAULT_OUT)
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "closeout_consumed",
        "interaction_exchange_balance_rule_accepted",
        "admissibility_only_status_preserved",
        "cexchange_candidate_preserved",
        "accepted_total_conservation_route_basis_preserved",
        "exchange_halves_context_preserved",
        "no_functional_embedding_multiplier_penalty_or_ck_variation",
        "closure_and_promotion_claims_blocked",
        "synthesis_packet_selected_next",
    }
    for key in [
        "closeout_result_review_prepared",
        "closeout_result_review_accepted",
        "C_exchange_closeout_accepted",
        "C_exchange_admissibility_rule_closed",
        "C_exchange_rule_closed_as_interaction_exchange_balance_rule",
        "interaction_exchange_balance_rule_closed",
        "admissibility_only_status_preserved",
        "based_on_accepted_total_stress_energy_conservation_route",
        "C_exchange_candidate_preserved",
        "T_total_preserved",
    ]:
        assert review[key] is True, key


def test_psi_a_u1_cexchange_closeout_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    for key in [
        "follow_on_synthesis_prepared",
        "interaction_exchange_rule_family_synthesis_packet_prepared",
        "interaction_exchange_rule_family_synthesized",
        "functional_action_embedding_claimed",
        "functional_action_embedding_selected",
        "functional_action_embedding_constructed",
        "C_exchange_functional_embedding_claimed",
        "C_exchange_functional_embedding_selected",
        "C_exchange_functional_embedding_constructed",
        "C_k_action_embedding_selected",
        "C_k_action_embedding_constructed",
        "multiplier_field_selected",
        "multiplier_action_route_selected",
        "multiplier_action_route_constructed",
        "penalty_functional_selected",
        "penalty_route_selected",
        "penalty_route_constructed",
        "penalty_route_licensed",
        "direct_dynamical_law_interpretation_selected",
        "direct_force_law_claimed",
        "new_force_law_claimed",
        "C_k_action_variation_executed",
        "C_k_action_variation_authorized",
        "candidate_varied",
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
        assert review[key] is False, key


def test_psi_a_u1_cexchange_closeout_result_review_nonclaim_boundary() -> None:
    boundary = _json(DEFAULT_OUT)["non_claim_boundary"]
    for phrase in [
        "accepts the C_exchange closeout only",
        "C_exchange remains admissibility-only",
        "accepted psi-A total-conservation route",
        "no functional embedding",
        "no multiplier/action route",
        "no penalty route",
        "no C_k variation",
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
        assert phrase in boundary, phrase


def test_psi_a_u1_cexchange_closeout_result_review_validation_policy_is_bounded() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_review"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_status_for_review"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert review["full_toeformal_aggregate_passed"] is False
    assert review["full_toeformal_aggregate_failed"] is False
    assert review["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_cexchange_closeout_result_review_rotates_to_synthesis() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = str(LEAN_PACKET_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["result_token"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["C_exchange_admissibility_rule_closeout_result"] == CLOSEOUT_OUTCOME
    assert consumed["C_exchange_admissibility_rule_closeout_result_review_result"] == (
        OUTCOME_ID
    )
    assert consumed["closeout_result_review_prepared"] == "yes"
    assert consumed["interaction_exchange_rule_family_synthesis_packet_prepared"] == "no"
    assert consumed["interaction_exchange_rule_family_synthesized"] == "no"
    assert consumed["C_k_action_variation_executed"] == "no"
    assert consumed["em_qft_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    next_row = _workstream(registry, NEXT_TARGET)
    assert next_row["workstream_id"] == NEXT_TARGET
    assert next_row["C_exchange_admissibility_rule_closeout_result_review_result"] == (
        OUTCOME_ID
    )
    assert next_row["C_exchange_remains_admissibility_only"] == "yes"
    assert next_row["C_exchange_rule_preserved"] == "yes"
    assert next_row["C_k_action_variation_executed"] == "no"
    assert next_row["em_qft_closure_claimed"] == "no"
    assert next_row["qft_gr_closure_claimed"] == "no"
    assert next_row["master_action_promoted"] == "no"

    if is_current:
        assert NEXT_TARGET not in registry["paused_lanes"]
        assert next_row["status"] == "active"
        assert next_row["packet_result"] == "PENDING"
        assert next_row["outcome_id"] == OUTCOME_ID
        assert next_row["selected_next_target"] == NEXT_TARGET
    else:
        assert NEXT_TARGET in registry["paused_lanes"]
        assert next_row["status"] == "paused"
        assert next_row["packet_result"] == FOLLOW_ON_SYNTHESIS_OUTCOME
        assert next_row["outcome_id"] == SYNTHESIS_OUTCOME
        assert next_row["result_token"] == SYNTHESIS_OUTCOME
        assert next_row["selected_next_target"] == SYNTHESIS_REVIEW_TARGET
        assert next_row["interaction_exchange_rule_family_synthesis_packet_prepared"] == "yes"
        assert next_row["interaction_exchange_rule_family_synthesized"] == "yes"


def test_psi_a_u1_cexchange_closeout_result_review_mirrors() -> None:
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
        REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        "ToeNativePsiAU1CExchangeAdmissibilityRuleCloseoutResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
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
        "TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "C_exchange remains admissibility-only",
        "no functional embedding",
        "no multiplier/action route",
        "no penalty route",
        "no C_k variation",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined, token


def test_psi_a_u1_cexchange_closeout_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_cexchange_admissibility_rule_closeout_result_review_gate.py"
    )
