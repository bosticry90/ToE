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
from formal.python.tools.toe_native_psi_a_u1_cexchange_functional_embedding_packet_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    DEFAULT_OUT as EMBEDDING_PACKET_PATH,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MULTIPLIER_ACTION_FORM,
    MULTIPLIER_ACTION_ROUTE_ID,
    OUTCOME_ID as EMBEDDING_PACKET_OUTCOME,
    PENALTY_ACTION_FORM,
    PENALTY_ROUTE_ID,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
)
from formal.python.tools.toe_native_psi_a_u1_cexchange_functional_embedding_packet_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    ARTIFACT_ID,
    BLOCKED_CLAIMS,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    build_toe_native_psi_a_u1_cexchange_functional_embedding_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_cexchange_functional_embedding_packet_result_review_report.py"
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


def test_psi_a_u1_cexchange_functional_embedding_review_files_exist() -> None:
    for path in [
        EMBEDDING_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_cexchange_functional_embedding_review_accepts_packet() -> None:
    packet = _json(EMBEDDING_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == EMBEDDING_PACKET_OUTCOME
    assert packet["selected_next_target"] == CONSUMED_TARGET

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
    assert review["embedding_packet_outcome"] == EMBEDDING_PACKET_OUTCOME
    assert build_toe_native_psi_a_u1_cexchange_functional_embedding_packet_result_review() == (
        review
    )


def test_psi_a_u1_cexchange_functional_embedding_review_carries_forms() -> None:
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
    assert review["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert review["multiplier_action_route_id"] == MULTIPLIER_ACTION_ROUTE_ID
    assert review["multiplier_action_form"] == MULTIPLIER_ACTION_FORM
    assert review["penalty_route_id"] == PENALTY_ROUTE_ID
    assert review["penalty_action_form"] == PENALTY_ACTION_FORM
    assert review["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert review["matter_sector_exchange_identity"] == MATTER_SECTOR_EXCHANGE_IDENTITY
    assert review["total_stress_energy_conservation_identity"] == (
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["accepted_review_findings_count"] == 9
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["blocked_claim_count"] == 11
    assert review["review_criteria_count"] == 11
    assert review["review_criteria_accepted_count"] == 11


def test_psi_a_u1_cexchange_functional_embedding_review_accepts_required_points() -> None:
    review = _json(DEFAULT_OUT)
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "functional_embedding_packet_consumed",
        "cexchange_candidate_preserved",
        "admissibility_only_route_selected",
        "multiplier_action_route_blocked",
        "penalty_route_unlicensed",
        "direct_dynamical_law_interpretation_blocked",
        "no_ck_action_variation",
        "no_functional_action_embedding",
        "no_total_interaction_theorem_beyond_route_scope",
        "no_closure_phase2_empirical_or_promotion",
        "admissibility_rule_closeout_selected_next",
    }
    for key in [
        "result_review_prepared",
        "result_review_accepted",
        "functional_embedding_result_review_prepared",
        "functional_embedding_result_review_accepted",
        "C_exchange_functional_embedding_result_review_accepted",
        "C_exchange_functional_embedding_packet_accepted",
        "C_exchange_candidate_preserved",
        "C_exchange_candidate_carried_forward",
        "admissibility_only_route_selected",
        "admissibility_only_route_accepted",
        "admissibility_only_interpretation_retained",
        "interaction_admissibility_rule_selected",
        "constraint_as_admissibility_rule_selected",
        "multiplier_action_route_blocked",
        "penalty_route_unlicensed",
        "direct_dynamical_law_interpretation_blocked",
        "no_C_k_action_variation_confirmed",
        "no_EM_QFT_closure_confirmed",
        "no_QFT_GR_closure_confirmed",
        "no_master_action_promotion_confirmed",
        "functional_embedding_packet_consumed",
        "admissibility_rule_closeout_selected_after_review",
        "C_exchange_admissibility_rule_closeout_authorized",
    ]:
        assert review[key] is True, key


def test_psi_a_u1_cexchange_functional_embedding_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    for key in [
        "C_exchange_closeout",
        "C_exchange_definition_closeout",
        "C_exchange_rule_family_closed",
        "admissibility_rule_closeout_prepared",
        "functional_action_embedding_claimed",
        "functional_action_embedding_selected",
        "functional_action_embedding_constructed",
        "C_exchange_functional_embedding_claimed",
        "C_exchange_functional_embedding_selected",
        "C_exchange_functional_embedding_constructed",
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
        "varied_dynamical_equation_claimed",
        "C_k_action_variation_executed",
        "C_k_action_variation_authorized",
        "candidate_varied",
        "action_embedding_claimed",
        "total_interaction_theorem_beyond_accepted_route_scope_claimed",
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
    for phrase in [
        "bounded C_exchange functional-embedding result review only",
        "C_exchange candidate is preserved",
        "admissibility-only route C_exchange^{Apsi,nu} = 0 is selected",
        "multiplier/action route is blocked",
        "penalty route is unlicensed",
        "direct dynamical-law interpretation is blocked",
        "no C_k action variation is executed",
        "selects C_exchange admissibility-rule closeout preparation next",
        "no C_exchange closeout",
        "no functional action embedding",
        "no multiplier field",
        "no penalty functional",
        "no total interaction theorem beyond accepted route scope",
        "no full Maxwell closure",
        "no quantized electromagnetism",
        "no anomaly analysis",
        "no Standard Model derivation",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in review["non_claim_boundary"], phrase


def test_psi_a_u1_cexchange_functional_embedding_review_validation_policy_is_bounded() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_review"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_status_for_review"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert review["full_toeformal_aggregate_passed"] is False
    assert review["full_toeformal_aggregate_failed"] is False
    assert review["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_cexchange_functional_embedding_review_rotates_to_closeout() -> None:
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

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["C_exchange_functional_embedding_packet_result"] == (
        EMBEDDING_PACKET_OUTCOME
    )
    assert consumed["C_exchange_functional_embedding_packet_result_review_result"] == (
        OUTCOME_ID
    )
    assert consumed["admissibility_only_route_selected"] == "yes"
    assert consumed["multiplier_action_route_blocked"] == "yes"
    assert consumed["penalty_route_unlicensed"] == "yes"
    assert consumed["direct_dynamical_law_interpretation_blocked"] == "yes"
    assert consumed["C_k_action_variation_executed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = _workstream(registry, NEXT_TARGET)
    assert active_row["status"] == "active"
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["active_lane"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["packet_result"] == "PENDING"
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["result_token"] == OUTCOME_ID
    assert active_row["selected_next_target"] == NEXT_TARGET
    assert active_row["C_exchange_functional_embedding_packet_result_review_result"] == (
        OUTCOME_ID
    )
    assert active_row["C_exchange_admissibility_rule_closeout_result"] == "PENDING"
    assert active_row["admissibility_rule_closeout_prepared"] == "no"
    assert active_row["C_exchange_admissibility_rule_closeout_authorized"] == "yes"
    assert active_row["admissibility_only_route_selected"] == "yes"
    assert active_row["functional_action_embedding_claimed"] == "no"
    assert active_row["multiplier_field_selected"] == "no"
    assert active_row["penalty_functional_selected"] == "no"
    assert active_row["C_k_action_variation_executed"] == "no"


def test_psi_a_u1_cexchange_functional_embedding_review_mirrors() -> None:
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
        "ToeNativePsiAU1CExchangeFunctionalEmbeddingPacketResultReview",
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
        "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "bounded C_exchange functional-embedding result review only",
        "admissibility-only route C_exchange^{Apsi,nu} = 0 is selected",
        "multiplier/action route is blocked",
        "penalty route is unlicensed",
        "no functional action embedding",
        "no multiplier field",
        "no penalty functional",
        "no total interaction theorem beyond accepted route scope",
        "no full Maxwell closure",
        "no quantized electromagnetism",
        "no anomaly analysis",
        "no Standard Model derivation",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined, token


def test_psi_a_u1_cexchange_functional_embedding_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_cexchange_functional_embedding_packet_result_review_gate.py"
    )
