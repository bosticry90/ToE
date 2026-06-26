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
from formal.python.tools.toe_native_psi_a_u1_cexchange_constraint_candidate_packet_report import (
    BLOCKED_CLAIMS,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    DEFAULT_OUT as CANDIDATE_PACKET_PATH,
    EXCHANGE_TERM_CANCELLATION,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAUGE_SECTOR_EXCHANGE_TERM,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MATTER_SECTOR_EXCHANGE_TERM,
    OUTCOME_ID as CANDIDATE_PACKET_OUTCOME,
    PACKET_RESULT as CANDIDATE_PACKET_RESULT,
    TOTAL_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
)
from formal.python.tools.toe_native_psi_a_u1_cexchange_constraint_candidate_packet_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    ARTIFACT_ID,
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
    build_toe_native_psi_a_u1_cexchange_constraint_candidate_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_cexchange_constraint_candidate_packet_result_review_report.py"
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


def test_psi_a_u1_cexchange_constraint_candidate_review_files_exist() -> None:
    for path in [
        CANDIDATE_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_cexchange_constraint_candidate_review_accepts_candidate() -> None:
    packet = _json(CANDIDATE_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == CANDIDATE_PACKET_OUTCOME
    assert packet["packet_result"] == CANDIDATE_PACKET_RESULT
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
    assert review["candidate_packet_outcome"] == CANDIDATE_PACKET_OUTCOME
    assert review["candidate_packet_result"] == CANDIDATE_PACKET_RESULT
    assert build_toe_native_psi_a_u1_cexchange_constraint_candidate_packet_result_review() == (
        review
    )


def test_psi_a_u1_cexchange_constraint_candidate_review_carries_forms_exactly() -> None:
    review = _json(DEFAULT_OUT)
    assert review["C_exchange_constraint_id"] == C_EXCHANGE_CONSTRAINT_ID
    assert review["C_exchange_constraint_form"] == C_EXCHANGE_CONSTRAINT_FORM
    assert review["C_exchange_total_stress_energy_form"] == (
        C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
    )
    assert review["C_exchange_admissibility_condition"] == (
        C_EXCHANGE_ADMISSIBILITY_CONDITION
    )
    assert review["C_exchange_plain_meaning"] == C_EXCHANGE_PLAIN_MEANING
    assert review["C_exchange_candidate_scope"] == C_EXCHANGE_CANDIDATE_SCOPE
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["accepted_review_findings_count"] == 5
    assert review["review_criteria_count"] == 9
    assert review["review_criteria_accepted_count"] == 9
    assert review["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert review["gauge_sector_exchange_term"] == GAUGE_SECTOR_EXCHANGE_TERM
    assert review["matter_sector_exchange_identity"] == MATTER_SECTOR_EXCHANGE_IDENTITY
    assert review["matter_sector_exchange_term"] == MATTER_SECTOR_EXCHANGE_TERM
    assert review["exchange_term_cancellation"] == EXCHANGE_TERM_CANCELLATION
    assert review["total_conservation_identity"] == TOTAL_CONSERVATION_IDENTITY
    assert review["total_stress_energy_object"] == TOTAL_STRESS_ENERGY_OBJECT
    assert review["total_stress_energy_conservation_identity"] == (
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )


def test_psi_a_u1_cexchange_constraint_candidate_review_accepts_required_points() -> None:
    review = _json(DEFAULT_OUT)
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "cexchange_candidate_packet_consumed",
        "cexchange_candidate_recorded",
        "candidate_based_on_total_conservation_route",
        "total_stress_energy_preserved",
        "admissibility_condition_recorded",
        "admissibility_only_status_preserved",
        "functionalization_action_variation_routes_blocked",
        "closure_phase2_empirical_and_promotion_blockers_preserved",
        "functional_embedding_packet_selected_next",
    }
    for key in [
        "review_executed",
        "result_review_prepared",
        "result_review_accepted",
        "C_exchange_constraint_candidate_result_review_accepted",
        "C_exchange_candidate_accepted",
        "C_exchange_candidate_recorded",
        "C_exchange_constraint_candidate_recorded",
        "total_exchange_conservation_residual_candidate_accepted",
        "candidate_based_on_accepted_total_conservation_route",
        "T_total_preserved",
        "total_stress_energy_object_preserved",
        "C_exchange_admissibility_condition_recorded",
        "admissibility_only_status_preserved",
        "candidate_not_functionalized",
        "candidate_not_action_embedded",
        "candidate_not_varied",
        "functional_embedding_packet_selected_after_review",
        "functional_embedding_packet_authorized_here",
        "C_exchange_functional_embedding_packet_selected",
        "C_exchange_functional_embedding_packet_authorized",
    ]:
        assert review[key] is True, key


def test_psi_a_u1_cexchange_constraint_candidate_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["blocked_claim_count"] == 14
    for key in [
        "C_exchange_closeout",
        "C_exchange_definition_closeout",
        "C_exchange_rule_family_closed",
        "C_exchange_functional_embedding_claimed",
        "C_exchange_functional_embedding_constructed_here",
        "C_exchange_functional_embedding_constructed",
        "multiplier_action_route_selected",
        "multiplier_action_route_constructed",
        "penalty_route_selected",
        "penalty_route_constructed",
        "direct_dynamical_law_interpretation_selected",
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
        assert review[key] is False, key
    assert review["direct_dynamical_law_interpretation_blocked"] is True
    for phrase in [
        "bounded C_exchange constraint-candidate result review only",
        "C_exchange candidate was recorded",
        "accepted psi-A total-conservation route",
        "T_total = T_A + T_psi is preserved",
        "C_exchange^{Apsi,nu} = 0 is recorded",
        "remains admissibility-only",
        "selects C_exchange functional embedding packet preparation next",
        "no C_exchange closeout",
        "no C_exchange functional embedding",
        "no multiplier/action route",
        "no penalty route",
        "no C_k action variation",
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
        assert phrase in review["non_claim_boundary"], phrase


def test_psi_a_u1_cexchange_constraint_candidate_review_validation_policy_is_bounded() -> None:
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


def test_psi_a_u1_cexchange_constraint_candidate_review_rotates_to_embedding_target() -> None:
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
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["C_exchange_constraint_candidate_packet_result"] == (
        CANDIDATE_PACKET_OUTCOME
    )
    assert consumed["C_exchange_constraint_candidate_packet_result_review_result"] == (
        OUTCOME_ID
    )
    assert consumed["C_exchange_candidate_accepted"] == "yes"
    assert consumed["admissibility_only_status_preserved"] == "yes"
    assert consumed["C_exchange_functional_embedding_packet_authorized"] == "yes"
    assert consumed["C_exchange_functional_embedding_claimed"] == "no"
    assert consumed["multiplier_action_route_selected"] == "no"
    assert consumed["penalty_route_selected"] == "no"
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
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["packet_result"] == "PENDING"
    assert active_row["C_exchange_constraint_candidate_packet_result"] == (
        CANDIDATE_PACKET_OUTCOME
    )
    assert active_row["C_exchange_constraint_candidate_packet_result_review_result"] == (
        OUTCOME_ID
    )
    assert active_row["C_exchange_functional_embedding_packet_result"] == "PENDING"
    assert active_row["C_exchange_functional_embedding_packet_selected"] == "yes"
    assert active_row["C_exchange_functional_embedding_packet_authorized"] == "yes"
    assert active_row["functional_embedding_packet_prepared"] == "no"
    assert active_row["multiplier_action_route_selected"] == "no"
    assert active_row["penalty_route_selected"] == "no"
    assert active_row["direct_dynamical_law_interpretation_blocked"] == "yes"
    assert active_row["C_exchange_functional_embedding_claimed"] == "no"
    assert active_row["C_k_action_variation_executed"] == "no"


def test_psi_a_u1_cexchange_constraint_candidate_review_mirrors() -> None:
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
        "ToeNativePsiAU1CExchangeConstraintCandidateResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        f"CURRENT_LIVE_NEXT_TARGET_v0: {NEXT_TARGET}",
        f"PREVIOUS_LIVE_NEXT_TARGET_v0: {CONSUMED_TARGET}",
        C_EXCHANGE_CONSTRAINT_ID,
        C_EXCHANGE_CONSTRAINT_FORM,
        C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
        C_EXCHANGE_ADMISSIBILITY_CONDITION,
        C_EXCHANGE_CANDIDATE_SCOPE,
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        "TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "bounded C_exchange constraint-candidate result review only",
        "C_exchange candidate was recorded",
        "T_total = T_A + T_psi is preserved",
        "selects C_exchange functional embedding packet preparation next",
        "no C_exchange closeout",
        "no C_exchange functional embedding",
        "no multiplier/action route",
        "no penalty route",
        "no C_k action variation",
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


def test_psi_a_u1_cexchange_constraint_candidate_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_cexchange_constraint_candidate_packet_result_review_gate.py"
    )
