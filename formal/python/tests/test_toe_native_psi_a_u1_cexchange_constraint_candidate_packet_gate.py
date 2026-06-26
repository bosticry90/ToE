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
    ALLOWED_CLAIMS,
    ARTIFACT_ID,
    BLOCKED_CLAIMS,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    EXCHANGE_TERM_CANCELLATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAUGE_SECTOR_EXCHANGE_TERM,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MATTER_SECTOR_EXCHANGE_TERM,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    TOTAL_CONSERVATION_IDENTITY,
    TOTAL_REVIEW_OUTCOME,
    TOTAL_REVIEW_PATH,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
    build_toe_native_psi_a_u1_cexchange_constraint_candidate_packet,
)
from formal.python.tools.toe_native_psi_a_u1_cexchange_constraint_candidate_packet_result_review_report import (
    NEXT_TARGET as CEXCHANGE_FUNCTIONAL_EMBEDDING_TARGET,
    OUTCOME_ID as CANDIDATE_RESULT_REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_cexchange_constraint_candidate_packet_report.py"
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


def test_psi_a_u1_cexchange_constraint_candidate_packet_files_exist() -> None:
    for path in [
        TOTAL_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_cexchange_constraint_candidate_packet_builds() -> None:
    review = _json(TOTAL_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert review["outcome_id"] == TOTAL_REVIEW_OUTCOME
    assert review["selected_next_target"] == CONSUMED_TARGET

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
    assert build_toe_native_psi_a_u1_cexchange_constraint_candidate_packet() == (
        packet
    )


def test_psi_a_u1_cexchange_constraint_candidate_packet_records_candidate() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["C_exchange_constraint_id"] == C_EXCHANGE_CONSTRAINT_ID
    assert packet["C_exchange_constraint_form"] == C_EXCHANGE_CONSTRAINT_FORM
    assert packet["C_exchange_total_stress_energy_form"] == (
        C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
    )
    assert packet["C_exchange_admissibility_condition"] == (
        C_EXCHANGE_ADMISSIBILITY_CONDITION
    )
    assert packet["C_exchange_plain_meaning"] == C_EXCHANGE_PLAIN_MEANING
    assert packet["C_exchange_candidate_scope"] == C_EXCHANGE_CANDIDATE_SCOPE
    assert packet["allowed_claims"] == ALLOWED_CLAIMS
    assert packet["allowed_claim_count"] == 6
    assert packet["candidate_row_count"] == 8
    assert packet["candidate_row_accepted_count"] == 8
    assert packet["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert packet["gauge_sector_exchange_term"] == GAUGE_SECTOR_EXCHANGE_TERM
    assert packet["matter_sector_exchange_identity"] == MATTER_SECTOR_EXCHANGE_IDENTITY
    assert packet["matter_sector_exchange_term"] == MATTER_SECTOR_EXCHANGE_TERM
    assert packet["exchange_term_cancellation"] == EXCHANGE_TERM_CANCELLATION
    assert packet["total_conservation_identity"] == TOTAL_CONSERVATION_IDENTITY
    assert packet["total_stress_energy_object"] == TOTAL_STRESS_ENERGY_OBJECT
    assert packet["total_stress_energy_conservation_identity"] == (
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    for key in [
        "C_exchange_constraint_candidate_packet_prepared",
        "C_exchange_candidate_recorded",
        "C_exchange_constraint_candidate_recorded",
        "total_exchange_conservation_residual_candidate_recorded",
        "candidate_based_on_accepted_total_conservation_route",
        "candidate_is_admissibility_only",
        "candidate_not_functionalized",
        "candidate_not_action_embedded",
        "candidate_not_varied",
        "total_stress_energy_object_preserved",
        "total_conservation_route_consumed",
        "total_stress_energy_conservation_route_consumed",
        "interaction_exchange_admissibility_candidate_recorded",
        "C_exchange_constraint_candidate_packet_result_review_selected",
        "C_exchange_constraint_candidate_packet_result_review_authorized",
    ]:
        assert packet[key] is True, key


def test_psi_a_u1_cexchange_constraint_candidate_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    assert packet["blocked_claim_count"] == 14
    for key in [
        "C_exchange_closeout",
        "C_exchange_definition_closeout",
        "C_exchange_rule_family_closed",
        "C_exchange_functional_embedding_claimed",
        "C_exchange_functional_embedding_selected",
        "C_exchange_functional_embedding_constructed",
        "C_exchange_functional_embedding_packet_prepared_here",
        "multiplier_action_route_selected",
        "multiplier_action_route_constructed",
        "penalty_route_selected",
        "penalty_route_constructed",
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
        "bounded C_exchange constraint-candidate packet only",
        "admissibility-only candidate",
        "not functionalized",
        "not action-embedded",
        "not varied",
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
        assert phrase in packet["non_claim_boundary"], phrase


def test_psi_a_u1_cexchange_constraint_candidate_packet_validation_policy_is_bounded() -> None:
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


def test_psi_a_u1_cexchange_constraint_candidate_packet_rotates_to_review_target() -> None:
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
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["C_exchange_constraint_candidate_packet_result"] == OUTCOME_ID
    assert consumed["C_exchange_candidate_recorded"] == "yes"
    assert consumed["candidate_is_admissibility_only"] == "yes"
    assert consumed["C_exchange_functional_embedding_claimed"] == "no"
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
        assert active_row["outcome_id"] == OUTCOME_ID
        assert active_row["packet_result"] == "PENDING"
        assert active_row["C_exchange_constraint_candidate_packet_result"] == OUTCOME_ID
        assert active_row["C_exchange_constraint_candidate_packet_result_review_result"] == (
            "PENDING"
        )
    else:
        assert active_row["status"] == "paused"
        assert active_row["review_result"] == CANDIDATE_RESULT_REVIEW_OUTCOME
        assert active_row["packet_result"] == CANDIDATE_RESULT_REVIEW_OUTCOME
        assert active_row["selected_next_target"] == CEXCHANGE_FUNCTIONAL_EMBEDDING_TARGET
        assert active_row["C_exchange_constraint_candidate_packet_result"] == OUTCOME_ID
        assert active_row["C_exchange_constraint_candidate_packet_result_review_result"] == (
            CANDIDATE_RESULT_REVIEW_OUTCOME
        )
    assert active_row["C_exchange_constraint_candidate_packet_result_review_selected"] == (
        "yes"
    )
    assert active_row["C_exchange_constraint_candidate_packet_result_review_authorized"] == (
        "yes"
    )
    assert active_row["C_exchange_functional_embedding_claimed"] == "no"
    assert active_row["C_k_action_variation_executed"] == "no"


def test_psi_a_u1_cexchange_constraint_candidate_packet_mirrors() -> None:
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
        "ToeNativePsiAU1CExchangeConstraintCandidatePacket",
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


def test_psi_a_u1_cexchange_constraint_candidate_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_cexchange_constraint_candidate_packet_gate.py"
    )
