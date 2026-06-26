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
from formal.python.tools.toe_native_psi_a_u1_total_stress_energy_conservation_route_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    BLOCKED_CLAIMS,
    CONSUMED_TARGET,
    C_EXCHANGE_CONSTRAINT_CANDIDATE_EQUATION,
    C_EXCHANGE_CONSTRAINT_CANDIDATE_TO_PREPARE,
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
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    TOTAL_CONSERVATION_IDENTITY,
    TOTAL_PACKET_OUTCOME,
    TOTAL_PACKET_PATH,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
    build_toe_native_psi_a_u1_total_stress_energy_conservation_route_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_total_stress_energy_conservation_route_result_review_report.py"
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


def test_psi_a_u1_total_stress_energy_conservation_route_result_review_files_exist() -> None:
    for path in [
        TOTAL_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_total_stress_energy_conservation_route_result_review_builds() -> None:
    packet = _json(TOTAL_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == TOTAL_PACKET_OUTCOME
    assert packet["selected_next_target"] == CONSUMED_TARGET

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
    assert (
        build_toe_native_psi_a_u1_total_stress_energy_conservation_route_result_review()
        == review
    )


def test_psi_a_u1_total_stress_energy_conservation_route_result_review_accepts_total_route() -> None:
    review = _json(DEFAULT_OUT)
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["accepted_review_findings_count"] == 5
    assert review["review_criteria_count"] == 8
    assert review["review_criteria_accepted_count"] == 8
    assert review["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert review["gauge_sector_exchange_term"] == GAUGE_SECTOR_EXCHANGE_TERM
    assert review["matter_sector_exchange_identity"] == MATTER_SECTOR_EXCHANGE_IDENTITY
    assert review["matter_sector_exchange_term"] == MATTER_SECTOR_EXCHANGE_TERM
    assert review["exchange_term_cancellation"] == EXCHANGE_TERM_CANCELLATION
    assert review["total_stress_energy_object"] == TOTAL_STRESS_ENERGY_OBJECT
    assert review["total_conservation_identity"] == TOTAL_CONSERVATION_IDENTITY
    assert review["total_stress_energy_conservation_identity"] == (
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    assert review["C_exchange_constraint_candidate_to_prepare"] == (
        C_EXCHANGE_CONSTRAINT_CANDIDATE_TO_PREPARE
    )
    assert review["C_exchange_constraint_candidate_equation_to_prepare"] == (
        C_EXCHANGE_CONSTRAINT_CANDIDATE_EQUATION
    )
    for key in [
        "total_conservation_route_result_review_accepted",
        "total_stress_energy_conservation_route_accepted",
        "total_conservation_route_accepted",
        "total_conservation_route_recorded",
        "total_conservation_identity_recorded",
        "total_stress_energy_conservation_identity_recorded",
        "total_conservation_proved",
        "total_stress_energy_conservation_proved",
        "bounded_total_conservation_route_accepted",
        "matter_gauge_exchange_balance_route_accepted",
        "gauge_sector_exchange_route_already_accepted",
        "matter_sector_exchange_route_already_accepted",
        "exchange_terms_cancel",
        "exchange_terms_cancel_accepted",
        "total_stress_energy_object_preserved",
        "combined_matter_gauge_system_conserved",
        "matter_gauge_interaction_balance_chain_complete",
        "C_exchange_candidate_ready_for_later_packet",
        "C_exchange_candidate_packet_selected_after_review",
        "C_exchange_candidate_packet_authorized_here",
        "C_exchange_constraint_candidate_packet_selected",
        "C_exchange_constraint_candidate_packet_authorized",
    ]:
        assert review[key] is True, key


def test_psi_a_u1_total_stress_energy_conservation_route_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["blocked_claim_count"] == 12
    for key in [
        "C_exchange_constraint_candidate_packet_prepared_here",
        "C_exchange_closeout",
        "C_exchange_definition_closeout",
        "C_exchange_rule_family_closed",
        "C_exchange_functional_embedding_claimed",
        "C_k_action_variation_executed",
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
        "bounded total stress-energy conservation route result review only",
        "accepted gauge-sector exchange route",
        "accepted matter-sector exchange route",
        "exchange-term cancellation",
        "T_total = T_A + T_psi",
        "nabla_mu T_total^{mu nu} = 0",
        "admissibility-only candidate",
        "no C_exchange closeout",
        "no C_exchange functional embedding",
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


def test_psi_a_u1_total_stress_energy_conservation_route_result_review_validation_policy_is_bounded() -> None:
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


def test_psi_a_u1_total_stress_energy_conservation_route_result_review_rotates_to_cexchange_packet() -> None:
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
    assert consumed["total_conservation_route_packet_result_review_result"] == (
        OUTCOME_ID
    )
    assert consumed["total_conservation_route_result_review_accepted"] == "yes"
    assert consumed["C_exchange_candidate_packet_selected_after_review"] == "yes"
    assert consumed["C_exchange_candidate_packet_authorized_here"] == "yes"
    assert consumed["C_exchange_closeout"] == "no"
    assert consumed["C_exchange_functional_embedding_claimed"] == "no"

    active_row = _workstream(registry, NEXT_TARGET)
    if is_current:
        assert active_row["status"] == "active"
        assert active_row["workstream_id"] == NEXT_TARGET
        assert active_row["active_lane"] == NEXT_TARGET
        assert active_row["authorized_next_strict_target"] == NEXT_TARGET
        assert active_row["authorized_target"] == NEXT_TARGET
        assert active_row["consumed_target"] == CONSUMED_TARGET
        assert active_row["packet_result"] == "PENDING"
    assert active_row["total_conservation_route_packet_result_review_result"] == (
        OUTCOME_ID
    )
    assert active_row["C_exchange_constraint_candidate_packet_result"] == "PENDING"
    assert active_row["C_exchange_candidate_packet_selected_after_review"] == "yes"
    assert active_row["C_exchange_candidate_packet_authorized_here"] == "yes"
    assert active_row["C_exchange_closeout"] == "no"
    assert active_row["C_exchange_functional_embedding_claimed"] == "no"


def test_psi_a_u1_total_stress_energy_conservation_route_result_review_mirrors() -> None:
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
        "ToeNativePsiAU1TotalStressEnergyConservationRouteResultReview",
        NEXT_TARGET,
        f"CURRENT_LIVE_NEXT_TARGET_v0: {NEXT_TARGET}",
        f"PREVIOUS_LIVE_NEXT_TARGET_v0: {CONSUMED_TARGET}",
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        EXCHANGE_TERM_CANCELLATION,
        TOTAL_CONSERVATION_IDENTITY,
        TOTAL_STRESS_ENERGY_OBJECT,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        C_EXCHANGE_CONSTRAINT_CANDIDATE_TO_PREPARE,
        C_EXCHANGE_CONSTRAINT_CANDIDATE_EQUATION,
        "no C_exchange closeout",
        "no C_exchange functional embedding",
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
        assert token in joined


def test_psi_a_u1_total_stress_energy_conservation_route_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_total_stress_energy_conservation_route_result_review_gate.py"
    )
