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
from formal.python.tools.toe_native_psi_a_u1_total_stress_energy_conservation_route_packet_report import (
    BLOCKED_CLAIMS,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    EXCHANGE_TERM_CANCELLATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAUGE_SECTOR_EXCHANGE_TERM,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_RESULT_REVIEW_OUTCOME,
    MATTER_RESULT_REVIEW_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MATTER_SECTOR_EXCHANGE_TERM,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SOURCE_CURRENT,
    TOTAL_CONSERVATION_IDENTITY,
    TOTAL_DIVERGENCE_SUM_IDENTITY,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
    build_toe_native_psi_a_u1_total_stress_energy_conservation_route_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_total_stress_energy_conservation_route_packet_report.py"
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


def test_psi_a_u1_total_stress_energy_conservation_route_packet_files_exist() -> None:
    for path in [
        MATTER_RESULT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_total_stress_energy_conservation_route_packet_builds() -> None:
    consumed = _json(MATTER_RESULT_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert consumed["outcome_id"] == MATTER_RESULT_REVIEW_OUTCOME
    assert consumed["selected_next_target"] == CONSUMED_TARGET

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
    assert (
        build_toe_native_psi_a_u1_total_stress_energy_conservation_route_packet()
        == packet
    )


def test_psi_a_u1_total_stress_energy_conservation_route_packet_constructs_total_route() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["source_current"] == SOURCE_CURRENT
    assert packet["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert packet["gauge_sector_exchange_term"] == GAUGE_SECTOR_EXCHANGE_TERM
    assert packet["matter_sector_exchange_identity"] == MATTER_SECTOR_EXCHANGE_IDENTITY
    assert packet["matter_sector_exchange_term"] == MATTER_SECTOR_EXCHANGE_TERM
    assert packet["total_divergence_sum_identity"] == TOTAL_DIVERGENCE_SUM_IDENTITY
    assert packet["exchange_term_cancellation"] == EXCHANGE_TERM_CANCELLATION
    assert packet["total_conservation_identity"] == TOTAL_CONSERVATION_IDENTITY
    assert packet["total_stress_energy_object"] == TOTAL_STRESS_ENERGY_OBJECT
    assert packet["total_stress_energy_conservation_identity"] == (
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    assert packet["route_step_count"] == 7
    assert packet["route_steps"][-1]["statement"] == (
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    for key in [
        "total_stress_energy_conservation_route_packet_prepared",
        "total_conservation_route_packet_prepared",
        "total_conservation_route_constructed",
        "total_conservation_route_recorded",
        "total_conservation_identity_recorded",
        "total_stress_energy_conservation_identity_recorded",
        "total_stress_energy_conservation_route_recorded",
        "total_conservation_proved",
        "total_conservation_proved_here",
        "total_stress_energy_conservation_proved",
        "bounded_total_conservation_route_constructed",
        "bounded_total_stress_energy_conservation_route_constructed",
        "exchange_terms_cancel",
        "gauge_matter_exchange_balance_recorded",
        "combined_matter_gauge_system_conserved",
        "matter_gauge_interaction_balance_chain_complete",
        "gauge_sector_exchange_route_accepted",
        "matter_sector_exchange_route_accepted",
        "both_exchange_halves_recorded",
        "C_exchange_candidate_ready_for_later_packet",
        "total_conservation_route_packet_result_review_selected",
        "total_conservation_route_packet_result_review_authorized",
    ]:
        assert packet[key] is True, key


def test_psi_a_u1_total_stress_energy_conservation_route_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    assert packet["blocked_claim_count"] == 12
    for key in [
        "C_exchange_candidate_packet_selected_after_review",
        "C_exchange_candidate_packet_authorized_here",
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
        assert packet[key] is False, key
    for phrase in [
        "bounded total stress-energy conservation route packet only",
        "accepted gauge-sector and matter-sector exchange identities",
        "records cancellation",
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
        assert phrase in packet["non_claim_boundary"], phrase


def test_psi_a_u1_total_stress_energy_conservation_route_packet_validation_policy_is_bounded() -> None:
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


def test_psi_a_u1_total_stress_energy_conservation_route_packet_rotates_to_result_review() -> None:
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
    assert consumed["total_conservation_route_packet_result"] == OUTCOME_ID
    assert consumed["total_stress_energy_conservation_route_packet_result"] == (
        OUTCOME_ID
    )
    assert consumed["total_conservation_route_constructed"] == "yes"
    assert consumed["total_conservation_proved"] == "yes"
    assert consumed["total_stress_energy_conservation_proved"] == "yes"
    assert consumed["C_exchange_closeout"] == "no"
    assert consumed["C_exchange_functional_embedding_claimed"] == "no"
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
    assert active_row["total_conservation_route_packet_result"] == OUTCOME_ID
    assert active_row["total_stress_energy_conservation_route_packet_result"] == (
        OUTCOME_ID
    )
    assert active_row["total_conservation_route_packet_result_review_result"] == (
        "PENDING"
    )
    assert active_row["total_conservation_route_packet_result_review_authorized"] == (
        "yes"
    )
    assert active_row["total_conservation_route_packet_result_review_completed"] == (
        "no"
    )
    assert active_row["total_conservation_proved"] == "yes"
    assert active_row["total_stress_energy_conservation_proved"] == "yes"
    assert active_row["C_exchange_closeout"] == "no"
    assert active_row["C_exchange_functional_embedding_claimed"] == "no"


def test_psi_a_u1_total_stress_energy_conservation_route_packet_mirrors() -> None:
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
        "ToeNativePsiAU1TotalStressEnergyConservationRoutePacket",
        NEXT_TARGET,
        f"CURRENT_LIVE_NEXT_TARGET_v0: {NEXT_TARGET}",
        f"PREVIOUS_LIVE_NEXT_TARGET_v0: {CONSUMED_TARGET}",
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        TOTAL_DIVERGENCE_SUM_IDENTITY,
        EXCHANGE_TERM_CANCELLATION,
        TOTAL_CONSERVATION_IDENTITY,
        TOTAL_STRESS_ENERGY_OBJECT,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
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


def test_psi_a_u1_total_stress_energy_conservation_route_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_total_stress_energy_conservation_route_packet_gate.py"
    )
