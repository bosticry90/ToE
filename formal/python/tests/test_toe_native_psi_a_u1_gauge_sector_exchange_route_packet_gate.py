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
from formal.python.tools.toe_native_psi_a_u1_gauge_sector_exchange_route_packet_report import (
    ASSUMPTIONS,
    BLOCKED_CLAIMS,
    C_EXCHANGE_CANDIDATE,
    C_EXCHANGE_EQUATION,
    CONSUMED_TARGET,
    CURRENT_CONSERVATION_RESULT,
    DEFAULT_OUT,
    FIELD_STRENGTH_POLICY,
    GAUGE_DIVERGENCE_INTERMEDIATE,
    GAUGE_DIVERGENCE_SOURCE_SUBSTITUTION,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAUGE_SECTOR_EXCHANGE_INTERPRETATION,
    GAUGE_SECTOR_EXCHANGE_TARGET,
    GAUGE_SECTOR_EXCHANGE_TERM,
    GAUGE_STRESS_ENERGY_LOWER_INDEX_POLICY,
    GAUGE_STRESS_ENERGY_OBJECT,
    GAUGE_STRESS_ENERGY_POLICY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_TARGET,
    MATTER_STRESS_ENERGY_OBJECT,
    MATTER_STRESS_ENERGY_POLICY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    STRESS_ENERGY_POLICY_RESULT_REVIEW_OUTCOME,
    STRESS_ENERGY_POLICY_RESULT_REVIEW_PATH,
    TOTAL_CONSERVATION_EXPANDED_TARGET,
    TOTAL_CONSERVATION_TARGET,
    TOTAL_STRESS_ENERGY_OBJECT,
    TOTAL_STRESS_ENERGY_POLICY,
    build_toe_native_psi_a_u1_gauge_sector_exchange_route_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_gauge_sector_exchange_route_packet_report.py"
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


def test_psi_a_u1_gauge_sector_exchange_route_packet_files_exist() -> None:
    for path in [
        STRESS_ENERGY_POLICY_RESULT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_gauge_sector_exchange_route_packet_builds() -> None:
    consumed = _json(STRESS_ENERGY_POLICY_RESULT_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert consumed["outcome_id"] == STRESS_ENERGY_POLICY_RESULT_REVIEW_OUTCOME
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
    assert build_toe_native_psi_a_u1_gauge_sector_exchange_route_packet() == packet


def test_psi_a_u1_gauge_sector_exchange_route_packet_constructs_gauge_identity() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["field_strength_policy"] == FIELD_STRENGTH_POLICY
    assert packet["source_current"] == SOURCE_CURRENT
    assert packet["current_conservation_result"] == CURRENT_CONSERVATION_RESULT
    assert packet["sourced_gauge_route"] == SOURCED_GAUGE_ROUTE
    assert packet["gauge_stress_energy_object"] == GAUGE_STRESS_ENERGY_OBJECT
    assert packet["gauge_stress_energy_policy"] == GAUGE_STRESS_ENERGY_POLICY
    assert packet["gauge_stress_energy_lower_index_policy"] == (
        GAUGE_STRESS_ENERGY_LOWER_INDEX_POLICY
    )
    assert packet["matter_stress_energy_object"] == MATTER_STRESS_ENERGY_OBJECT
    assert packet["matter_stress_energy_policy"] == MATTER_STRESS_ENERGY_POLICY
    assert packet["total_stress_energy_object"] == TOTAL_STRESS_ENERGY_OBJECT
    assert packet["total_stress_energy_policy"] == TOTAL_STRESS_ENERGY_POLICY
    assert packet["gauge_sector_exchange_target"] == GAUGE_SECTOR_EXCHANGE_TARGET
    assert packet["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert packet["gauge_sector_exchange_term"] == GAUGE_SECTOR_EXCHANGE_TERM
    assert packet["gauge_divergence_intermediate"] == GAUGE_DIVERGENCE_INTERMEDIATE
    assert packet["gauge_divergence_source_substitution"] == (
        GAUGE_DIVERGENCE_SOURCE_SUBSTITUTION
    )
    assert packet["matter_sector_exchange_target"] == MATTER_SECTOR_EXCHANGE_TARGET
    assert packet["total_conservation_target"] == TOTAL_CONSERVATION_TARGET
    assert packet["total_conservation_expanded_target"] == TOTAL_CONSERVATION_EXPANDED_TARGET
    assert packet["C_exchange_candidate"] == C_EXCHANGE_CANDIDATE
    assert packet["C_exchange_equation"] == C_EXCHANGE_EQUATION
    assert packet["assumptions"] == ASSUMPTIONS
    assert packet["route_step_count"] == 6
    assert packet["route_steps"][-1]["statement"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert packet["plain_meaning"] == GAUGE_SECTOR_EXCHANGE_INTERPRETATION
    for key in [
        "gauge_sector_exchange_route_packet_prepared",
        "gauge_sector_exchange_route_constructed",
        "gauge_sector_exchange_route_recorded",
        "gauge_sector_exchange_identity_recorded",
        "gauge_sector_exchange_identity_constructed",
        "gauge_stress_energy_divergence_route_recorded",
        "gauge_sector_exchange_proved",
        "gauge_sector_exchange_proved_here",
        "gauge_side_exchange_only",
        "gauge_field_energy_momentum_not_separately_conserved_when_J_present",
        "gauge_sector_exchange_route_packet_result_review_selected",
        "gauge_sector_exchange_route_packet_result_review_authorized",
    ]:
        assert packet[key] is True, key


def test_psi_a_u1_gauge_sector_exchange_route_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    assert packet["blocked_claim_count"] == 12
    for key in [
        "matter_sector_exchange_packet_selected",
        "matter_sector_exchange_packet_authorized_here",
        "total_conservation_packet_selected",
        "total_conservation_packet_authorized_here",
        "stress_energy_derived_here",
        "stress_energy_metric_variation_derived",
        "stress_energy_tetrad_variation_derived",
        "psi_stress_energy_derived",
        "matter_stress_energy_derived",
        "matter_sector_exchange_proved",
        "matter_sector_exchange_route_constructed",
        "matter_sector_exchange_identity_recorded",
        "gauge_matter_exchange_identity_proved",
        "exchange_identity_proved",
        "gauge_matter_exchange_proved",
        "matter_gauge_exchange_proved",
        "total_conservation_proved",
        "total_stress_energy_conservation_proved",
        "C_exchange_closeout",
        "C_exchange_definition_closeout",
        "C_exchange_rule_family_closed",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "quantized_electromagnetism_claimed",
        "anomaly_analysis_performed",
        "standard_model_derivation_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "gauge-sector exchange route packet only",
        "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha",
        "no matter-sector exchange proof",
        "no total conservation proof",
        "no C_exchange closeout",
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


def test_psi_a_u1_gauge_sector_exchange_route_packet_rotates_to_result_review() -> None:
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

    state = registry["current_target_state"]
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
    if is_current:
        assert state["previous_live_next_target"] == CONSUMED_TARGET
        assert state["live_next_target"] == NEXT_TARGET
        assert state["active_lane"] == NEXT_TARGET
        assert state["live_next_target_evidence"] == evidence
        assert state["live_next_target_report"] == str(
            DEFAULT_OUT.relative_to(REPO_ROOT)
        ).replace("\\", "/")
        assert state["live_next_target_outcome"] == OUTCOME_ID
        assert state["live_next_target_kind"] == NEXT_TARGET_KIND
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["gauge_sector_exchange_route_packet_result"] == OUTCOME_ID
    assert consumed["gauge_sector_exchange_route_constructed"] == "yes"
    assert consumed["gauge_sector_exchange_identity_recorded"] == "yes"
    assert consumed["gauge_sector_exchange_proved"] == "yes"
    assert consumed["matter_sector_exchange_proved"] == "no"
    assert consumed["total_stress_energy_conservation_proved"] == "no"
    assert consumed["C_exchange_definition_closeout"] == "no"
    assert consumed["master_action_promoted"] == "no"

    if is_current:
        active_row = active[0]
        assert active_row["workstream_id"] == NEXT_TARGET
        assert active_row["authorized_next_strict_target"] == NEXT_TARGET
        assert active_row["consumed_target"] == CONSUMED_TARGET
        assert active_row["consumed_gauge_sector_exchange_route_packet_result"] == (
            OUTCOME_ID
        )
        assert active_row["packet_result"] == "PENDING"
        assert active_row["gauge_sector_exchange_route_packet_result"] == OUTCOME_ID
        assert active_row["gauge_sector_exchange_route_packet_result_review_result"] == (
            "PENDING"
        )
        assert active_row["gauge_sector_exchange_route_packet_result_review_authorized"] == (
            "yes"
        )
        assert active_row["gauge_sector_exchange_route_packet_result_review_completed"] == (
            "no"
        )
        assert active_row["gauge_sector_exchange_route_constructed"] == "yes"
        assert active_row["gauge_sector_exchange_identity_recorded"] == "yes"
        assert active_row["gauge_sector_exchange_proved"] == "yes"
        assert active_row["matter_sector_exchange_proved"] == "no"
        assert active_row["total_stress_energy_conservation_proved"] == "no"
        assert active_row["C_exchange_definition_closeout"] == "no"
        assert active_row["master_action_promoted"] == "no"


def test_psi_a_u1_gauge_sector_exchange_route_packet_mirrors() -> None:
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
        "ToeNativePsiAU1GaugeSectorExchangeRoutePacket",
        NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: review_toe_native_psi_A_u1_gauge_sector_exchange_route_packet_result",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: prepare_toe_native_psi_A_u1_gauge_sector_exchange_route_packet",
        GAUGE_STRESS_ENERGY_POLICY,
        SOURCED_GAUGE_ROUTE,
        SOURCE_CURRENT,
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_TARGET,
        TOTAL_CONSERVATION_EXPANDED_TARGET,
        "no matter-sector exchange proof",
        "no total conservation proof",
        "no C_exchange closeout",
        "no full Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_psi_a_u1_gauge_sector_exchange_route_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_gauge_sector_exchange_route_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_gauge_sector_exchange_route_packet_gate.py"
    )
