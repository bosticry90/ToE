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
from formal.python.tools.toe_native_psi_a_u1_current_conservation_from_dirac_pair_packet_report import (
    ADJOINT_DIRAC_ROUTE_OUTCOME,
    ADJOINT_DIRAC_ROUTE_PATH,
    ADJOINT_DERIVATIVE_POLICY,
    ADJOINT_EQUATION_ROUTE,
    ASSUMPTIONS,
    BLOCKED_CLAIMS,
    CONSUMED_TARGET,
    COVARIANT_DERIVATIVE_PAIR_POLICY,
    CURRENT_CANDIDATE,
    CURRENT_CANDIDATE_POLICY_AFTER_CONSERVATION,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_CONSERVATION_ROUTE_STATUS,
    CURRENT_DIVERGENCE_ROUTE,
    DEFAULT_OUT,
    DIRAC_PAIR_ROUTE_INPUTS,
    EXCHANGE_ROUTE_PREVIEW,
    INDEXED_FUTURE_ROUTES,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MASS_TERM_CANCELLATION_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PSI_EQUATION_ROUTE,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ROUTE_STEPS,
    SCHEMA_ID,
    SOURCED_MAXWELL_ROUTE_PREVIEW,
    TARGET_CONSERVATION_LAW,
    build_toe_native_psi_a_u1_current_conservation_from_dirac_pair_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_current_conservation_from_dirac_pair_packet_report.py"
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


def test_psi_a_u1_current_conservation_from_dirac_pair_packet_files_exist() -> None:
    for path in [
        ADJOINT_DIRAC_ROUTE_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_current_conservation_from_dirac_pair_packet_builds() -> None:
    adjoint_packet = _json(ADJOINT_DIRAC_ROUTE_PATH)
    packet = _json(DEFAULT_OUT)
    assert adjoint_packet["outcome_id"] == ADJOINT_DIRAC_ROUTE_OUTCOME
    assert adjoint_packet["selected_next_target"] == CONSUMED_TARGET

    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["consumed_adjoint_dirac_route_packet_result"] == ADJOINT_DIRAC_ROUTE_OUTCOME
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_toe_native_psi_a_u1_current_conservation_from_dirac_pair_packet() == packet


def test_psi_a_u1_current_conservation_from_dirac_pair_packet_constructs_route() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["current_candidate"] == CURRENT_CANDIDATE
    assert packet["current_candidate_policy"] == CURRENT_CANDIDATE_POLICY_AFTER_CONSERVATION
    assert packet["target_conservation_law"] == TARGET_CONSERVATION_LAW
    assert packet["current_conservation_result"] == CURRENT_CONSERVATION_RESULT
    assert packet["current_divergence_route"] == CURRENT_DIVERGENCE_ROUTE
    assert packet["mass_term_cancellation_route"] == MASS_TERM_CANCELLATION_ROUTE
    assert packet["dirac_pair_route_inputs"] == DIRAC_PAIR_ROUTE_INPUTS
    assert packet["psi_equation_route"] == PSI_EQUATION_ROUTE
    assert packet["adjoint_equation_route"] == ADJOINT_EQUATION_ROUTE
    assert packet["adjoint_derivative_policy"] == ADJOINT_DERIVATIVE_POLICY
    assert packet["covariant_derivative_pair_policy"] == COVARIANT_DERIVATIVE_PAIR_POLICY
    assert packet["current_conservation_route_status"] == CURRENT_CONSERVATION_ROUTE_STATUS
    assert packet["route_steps"] == ROUTE_STEPS
    assert packet["route_step_count"] == 5
    assert packet["assumptions"] == ASSUMPTIONS
    assert packet["assumption_count"] == 4
    assert packet["sourced_maxwell_route_preview"] == SOURCED_MAXWELL_ROUTE_PREVIEW
    assert packet["exchange_route_preview"] == EXCHANGE_ROUTE_PREVIEW
    assert packet["indexed_future_routes"] == INDEXED_FUTURE_ROUTES
    assert packet["indexed_future_route_count"] == 2
    for key in [
        "current_conservation_from_dirac_pair_packet_prepared",
        "current_conservation_route_constructed",
        "bounded_current_conservation_route_constructed",
        "current_conservation_recorded",
        "current_conservation_proved",
        "bounded_current_conservation_proved",
        "target_conservation_law_recorded",
        "target_conservation_law_satisfied_under_dirac_pair",
        "dirac_pair_used",
        "psi_equation_route_used",
        "adjoint_equation_route_used",
        "mass_term_cancellation_recorded",
        "gamma_compatibility_assumptions_indexed",
        "domain_boundary_assumptions_indexed",
        "sourced_maxwell_consistency_candidate_ready",
        "sourced_maxwell_route_packet_selected",
        "sourced_maxwell_route_packet_preparation_authorized",
    ]:
        assert packet[key] is True, key


def test_psi_a_u1_current_conservation_from_dirac_pair_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    assert packet["blocked_claim_count"] == 14
    for key in [
        "sourced_maxwell_closure_claimed",
        "sourced_maxwell_equation_derived",
        "sourced_maxwell_route_derived",
        "full_maxwell_system_closure_claimed",
        "full_em_closure_claimed",
        "stress_energy_derived",
        "psi_stress_energy_derived",
        "gauge_matter_exchange_identity_proved",
        "exchange_identity_proved",
        "gauge_matter_exchange_proved",
        "matter_gauge_exchange_proved",
        "total_conservation_proved",
        "total_stress_energy_conservation_proved",
        "C_exchange_closeout",
        "C_exchange_definition_closeout",
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
        "bounded current-conservation-from-Dirac-pair packet only",
        "nabla_mu J^mu = 0",
        "J^mu = q psibar gamma^mu psi",
        "no sourced Maxwell closure",
        "no full Maxwell system closure",
        "no stress-energy derivation",
        "no gauge-matter exchange identity",
        "no total stress-energy conservation proof",
        "no C_exchange closeout",
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


def test_psi_a_u1_current_conservation_from_dirac_pair_packet_rotates_to_sourced_maxwell() -> None:
    registry = _json(REGISTRY_PATH)
    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=str(LEAN_PACKET_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
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
        assert state["live_next_target_evidence"] == str(
            LEAN_PACKET_PATH.relative_to(REPO_ROOT)
        ).replace("\\", "/")
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
    assert consumed["current_conservation_from_dirac_pair_packet_result"] == OUTCOME_ID
    assert consumed["current_conservation_proved"] == "yes"
    assert consumed["current_divergence_route"] == CURRENT_DIVERGENCE_ROUTE
    assert consumed["mass_term_cancellation_route"] == MASS_TERM_CANCELLATION_ROUTE
    assert consumed["current_conservation_result"] == CURRENT_CONSERVATION_RESULT
    assert consumed["sourced_maxwell_closure_claimed"] == "no"
    assert consumed["exchange_identity_proved"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    if is_current:
        active_row = active[0]
        assert active_row["workstream_id"] == NEXT_TARGET
        assert active_row["authorized_next_strict_target"] == NEXT_TARGET
        assert active_row["consumed_target"] == CONSUMED_TARGET
        assert (
            active_row["consumed_current_conservation_from_dirac_pair_packet_result"]
            == OUTCOME_ID
        )
        assert active_row["packet_result"] == "PENDING"
        assert active_row["sourced_maxwell_route_packet_result"] == "PENDING"
        assert active_row["sourced_maxwell_route_packet_preparation_authorized"] == "yes"
        assert active_row["sourced_maxwell_route_packet_prepared"] == "no"
        assert active_row["current_conservation_proved"] == "yes"
        assert active_row["current_conservation_result"] == CURRENT_CONSERVATION_RESULT
        assert active_row["sourced_maxwell_route_preview"] == SOURCED_MAXWELL_ROUTE_PREVIEW
        for key in [
            "current_conservation_from_dirac_pair_packet_prepared",
            "current_conservation_route_constructed",
            "bounded_current_conservation_route_constructed",
            "current_conservation_recorded",
            "bounded_current_conservation_proved",
            "dirac_pair_used",
            "mass_term_cancellation_recorded",
            "sourced_maxwell_consistency_candidate_ready",
            "sourced_maxwell_route_packet_selected",
            "sourced_maxwell_route_packet_preparation_authorized",
        ]:
            assert active_row[key] == "yes", key
        for key in [
            "sourced_maxwell_closure_claimed",
            "sourced_maxwell_equation_derived",
            "sourced_maxwell_route_derived",
            "full_maxwell_system_closure_claimed",
            "stress_energy_derived",
            "exchange_identity_proved",
            "total_stress_energy_conservation_proved",
            "C_exchange_definition_closeout",
            "em_qft_closure_claimed",
            "qft_gr_closure_claimed",
            "quantized_electromagnetism_claimed",
            "anomaly_analysis_performed",
            "standard_model_derivation_claimed",
            "phase2_authorized",
            "empirical_validation_claimed",
            "master_action_promoted",
        ]:
            assert active_row[key] == "no", key


def test_psi_a_u1_current_conservation_from_dirac_pair_packet_lean_and_surface_mirrors() -> None:
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
        "ToeNativePsiAU1CurrentConservationFromDiracPairPacket",
        NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_toe_native_psi_A_u1_sourced_maxwell_route_packet",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: prepare_toe_native_psi_A_u1_current_conservation_from_dirac_pair_packet",
        CURRENT_CANDIDATE,
        CURRENT_DIVERGENCE_ROUTE,
        MASS_TERM_CANCELLATION_ROUTE,
        CURRENT_CONSERVATION_RESULT,
        SOURCED_MAXWELL_ROUTE_PREVIEW,
        "no sourced Maxwell closure",
        "no full Maxwell system closure",
        "no stress-energy derivation",
        "no gauge-matter exchange identity",
        "no total stress-energy conservation proof",
        "no C_exchange closeout",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_psi_a_u1_current_conservation_from_dirac_pair_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_current_conservation_from_dirac_pair_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_current_conservation_from_dirac_pair_packet_gate.py"
    )
