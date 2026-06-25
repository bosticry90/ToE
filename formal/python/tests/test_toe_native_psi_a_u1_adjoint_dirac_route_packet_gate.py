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
from formal.python.tools.toe_native_psi_a_u1_adjoint_dirac_route_packet_report import (
    ADJOINT_DERIVATIVE_POLICY,
    ADJOINT_EQUATION_ROUTE,
    ADJOINT_EQUATION_ROUTE_STATUS,
    ADJOINT_VARIATION_ROUTE,
    BLOCKED_CLAIMS,
    CONSUMED_TARGET,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE_POLICY,
    CURRENT_CONSERVATION_FROM_PAIR_PREVIEW,
    CURRENT_CONSERVATION_ROUTE_PREVIEW,
    DEFAULT_OUT,
    EXCHANGE_ROUTE_PREVIEW,
    INDEXED_FUTURE_ROUTES,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LEFT_ACTING_ADJOINT_NOTATION,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PRIMARY_VARIATION_VARIABLE,
    PSI_EQUATION_ROUTE,
    PSI_VARIATION_DIRAC_ROUTE_OUTCOME,
    PSI_VARIATION_DIRAC_ROUTE_PATH,
    PSIBAR_VARIATION_ROUTE,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SOURCED_MAXWELL_COMPATIBILITY_ROUTE_PREVIEW,
    TARGET_CONSERVATION_LAW,
    build_toe_native_psi_a_u1_adjoint_dirac_route_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_adjoint_dirac_route_packet_report.py"
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


def test_psi_a_u1_adjoint_dirac_route_packet_files_exist() -> None:
    for path in [
        PSI_VARIATION_DIRAC_ROUTE_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_adjoint_dirac_route_packet_builds() -> None:
    psi_variation = _json(PSI_VARIATION_DIRAC_ROUTE_PATH)
    packet = _json(DEFAULT_OUT)
    assert psi_variation["outcome_id"] == PSI_VARIATION_DIRAC_ROUTE_OUTCOME
    assert psi_variation["selected_next_target"] == CONSUMED_TARGET

    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert (
        packet["consumed_psi_variation_dirac_route_packet_result"]
        == PSI_VARIATION_DIRAC_ROUTE_OUTCOME
    )
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_toe_native_psi_a_u1_adjoint_dirac_route_packet() == packet


def test_psi_a_u1_adjoint_dirac_route_packet_records_route_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["primary_variation_variable"] == PRIMARY_VARIATION_VARIABLE
    assert packet["psibar_variation_route"] == PSIBAR_VARIATION_ROUTE
    assert packet["psi_equation_route"] == PSI_EQUATION_ROUTE
    assert packet["covariant_derivative_policy"] == COVARIANT_DERIVATIVE_POLICY
    assert packet["current_candidate_policy"] == CURRENT_CANDIDATE_POLICY
    assert packet["target_conservation_law"] == TARGET_CONSERVATION_LAW
    assert packet["adjoint_derivative_policy"] == ADJOINT_DERIVATIVE_POLICY
    assert packet["adjoint_variation_route"] == ADJOINT_VARIATION_ROUTE
    assert packet["adjoint_equation_route"] == ADJOINT_EQUATION_ROUTE
    assert packet["left_acting_adjoint_notation"] == LEFT_ACTING_ADJOINT_NOTATION
    assert packet["adjoint_equation_route_status"] == ADJOINT_EQUATION_ROUTE_STATUS
    assert (
        packet["current_conservation_from_pair_preview"]
        == CURRENT_CONSERVATION_FROM_PAIR_PREVIEW
    )
    assert packet["current_conservation_route_preview"] == CURRENT_CONSERVATION_ROUTE_PREVIEW
    assert (
        packet["sourced_maxwell_compatibility_route_preview"]
        == SOURCED_MAXWELL_COMPATIBILITY_ROUTE_PREVIEW
    )
    assert packet["exchange_route_preview"] == EXCHANGE_ROUTE_PREVIEW
    assert packet["indexed_future_routes"] == INDEXED_FUTURE_ROUTES
    assert packet["indexed_future_route_count"] == 3
    for key in [
        "adjoint_dirac_route_packet_prepared",
        "psi_variation_adjoint_route_recorded",
        "adjoint_equation_route_recorded",
        "opposite_gauge_sign_adjoint_derivative_indexed",
        "left_acting_adjoint_notation_recorded",
        "psi_and_adjoint_pair_indexed",
        "current_conservation_from_dirac_pair_packet_selected",
        "current_conservation_from_dirac_pair_packet_preparation_authorized",
        "current_conservation_route_indexed",
        "sourced_maxwell_compatibility_route_indexed",
        "exchange_route_indexed",
    ]:
        assert packet[key] is True, key


def test_psi_a_u1_adjoint_dirac_route_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    assert packet["blocked_claim_count"] == 13
    for key in [
        "adjoint_dirac_equation_derived",
        "adjoint_dirac_derivation_claimed",
        "current_conservation_proved",
        "sourced_maxwell_closure_claimed",
        "sourced_maxwell_equation_derived",
        "stress_energy_derived",
        "psi_stress_energy_derived",
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
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "adjoint Dirac route packet only",
        "D_mu psibar = nabla_mu psibar - i q A_mu psibar",
        "delta_psi S_{psi A} -> i (D_mu psibar) gamma^mu + m psibar = 0",
        "bounded adjoint equation route",
        "no current conservation proof",
        "no sourced Maxwell closure",
        "no stress-energy derivation",
        "no exchange identity",
        "no total conservation proof",
        "no C_exchange closeout",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no quantized electromagnetism",
        "no anomaly analysis",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_psi_a_u1_adjoint_dirac_route_packet_rotates_to_conservation_pair() -> None:
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
    assert consumed["adjoint_dirac_route_packet_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["adjoint_derivative_policy"] == ADJOINT_DERIVATIVE_POLICY
    assert consumed["adjoint_variation_route"] == ADJOINT_VARIATION_ROUTE
    assert consumed["adjoint_equation_route"] == ADJOINT_EQUATION_ROUTE
    assert consumed["left_acting_adjoint_notation"] == LEFT_ACTING_ADJOINT_NOTATION
    assert consumed["opposite_gauge_sign_adjoint_derivative_indexed"] == "yes"
    assert consumed["left_acting_adjoint_notation_recorded"] == "yes"
    assert consumed["current_conservation_proved"] == "no"
    assert consumed["adjoint_dirac_equation_derived"] == "no"
    assert consumed["sourced_maxwell_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    if is_current:
        active_row = active[0]
        assert active_row["workstream_id"] == NEXT_TARGET
        assert active_row["authorized_next_strict_target"] == NEXT_TARGET
        assert active_row["consumed_target"] == CONSUMED_TARGET
        assert active_row["consumed_adjoint_dirac_route_packet_result"] == OUTCOME_ID
        assert active_row["packet_result"] == "PENDING"
        assert active_row["current_conservation_from_dirac_pair_packet_result"] == (
            "PENDING"
        )
        assert (
            active_row[
                "current_conservation_from_dirac_pair_packet_preparation_authorized"
            ]
            == "yes"
        )
        assert active_row["current_conservation_from_dirac_pair_packet_prepared"] == "no"
        assert active_row["adjoint_derivative_policy"] == ADJOINT_DERIVATIVE_POLICY
        assert active_row["adjoint_variation_route"] == ADJOINT_VARIATION_ROUTE
        assert active_row["adjoint_equation_route"] == ADJOINT_EQUATION_ROUTE
        assert active_row["left_acting_adjoint_notation"] == LEFT_ACTING_ADJOINT_NOTATION
        assert active_row["current_conservation_route_preview"] == (
            CURRENT_CONSERVATION_ROUTE_PREVIEW
        )
        assert active_row["proof_pair_status"].endswith("conservation proof remains blocked")
        for key in [
            "adjoint_dirac_route_packet_prepared",
            "psi_variation_adjoint_route_recorded",
            "adjoint_equation_route_recorded",
            "opposite_gauge_sign_adjoint_derivative_indexed",
            "left_acting_adjoint_notation_recorded",
            "psi_and_adjoint_pair_indexed",
            "current_conservation_from_dirac_pair_packet_selected",
            "current_conservation_from_dirac_pair_packet_preparation_authorized",
            "current_conservation_route_indexed",
            "sourced_maxwell_compatibility_route_indexed",
            "exchange_route_indexed",
        ]:
            assert active_row[key] == "yes", key
        for key in [
            "current_conservation_proved",
            "adjoint_dirac_equation_derived",
            "adjoint_dirac_derivation_claimed",
            "sourced_maxwell_closure_claimed",
            "sourced_maxwell_equation_derived",
            "stress_energy_derived",
            "exchange_identity_proved",
            "total_conservation_proved",
            "C_exchange_definition_closeout",
            "em_qft_closure_claimed",
            "qft_gr_closure_claimed",
            "quantized_electromagnetism_claimed",
            "anomaly_analysis_performed",
            "phase2_authorized",
            "empirical_validation_claimed",
            "master_action_promoted",
        ]:
            assert active_row[key] == "no", key


def test_psi_a_u1_adjoint_dirac_route_packet_lean_and_surface_mirrors() -> None:
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
        "ToeNativePsiAU1AdjointDiracRoutePacket",
        NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_psi_A_u1_current_conservation_from_dirac_pair_packet",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_psi_A_u1_adjoint_dirac_route_packet",
        ADJOINT_DERIVATIVE_POLICY,
        ADJOINT_VARIATION_ROUTE,
        ADJOINT_EQUATION_ROUTE,
        LEFT_ACTING_ADJOINT_NOTATION,
        CURRENT_CONSERVATION_ROUTE_PREVIEW,
        SOURCED_MAXWELL_COMPATIBILITY_ROUTE_PREVIEW,
        EXCHANGE_ROUTE_PREVIEW,
        "no current conservation proof",
        "no sourced Maxwell closure",
        "no stress-energy derivation",
        "no exchange identity",
        "no total conservation proof",
        "no C_exchange closeout",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_psi_a_u1_adjoint_dirac_route_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_adjoint_dirac_route_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_adjoint_dirac_route_packet_gate.py"
    )
