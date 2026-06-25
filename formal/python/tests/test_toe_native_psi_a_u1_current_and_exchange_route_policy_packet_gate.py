from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    assert_historical_target_recorded,
)
from formal.python.tools.master_action_interaction_selection_after_a_ck_triad_report import (
    DEFAULT_OUT as SELECTOR_PATH,
    OUTCOME_ID as SELECTOR_OUTCOME,
    SELECTED_INTERACTION_ROUTE,
)
from formal.python.tools.toe_native_psi_a_u1_current_and_exchange_route_policy_packet_report import (
    ADJOINT_POLICY,
    ALTERNATE_COVARIANT_DERIVATIVE_REJECTED,
    BACKGROUND_SCOPE_POLICY,
    BLOCKED_CLAIMS,
    BOUNDARY_VARIATION_POLICY,
    COVARIANT_DERIVATIVE_POLICY,
    C_EXCHANGE_EQUATION_PREVIEW,
    C_EXCHANGE_POLICY_PREVIEW,
    CURRENT_CANDIDATE_POLICY,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FIELD_DOMAIN_POLICY,
    FIELD_STRENGTH_POLICY,
    GAUGE_FIELD_POLICY,
    GAUGE_GROUP_POLICY,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SURFACE_POLICY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    POLICY_ITEMS,
    POLICY_PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SPIN_CONNECTION_POLICY,
    STRESS_ENERGY_POLICY,
    TETRAD_POLICY,
    TOTAL_EXCHANGE_PREVIEW,
    build_toe_native_psi_a_u1_current_and_exchange_route_policy_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_current_and_exchange_route_policy_packet_report.py"
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
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_psi_a_u1_policy_packet_files_exist() -> None:
    for path in [
        SELECTOR_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_policy_packet_selects_policy_and_blocks_derivation() -> None:
    selector = _json(SELECTOR_PATH)
    packet = _json(DEFAULT_OUT)
    assert selector["outcome_id"] == SELECTOR_OUTCOME
    assert selector["selected_next_target"] == packet["consumed_target"]
    assert selector["selected_interaction_route"] == SELECTED_INTERACTION_ROUTE

    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["policy_packet_result"] == POLICY_PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["interaction_policy_selected"] is True
    assert packet["psi_A_u1_policy_packet_prepared"] is True
    assert build_toe_native_psi_a_u1_current_and_exchange_route_policy_packet() == packet


def test_psi_a_u1_policy_packet_records_selected_contract() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["policy_item_count"] == 18
    assert packet["policy_selected_count"] == 14
    assert packet["policy_blocked_count"] == 1
    assert packet["policy_items_expected"] == POLICY_ITEMS
    assert [row["policy_id"] for row in packet["policy_items"]] == [
        "matter_surface",
        "gauge_group",
        "gauge_field",
        "field_strength",
        "charge_sign_convention",
        "covariant_derivative",
        "alternate_derivative_convention",
        "gamma_matrices",
        "tetrad_frame_policy",
        "spin_connection",
        "psibar_adjoint",
        "field_domains",
        "boundary_variation",
        "gauge_transformations",
        "current_candidate",
        "stress_energy_policy",
        "exchange_policy",
        "background_scope",
    ]
    assert packet["matter_surface_policy"] == MATTER_SURFACE_POLICY
    assert packet["gauge_group_policy"] == GAUGE_GROUP_POLICY
    assert packet["gauge_field_policy"] == GAUGE_FIELD_POLICY
    assert packet["field_strength_policy"] == FIELD_STRENGTH_POLICY
    assert packet["covariant_derivative_policy"] == COVARIANT_DERIVATIVE_POLICY
    assert packet["plus_sign_covariant_derivative_selected"] is True
    assert packet["minus_sign_covariant_derivative_selected"] is False
    assert packet["alternate_covariant_derivative_rejected"] == (
        ALTERNATE_COVARIANT_DERIVATIVE_REJECTED
    )
    assert packet["tetrad_policy"] == TETRAD_POLICY
    assert packet["spin_connection_policy"] == SPIN_CONNECTION_POLICY
    assert packet["adjoint_policy"] == ADJOINT_POLICY
    assert packet["field_domain_policy"] == FIELD_DOMAIN_POLICY
    assert packet["boundary_variation_policy"] == BOUNDARY_VARIATION_POLICY
    assert packet["gauge_transformation_policy"] == GAUGE_TRANSFORMATION_POLICY


def test_psi_a_u1_policy_packet_records_current_and_exchange_as_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["current_candidate_policy"] == CURRENT_CANDIDATE_POLICY
    assert packet["stress_energy_policy"] == STRESS_ENERGY_POLICY
    assert packet["background_scope_policy"] == BACKGROUND_SCOPE_POLICY
    assert packet["total_exchange_preview"] == TOTAL_EXCHANGE_PREVIEW
    assert packet["c_exchange_policy_preview"] == C_EXCHANGE_POLICY_PREVIEW
    assert packet["c_exchange_equation_preview"] == C_EXCHANGE_EQUATION_PREVIEW
    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    assert packet["blocked_claim_count"] == 15
    assert packet["review_criteria_count"] == 13
    assert packet["review_criteria_accepted_count"] == 13

    for key in [
        "current_route_derived",
        "matter_current_J_nu_derived",
        "J_nu_derived",
        "current_conservation_proved",
        "sourced_maxwell_equation_derived",
        "dirac_equation_derived",
        "matter_gauge_exchange_proved",
        "psi_stress_energy_derived",
        "total_stress_energy_conservation_proved",
        "c_exchange_functional_defined",
        "c_exchange_rule_proved",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "quantized_electromagnetism_claimed",
        "anomaly_cancellation_claimed",
        "standard_model_derivation_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
    ]:
        assert packet[key] is False, key

    for phrase in [
        "does not derive J^nu",
        "does not prove current conservation",
        "does not derive sourced Maxwell",
        "does not derive the Dirac equation",
        "does not prove matter-gauge exchange",
        "does not derive psi stress-energy",
        "does not prove total stress-energy conservation",
        "does not define or prove a completed C_exchange functional",
        "does not close EM-QFT",
        "does not close QFT-GR",
        "does not promote the master action",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_psi_a_u1_policy_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_policy_packet_rotates_live_target_to_obligation_packet() -> None:
    registry = _json(REGISTRY_PATH)
    transition_is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target="prepare_toe_native_psi_A_u1_current_and_exchange_route_policy_packet",
        live_target=NEXT_TARGET,
        evidence=(
            "formal/toe_formal/ToeFormal/Derivation/"
            "ToeNativePsiAU1CurrentAndExchangeRoutePolicyPacket.lean"
        ),
        lane=NEXT_TARGET,
    )
    state = registry["current_target_state"]
    if transition_is_current:
        assert state["previous_live_next_target"] == (
            "prepare_toe_native_psi_A_u1_current_and_exchange_route_policy_packet"
        )
        assert state["live_next_target"] == NEXT_TARGET
        assert state["active_lane"] == NEXT_TARGET
        assert state["live_next_target_evidence"] == (
            "formal/toe_formal/ToeFormal/Derivation/"
            "ToeNativePsiAU1CurrentAndExchangeRoutePolicyPacket.lean"
        )
        assert state["live_next_target_report"] == (
            "formal/docs/release/"
            "TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_ROUTE_POLICY_PACKET_20260624_v0.json"
        )
        assert state["live_next_target_outcome"] == OUTCOME_ID
        assert state["live_next_target_kind"] == NEXT_TARGET_KIND
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(
        registry, "prepare_toe_native_psi_A_u1_current_and_exchange_route_policy_packet"
    )
    assert consumed["status"] == "paused"
    assert consumed["policy_packet_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["policy_item_count"] == "18"
    assert consumed["plus_sign_covariant_derivative_selected"] == "yes"
    assert consumed["current_candidate_recorded"] == "yes"
    assert consumed["exchange_policy_selected"] == "yes"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["current_conservation_proved"] == "no"
    assert consumed["sourced_maxwell_equation_derived"] == "no"
    assert consumed["matter_gauge_exchange_proved"] == "no"
    assert consumed["em_qft_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    obligation_row = _workstream(registry, NEXT_TARGET)
    assert obligation_row["selected_interaction_route"] == SELECTED_INTERACTION_ROUTE
    assert obligation_row["covariant_derivative_policy"] == COVARIANT_DERIVATIVE_POLICY
    assert obligation_row["obligation_packet_prepared"] in {"yes", "no"}
    assert obligation_row["J_nu_derived"] == "no"
    assert obligation_row["sourced_maxwell_equation_derived"] == "no"
    assert obligation_row["matter_gauge_exchange_proved"] == "no"
    assert obligation_row["qft_gr_closure_claimed"] == "no"
    assert obligation_row["master_action_promoted"] == "no"


def test_psi_a_u1_policy_packet_lean_and_surface_mirrors() -> None:
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
        POLICY_PACKET_RESULT,
        PACKET_CLASSIFICATION,
        "ToeNativePsiAU1CurrentAndExchangeRoutePolicyPacket",
        NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_psi_A_u1_interaction_action_block_definition_packet_result",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_psi_A_u1_interaction_action_block_definition_packet",
        COVARIANT_DERIVATIVE_POLICY,
        GAUGE_TRANSFORMATION_POLICY,
        CURRENT_CANDIDATE_POLICY,
        TOTAL_EXCHANGE_PREVIEW,
        C_EXCHANGE_POLICY_PREVIEW,
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not prove matter-gauge exchange",
        "does not close EM-QFT",
        "does not close QFT-GR",
        "does not promote the master action",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_psi_a_u1_policy_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_current_and_exchange_route_policy_packet_gate.py"
    )
