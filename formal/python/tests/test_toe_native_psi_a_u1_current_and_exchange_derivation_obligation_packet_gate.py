from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
)
from formal.python.tools.toe_native_psi_a_u1_current_and_exchange_derivation_obligation_packet_report import (
    BLOCKED_CLAIMS,
    COVARIANT_DERIVATIVE_POLICY,
    C_EXCHANGE_EQUATION_PREVIEW,
    C_EXCHANGE_POLICY_PREVIEW,
    CURRENT_CANDIDATE_POLICY,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    GAUGE_EXCHANGE_PREVIEW,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_EXCHANGE_PREVIEW,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OBLIGATION_PACKET_RESULT,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    POLICY_PACKET_OUTCOME,
    POLICY_PACKET_PATH,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCED_GAUGE_EQUATION_PREVIEW,
    TOTAL_EXCHANGE_PREVIEW,
    build_toe_native_psi_a_u1_current_and_exchange_derivation_obligation_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_current_and_exchange_derivation_obligation_packet_report.py"
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
CONSUMED_TARGET = (
    "prepare_toe_native_psi_A_u1_current_and_exchange_derivation_obligation_packet"
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


def test_psi_a_u1_obligation_packet_files_exist() -> None:
    for path in [
        POLICY_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_obligation_packet_indexes_obligations_without_derivation() -> None:
    policy = _json(POLICY_PACKET_PATH)
    packet = _json(DEFAULT_OUT)
    assert policy["outcome_id"] == POLICY_PACKET_OUTCOME
    assert policy["selected_next_target"] == packet["consumed_target"]

    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["obligation_packet_result"] == OBLIGATION_PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_toe_native_psi_a_u1_current_and_exchange_derivation_obligation_packet() == packet


def test_psi_a_u1_obligation_packet_records_o1_to_o10() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["derivation_obligation_count"] == 10
    assert packet["obligation_ids"] == [
        "O1",
        "O2",
        "O3",
        "O4",
        "O5",
        "O6",
        "O7",
        "O8",
        "O9",
        "O10",
    ]
    assert all(
        row["status"] == "indexed_pending_future_packet"
        for row in packet["derivation_obligations"]
    )
    assert packet["covariant_derivative_policy"] == COVARIANT_DERIVATIVE_POLICY
    assert packet["gauge_transformation_policy"] == GAUGE_TRANSFORMATION_POLICY
    assert packet["current_candidate_policy"] == CURRENT_CANDIDATE_POLICY
    assert packet["sourced_gauge_equation_preview"] == SOURCED_GAUGE_EQUATION_PREVIEW
    assert packet["gauge_exchange_preview"] == GAUGE_EXCHANGE_PREVIEW
    assert packet["matter_exchange_preview"] == MATTER_EXCHANGE_PREVIEW
    assert packet["total_exchange_preview"] == TOTAL_EXCHANGE_PREVIEW
    assert packet["c_exchange_policy_preview"] == C_EXCHANGE_POLICY_PREVIEW
    assert packet["c_exchange_equation_preview"] == C_EXCHANGE_EQUATION_PREVIEW


def test_psi_a_u1_obligation_packet_preserves_blocked_claims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    assert packet["blocked_claim_count"] == 16
    for key in [
        "interaction_action_block_defined",
        "gauge_covariance_proved",
        "psi_field_equation_derived",
        "A_variation_current_derived",
        "current_derived",
        "J_nu_derived",
        "current_conservation_proved",
        "sourced_maxwell_equation_derived",
        "dirac_equation_derived",
        "psi_stress_energy_derived",
        "gauge_matter_exchange_proved",
        "matter_gauge_exchange_proved",
        "total_stress_energy_conservation_proved",
        "C_exchange_closeout",
        "c_exchange_rule_family_decided",
        "c_exchange_functional_defined",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "standard_model_derivation_claimed",
        "quantized_electromagnetism_claimed",
        "anomaly_analysis_performed",
        "empirical_validation_claimed",
        "phase2_authorized",
        "master_action_promoted",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "indexes proof obligations only",
        "does not derive J^nu",
        "does not prove current conservation",
        "does not derive sourced Maxwell",
        "does not derive the Dirac equation",
        "does not derive psi stress-energy",
        "does not prove gauge-matter exchange",
        "does not prove total stress-energy conservation",
        "does not close C_exchange",
        "does not close EM-QFT",
        "does not close QFT-GR",
        "does not authorize Phase 2",
        "does not promote the master action",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_psi_a_u1_obligation_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_obligation_packet_rotates_live_target_to_action_block_packet() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    registry = _json(REGISTRY_PATH)
    state = registry["current_target_state"]
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
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
    assert consumed["obligation_packet_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["derivation_obligation_count"] == "10"
    assert consumed["current_derivation_obligations_indexed"] == "yes"
    assert consumed["exchange_proof_obligations_indexed"] == "yes"
    assert consumed["C_exchange_closeout"] == "no"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["current_conservation_proved"] == "no"
    assert consumed["sourced_maxwell_equation_derived"] == "no"
    assert consumed["matter_gauge_exchange_proved"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["consumed_obligation_packet_result"] == OUTCOME_ID
    assert active_row["packet_result"] == "PENDING"
    assert active_row["action_block_definition_packet_result"] == "PENDING"
    assert active_row["selected_interaction_route"] == SELECTED_INTERACTION_ROUTE
    assert active_row["covariant_derivative_policy"] == COVARIANT_DERIVATIVE_POLICY
    assert active_row["action_block_definition_packet_preparation_authorized"] == "yes"
    assert active_row["action_block_definition_packet_prepared"] == "no"
    assert active_row["interaction_action_block_defined"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["matter_gauge_exchange_proved"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_psi_a_u1_obligation_packet_lean_and_surface_mirrors() -> None:
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
        OBLIGATION_PACKET_RESULT,
        PACKET_CLASSIFICATION,
        "ToeNativePsiAU1CurrentAndExchangeDerivationObligationPacket",
        NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_psi_A_u1_interaction_action_block_definition_packet",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_psi_A_u1_current_and_exchange_derivation_obligation_packet",
        COVARIANT_DERIVATIVE_POLICY,
        GAUGE_TRANSFORMATION_POLICY,
        CURRENT_CANDIDATE_POLICY,
        TOTAL_EXCHANGE_PREVIEW,
        C_EXCHANGE_POLICY_PREVIEW,
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not prove gauge-matter exchange",
        "does not close C_exchange",
        "does not close EM-QFT",
        "does not close QFT-GR",
        "does not promote the master action",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_psi_a_u1_obligation_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_current_and_exchange_derivation_obligation_packet_gate.py"
    )
