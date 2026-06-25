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
from formal.python.tools.toe_native_psi_a_u1_interaction_action_block_definition_packet_report import (
    ACTION_BLOCK_DEFINITION_PACKET_RESULT,
    ACTION_BLOCK_DENSITY,
    ACTION_BLOCK_GAUGE_TERM,
    ACTION_BLOCK_ID,
    ACTION_BLOCK_MATTER_TERM,
    ACTION_BLOCK_STATEMENT,
    BLOCKED_CLAIMS,
    CONSUMED_TARGET,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE_PREVIEW,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FIELD_STRENGTH_POLICY,
    GAUGE_COVARIANT_DERIVATIVE_TRANSFORM,
    GAUGE_TRANSFORMATION_POLICY,
    INTERACTION_TERM_SHAPE,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MINIMAL_COUPLING_EXPANSION,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    build_toe_native_psi_a_u1_interaction_action_block_definition_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_interaction_action_block_definition_packet_report.py"
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


def test_psi_a_u1_action_block_definition_packet_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_action_block_definition_packet_records_bounded_action() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["action_block_definition_packet_result"] == ACTION_BLOCK_DEFINITION_PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_toe_native_psi_a_u1_interaction_action_block_definition_packet() == packet

    assert packet["selected_interaction_route"] == SELECTED_INTERACTION_ROUTE
    assert packet["action_block_id"] == ACTION_BLOCK_ID
    assert packet["action_block_statement"] == ACTION_BLOCK_STATEMENT
    assert packet["action_block_density"] == ACTION_BLOCK_DENSITY
    assert packet["action_block_matter_term"] == ACTION_BLOCK_MATTER_TERM
    assert packet["action_block_gauge_term"] == ACTION_BLOCK_GAUGE_TERM
    assert packet["covariant_derivative_policy"] == COVARIANT_DERIVATIVE_POLICY
    assert packet["field_strength_policy"] == FIELD_STRENGTH_POLICY
    assert packet["gauge_transformation_policy"] == GAUGE_TRANSFORMATION_POLICY
    assert packet["gauge_covariant_derivative_transform"] == GAUGE_COVARIANT_DERIVATIVE_TRANSFORM
    assert packet["minimal_coupling_expansion"] == MINIMAL_COUPLING_EXPANSION
    assert packet["interaction_term_shape"] == INTERACTION_TERM_SHAPE
    assert packet["current_candidate_preview"] == CURRENT_CANDIDATE_PREVIEW


def test_psi_a_u1_action_block_definition_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    assert packet["blocked_claim_count"] == 15
    for key in [
        "A_variation_result_derived",
        "A_variation_current_derived",
        "psi_variation_result_derived",
        "psi_field_equation_derived",
        "J_nu_derived",
        "matter_current_J_nu_derived",
        "current_derived",
        "current_conservation_proved",
        "sourced_maxwell_equation_derived",
        "dirac_equation_derived",
        "psi_stress_energy_derived",
        "A_psi_exchange_identity_proved",
        "gauge_matter_exchange_proved",
        "matter_gauge_exchange_proved",
        "total_stress_energy_conservation_proved",
        "C_exchange_definition_closeout",
        "C_exchange_closeout",
        "c_exchange_functional_defined",
        "c_exchange_rule_proved",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "action-block definition packet only",
        "no A-variation result",
        "no psi variation result",
        "no J^nu derivation",
        "no current conservation proof",
        "no sourced Maxwell derivation",
        "no Dirac derivation",
        "no psi stress-energy derivation",
        "no A/psi exchange identity",
        "no total stress-energy conservation proof",
        "no C_exchange definition closeout",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_psi_a_u1_action_block_definition_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_action_block_definition_packet_rotates_live_target_to_review() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    registry = _json(REGISTRY_PATH)
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
    assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=str(LEAN_PACKET_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        lane=NEXT_TARGET,
    )
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["action_block_definition_packet_result"] == OUTCOME_ID
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["action_block_definition_packet_prepared"] == "yes"
    assert consumed["interaction_action_block_defined"] == "yes"
    assert consumed["minimal_u1_dirac_gauge_action_block_recorded"] == "yes"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["sourced_maxwell_equation_derived"] == "no"
    assert consumed["matter_gauge_exchange_proved"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    review_row = _workstream(registry, NEXT_TARGET)
    assert review_row["status"] in {"active", "paused"}
    assert review_row["authorized_next_strict_target"] == NEXT_TARGET
    assert review_row["consumed_target"] == CONSUMED_TARGET
    assert review_row["consumed_action_block_definition_packet_result"] == OUTCOME_ID
    assert review_row["selected_interaction_route"] == SELECTED_INTERACTION_ROUTE
    assert review_row["action_block_statement"] == ACTION_BLOCK_STATEMENT
    assert review_row["minimal_coupling_expansion"] == MINIMAL_COUPLING_EXPANSION
    assert review_row["interaction_term_shape"] == INTERACTION_TERM_SHAPE
    assert review_row["A_variation_result_derived"] == "no"
    assert review_row["psi_variation_result_derived"] == "no"
    assert review_row["J_nu_derived"] == "no"
    assert review_row["sourced_maxwell_equation_derived"] == "no"
    assert review_row["matter_gauge_exchange_proved"] == "no"
    assert review_row["qft_gr_closure_claimed"] == "no"
    assert review_row["master_action_promoted"] == "no"


def test_psi_a_u1_action_block_definition_packet_lean_and_surface_mirrors() -> None:
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
        ACTION_BLOCK_DEFINITION_PACKET_RESULT,
        PACKET_CLASSIFICATION,
        "ToeNativePsiAU1InteractionActionBlockDefinitionPacket",
        NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_psi_A_u1_current_derivation_from_A_variation_packet",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_psi_A_u1_interaction_action_block_definition_packet_result",
        ACTION_BLOCK_STATEMENT,
        COVARIANT_DERIVATIVE_POLICY,
        FIELD_STRENGTH_POLICY,
        GAUGE_TRANSFORMATION_POLICY,
        GAUGE_COVARIANT_DERIVATIVE_TRANSFORM,
        MINIMAL_COUPLING_EXPANSION,
        INTERACTION_TERM_SHAPE,
        "no A-variation result",
        "no psi variation result",
        "no J^nu derivation",
        "no sourced Maxwell derivation",
        "no A/psi exchange identity",
        "no C_exchange definition closeout",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_psi_a_u1_action_block_definition_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_interaction_action_block_definition_packet_gate.py"
    )
