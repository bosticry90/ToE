from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_bridge_admissibility_ck_constraint_candidate_packet_report import (
    A_BRIDGE_CANDIDATE_ID,
    A_BRIDGE_CANDIDATE_TYPE,
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    A_BRIDGE_FIELD_EQUATION_MATCH,
    A_BRIDGE_RULE_PLAIN_MEANING,
    A_BRIDGE_SOURCE_RESIDUAL_MATCH,
    A_BRIDGE_STRESS_ENERGY_MATCH,
    A_CK_FAMILY_SELECTOR_OUTCOME,
    A_CK_FAMILY_SELECTOR_PATH,
    ARTIFACT_ID,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FULL_TOEFORMAL_STATUS,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    build_toe_native_a_bridge_admissibility_ck_constraint_candidate_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_bridge_admissibility_ck_constraint_candidate_packet_report.py"
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
        if row.get("workstream_id") == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_a_bridge_ck_candidate_packet_files_exist() -> None:
    for path in [
        A_CK_FAMILY_SELECTOR_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_bridge_ck_candidate_packet_accepts_selector() -> None:
    selector = _json(A_CK_FAMILY_SELECTOR_PATH)
    packet = _json(DEFAULT_OUT)
    assert selector["outcome_id"] == A_CK_FAMILY_SELECTOR_OUTCOME
    assert selector["selected_next_target"] == CONSUMED_TARGET
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
    assert (
        build_toe_native_a_bridge_admissibility_ck_constraint_candidate_packet()
        == packet
    )


def test_a_bridge_ck_candidate_packet_records_tuple() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_A_ck_option_class"] == SELECTED_A_CK_OPTION_CLASS
    assert packet["selected_A_ck_constraint_family"] == SELECTED_A_CK_CONSTRAINT_FAMILY
    assert packet["A_bridge_candidate_id"] == A_BRIDGE_CANDIDATE_ID
    assert packet["A_bridge_candidate_type"] == A_BRIDGE_CANDIDATE_TYPE
    assert packet["A_bridge_constraint_form"] == A_BRIDGE_CONSTRAINT_FORM
    assert packet["A_bridge_constraint_equation"] == A_BRIDGE_CONSTRAINT_EQUATION
    assert packet["A_bridge_field_equation_match"] == A_BRIDGE_FIELD_EQUATION_MATCH
    assert packet["A_bridge_stress_energy_match"] == A_BRIDGE_STRESS_ENERGY_MATCH
    assert packet["A_bridge_source_residual_match"] == A_BRIDGE_SOURCE_RESIDUAL_MATCH
    assert packet["A_bridge_rule_plain_meaning"] == A_BRIDGE_RULE_PLAIN_MEANING
    assert packet["bridge_component_count"] == 3
    assert packet["route_alignment_contract_count"] == 7
    assert packet["candidate_criteria_count"] == 9
    assert packet["candidate_criteria_accepted_count"] == 9


def test_a_bridge_ck_candidate_packet_preserves_source_and_vacuum_context() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert packet["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert (
        packet["source_candidate_constraint_equation"]
        == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert (
        packet["source_admissibility_constraint_form"]
        == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert packet["gauge_group_policy"] == "U(1) / Abelian test route"
    assert packet["vacuum_euler_lagrange_route"] == "nabla_mu F^{mu nu} = 0"
    assert packet["on_shell_vacuum_conservation_identity"] == (
        "nabla_mu T_A^{mu nu} = 0"
    )
    assert packet["source_route_still_blocked"] == "nabla_mu F^{mu nu} = J^nu"
    assert packet["source_admissibility_rule_retained_as_context"] is True
    assert packet["source_admissibility_family_completed"] is False
    assert packet["source_admissibility_claimed"] is False


def test_a_bridge_ck_candidate_packet_records_components_unproved() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "A_bridge_admissibility_ck_constraint_candidate_packet_prepared",
        "A_bridge_candidate_packet_prepared",
        "A_bridge_candidate_packet_accepted",
        "A_bridge_candidate_recorded",
        "A_bridge_route_consistency_rule_recorded",
        "A_bridge_candidate_selected_as_route_consistency_rule",
        "A_bridge_candidate_recorded_as_admissibility_rule",
        "A_bridge_candidate_recorded_as_admissibility_candidate",
        "A_bridge_admissibility_family_selected",
        "A_bridge_route_alignment_sequence_recorded",
        "route_consistency_tuple_recorded",
        "field_equation_match_recorded",
        "stress_energy_match_recorded",
        "source_residual_match_recorded",
    ]:
        assert packet[key] is True, key
    for key in [
        "A_bridge_candidate_recorded_as_action_term",
        "A_bridge_candidate_recorded_as_new_dynamical_law",
        "A_bridge_candidate_rule_proved",
        "A_bridge_admissibility_claimed",
        "A_bridge_admissibility_proved",
        "A_bridge_route_alignment_verified",
        "route_consistency_tuple_proved",
        "field_equation_match_proved",
        "stress_energy_match_proved",
        "source_residual_match_proved",
        "bridge_admissibility_proof_claimed",
    ]:
        assert packet[key] is False, key


def test_a_bridge_ck_candidate_packet_blocks_shortcuts() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "ck_action_embedding_constructed",
        "C_k_action_embedding_constructed",
        "ck_variation_executed",
        "C_k_variation_executed",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "A_variation_of_candidate_executed",
        "new_conservation_proof_claimed",
        "new_source_admissibility_proof_claimed",
        "source_admissibility_completed",
        "A_source_admissibility_proved",
        "current_route_derived",
        "current_source_route_constructed",
        "J_nu_derived",
        "psi_current_route_constructed",
        "external_current_native_derivation_selected",
        "matter_current_exchange_route_proved",
        "matter_gauge_energy_exchange_proved",
        "sourced_maxwell_equation_derived",
        "sourced_maxwell_closure_claimed",
        "full_em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
        "canonical_master_action_promoted",
        "phase2_readiness_claim",
        "pillar_completion_inferred",
        "seam_closure_claim",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "vacuum U(1) route-consistency admissibility candidate only",
        "does not prove bridge admissibility",
        "does not verify route alignment",
        "does not embed C_bridge^A into the action",
        "does not execute C_k variation",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "does not promote the master action",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_a_bridge_ck_candidate_packet_validation_policy_not_run() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == FULL_TOEFORMAL_STATUS
    assert policy["full_toeformal_aggregate_status_for_packet"] == FULL_TOEFORMAL_STATUS
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_bridge_ck_candidate_packet_rotates_to_review() -> None:
    registry = _json(REGISTRY_PATH)
    skip_if_not_current_target(registry, NEXT_TARGET)
    state = registry["current_target_state"]
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == NEXT_TARGET
    assert state["active_lane"] == NEXT_TARGET
    assert state["live_next_target_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "ToeNativeABridgeAdmissibilityCKConstraintCandidatePacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_"
        "20260622_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["A_bridge_candidate_id"] == A_BRIDGE_CANDIDATE_ID
    assert consumed["A_bridge_constraint_equation"] == A_BRIDGE_CONSTRAINT_EQUATION
    assert consumed["A_bridge_candidate_recorded_as_admissibility_rule"] == "yes"
    assert consumed["A_bridge_candidate_rule_proved"] == "no"
    assert consumed["C_k_variation_executed"] == "no"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["sourced_maxwell_closure_claimed"] == "no"
    assert consumed["full_em_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["packet_result"] == PACKET_RESULT
    assert active_row["review_prepared"] == "no"
    assert active_row["review_executed"] == "no"
    assert active_row["A_bridge_candidate_id"] == A_BRIDGE_CANDIDATE_ID
    assert active_row["A_bridge_constraint_form"] == A_BRIDGE_CONSTRAINT_FORM
    assert active_row["A_bridge_candidate_rule_proved"] == "no"
    assert active_row["A_bridge_route_alignment_verified"] == "no"
    assert active_row["C_k_variation_executed"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_closure_claimed"] == "no"
    assert active_row["full_em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_bridge_ck_candidate_packet_mirrors() -> None:
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
        CONSUMED_TARGET,
        NEXT_TARGET,
        "ToeNativeABridgeAdmissibilityCKConstraintCandidatePacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_A_bridge_admissibility_ck_constraint_candidate_packet_result",
        A_BRIDGE_CANDIDATE_ID,
        A_BRIDGE_CONSTRAINT_FORM,
        A_BRIDGE_CONSTRAINT_EQUATION,
        A_BRIDGE_FIELD_EQUATION_MATCH,
        A_BRIDGE_STRESS_ENERGY_MATCH,
        A_BRIDGE_SOURCE_RESIDUAL_MATCH,
        "vacuum U(1) route-consistency admissibility candidate",
        "does not execute C_k variation",
        "does not verify route alignment",
        "no QFT-GR closure",
        "no master-action promotion",
        "NOT_RUN",
    ]:
        assert token in joined


def test_a_bridge_ck_candidate_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_bridge_admissibility_ck_constraint_candidate_packet_gate.py"
    )
