from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_transport_consistency_ck_constraint_candidate_packet_report import (
    ARTIFACT_ID,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    KNOWN_PHI_TRANSPORT_CHAIN_FORM,
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
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_CLASSIFICATION,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
    build_phi_transport_consistency_ck_constraint_candidate_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_transport_consistency_ck_constraint_candidate_packet_report.py"
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


def test_phi_transport_consistency_ck_candidate_packet_files_exist() -> None:
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


def test_phi_transport_consistency_ck_candidate_packet_accepts_selector() -> None:
    packet = _json(DEFAULT_OUT)
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
    assert build_phi_transport_consistency_ck_constraint_candidate_packet() == packet


def test_phi_transport_consistency_ck_candidate_records_transport_tuple() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert packet["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert packet["transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert packet["transport_candidate_type"] == TRANSPORT_CANDIDATE_TYPE
    assert packet["transport_rule_classification"] == TRANSPORT_RULE_CLASSIFICATION
    assert packet["transport_rule_epistemic_status"] == TRANSPORT_RULE_EPISTEMIC_STATUS
    assert packet["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert packet["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert packet["transport_tuple_recorded"] is True
    assert packet["transport_tuple_proved"] is False
    assert packet["transport_candidate_recorded_as_admissibility_rule"] is True
    assert packet["transport_candidate_recorded_as_transport_stability_rule"] is True
    assert packet["transport_candidate_recorded_as_action_term"] is False
    assert packet["transport_candidate_recorded_as_new_dynamical_law"] is False


def test_phi_transport_consistency_ck_candidate_preserves_source_bridge_context() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert packet["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert packet["source_candidate_constraint_equation"] == (
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert packet["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert packet["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert packet["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert packet["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert packet["bridge_route_field_equation_match"] == (
        BRIDGE_ROUTE_FIELD_EQUATION_MATCH
    )
    assert packet["bridge_route_stress_energy_match"] == (
        BRIDGE_ROUTE_STRESS_ENERGY_MATCH
    )
    assert packet["bridge_route_source_residual_match"] == (
        BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
    )
    assert packet["closed_phi_ck_rule_roles"] == [
        "source admissibility",
        "bridge admissibility",
        "transport consistency",
    ]
    assert packet["phi_ck_rule_family_count_after_packet"] == 3


def test_phi_transport_consistency_ck_candidate_records_components_unproved() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["known_phi_transport_chain_form"] == KNOWN_PHI_TRANSPORT_CHAIN_FORM
    assert packet["known_phi_chain_recorded"] is True
    assert packet["known_phi_chain_proved"] is False
    assert packet["transport_component_count"] == len(TRANSPORT_COMPONENTS)
    assert packet["transport_components_recorded"] is True
    assert packet["transport_components_proved"] is False
    assert [
        row["component_form"] for row in packet["transport_components"]
    ] == [row["component_form"] for row in TRANSPORT_COMPONENTS]
    assert all(row["recorded_here"] is True for row in packet["transport_components"])
    assert all(row["proved_here"] is False for row in packet["transport_components"])
    assert all(
        row["variation_executed_here"] is False
        for row in packet["transport_components"]
    )
    assert all(
        row["action_term_defined_here"] is False
        for row in packet["transport_components"]
    )


def test_phi_transport_consistency_ck_candidate_blocks_shortcuts() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "transport_candidate_functional_defined",
        "transport_candidate_functional_selected",
        "transport_candidate_rule_proved",
        "transport_consistency_claimed",
        "transport_consistency_proved",
        "transport_proof_claimed",
        "full_route_alignment_proof_claimed",
        "full_route_alignment_proved",
        "route_chain_compatibility_proved",
        "source_admissibility_proved",
        "bridge_admissibility_proved",
        "new_conservation_proof_claimed",
        "new_source_admissibility_proof_claimed",
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "ck_action_embedding_claimed",
        "candidate_action_insertion_executed",
        "constraint_as_action_term_selected",
        "constraint_term_selected",
        "ck_variation_executed",
        "ck_variation_authorized",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "phi_variation_of_candidate_executed",
        "native_phi_derivation_claimed",
        "phi_generated_by_ck_claimed",
        "v_phi_derivation_claimed",
        "derived_v_phi_claimed",
        "potential_derived",
        "qft_gr_closure_claimed",
        "qft_gr_solved",
        "qft_gr_seam_closed",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "canonical_master_action_promoted",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "phase2_readiness_claim",
        "pillar_completion_inferred",
        "seam_closure_claim",
    ]:
        assert packet[key] is False, key
    assert "does not embed C_transport^phi into the action" in packet["non_claim_boundary"]
    assert "does not execute C_k variation" in packet["non_claim_boundary"]
    assert "does not prove transport consistency" in packet["non_claim_boundary"]
    assert "does not prove full route alignment" in packet["non_claim_boundary"]
    assert "does not close QFT-GR" in packet["non_claim_boundary"]
    assert "does not promote the master action" in packet["non_claim_boundary"]


def test_phi_transport_consistency_ck_candidate_validation_policy_not_run() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["aggregate_lean_validation_status_allowed_values"] == ["NOT_RUN"]
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert packet["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert packet["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert packet["full_toeformal_aggregate_passed"] is False
    assert packet["full_toeformal_aggregate_failed"] is False
    assert packet["full_toeformal_aggregate_timed_out"] is False


def test_phi_transport_consistency_ck_candidate_rotates_to_review() -> None:
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
        "PhiTransportConsistencyCKConstraintCandidatePacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_20260619_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == PACKET_RESULT
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert consumed["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert consumed["transport_candidate_recorded_as_admissibility_rule"] == "yes"
    assert consumed["transport_candidate_functional_defined"] == "no"
    assert consumed["transport_consistency_proved"] == "no"
    assert consumed["result_review_authorized"] == "yes"
    assert consumed["review_prepared"] == "no"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["packet_result"] == PACKET_RESULT
    assert active_row["result_review_authorized"] == "yes"
    assert active_row["result_review_prepared"] == "no"
    assert active_row["review_prepared"] == "no"
    assert active_row["review_executed"] == "no"
    assert active_row["transport_candidate_recorded_as_admissibility_rule"] == "yes"
    assert active_row["transport_candidate_functional_defined"] == "no"
    assert active_row["transport_consistency_proved"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_transport_consistency_ck_candidate_mirrors() -> None:
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
        "PhiTransportConsistencyCKConstraintCandidatePacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: review_phi_transport_consistency_ck_constraint_candidate_packet_result",
        SOURCE_CANDIDATE_CONSTRAINT_FORM,
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        BRIDGE_CONSTRAINT_FORM,
        BRIDGE_CONSTRAINT_EQUATION,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        TRANSPORT_CONSTRAINT_FORM,
        TRANSPORT_CONSTRAINT_EQUATION,
        "source admissibility, bridge admissibility, and transport consistency",
        "does not execute C_k variation",
        "does not prove transport consistency",
        "does not prove full route alignment",
        "does not close QFT-GR",
        "does not promote the master action",
        "NOT_RUN",
    ]:
        assert token in joined


def test_phi_transport_consistency_ck_candidate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_transport_consistency_ck_constraint_candidate_packet_gate.py"
    )
