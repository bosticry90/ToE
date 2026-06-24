from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_ck_source_bridge_transport_rule_family_synthesis_packet_report import (
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    ARTIFACT_ID,
    BRIDGE_RULE_CLASSIFICATION,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
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
    REVIEW_OUTCOME_HINT,
    RULE_FAMILY_CLASSIFICATION,
    SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLASSIFICATION,
    SOURCE_RULE_DISPLAY_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_CLOSEOUT_OUTCOME,
    TRANSPORT_CLOSEOUT_PATH,
    TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
    TRANSPORT_CLOSEOUT_RULE_ROLE,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_CLASSIFICATION,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
    build_toe_native_a_ck_source_bridge_transport_rule_family_synthesis_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_ck_source_bridge_transport_rule_family_synthesis_packet_report.py"
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


def test_a_ck_source_bridge_transport_synthesis_files_exist() -> None:
    for path in [
        TRANSPORT_CLOSEOUT_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_ck_source_bridge_transport_synthesis_accepts_closeout() -> None:
    closeout = _json(TRANSPORT_CLOSEOUT_PATH)
    packet = _json(DEFAULT_OUT)
    assert closeout["outcome_id"] == TRANSPORT_CLOSEOUT_OUTCOME
    assert closeout["selected_next_target"] == CONSUMED_TARGET
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
    assert packet["review_outcome_hint"] == REVIEW_OUTCOME_HINT
    assert (
        build_toe_native_a_ck_source_bridge_transport_rule_family_synthesis_packet()
        == packet
    )


def test_a_ck_source_bridge_transport_synthesis_preserves_triad() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["A_ck_admissibility_rule_family_count"] == 3
    assert packet["rule_family_classification"] == RULE_FAMILY_CLASSIFICATION
    assert packet["concrete_A_ck_rule_roles"] == [
        "source admissibility",
        "bridge admissibility",
        "transport consistency",
    ]
    assert packet["rule_family_display_forms"] == [
        SOURCE_RULE_DISPLAY_FORM,
        A_BRIDGE_CONSTRAINT_EQUATION,
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    ]
    assert packet["source_rule_classification"] == SOURCE_RULE_CLASSIFICATION
    assert packet["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert packet["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert packet["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert packet["source_rule_display_form"] == SOURCE_RULE_DISPLAY_FORM
    assert packet["bridge_rule_classification"] == BRIDGE_RULE_CLASSIFICATION
    assert packet["A_bridge_constraint_form"] == A_BRIDGE_CONSTRAINT_FORM
    assert packet["A_bridge_constraint_equation"] == A_BRIDGE_CONSTRAINT_EQUATION
    assert packet["bridge_admissibility_constraint_form"] == (
        A_BRIDGE_CONSTRAINT_EQUATION
    )
    assert packet["transport_rule_classification"] == TRANSPORT_RULE_CLASSIFICATION
    assert packet["transport_closeout_rule_classification"] == (
        TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION
    )
    assert packet["transport_rule_subclassification"] == TRANSPORT_CLOSEOUT_RULE_ROLE
    assert packet["transport_rule_epistemic_status"] == (
        TRANSPORT_RULE_EPISTEMIC_STATUS
    )
    assert packet["transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert packet["transport_candidate_type"] == TRANSPORT_CANDIDATE_TYPE
    assert packet["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert packet["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert packet["transport_admissibility_constraint_form"] == (
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert packet["transport_component_forms"] == [
        row["component_form"] for row in TRANSPORT_COMPONENTS
    ]
    assert {row["rule_id"] for row in packet["rule_family_entries"]} == {
        "A_source_admissibility_ck_rule",
        "A_bridge_admissibility_ck_rule",
        "A_transport_consistency_ck_rule",
    }


def test_a_ck_source_bridge_transport_synthesis_blocks_claims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["synthesis_criteria_count"] == 12
    assert packet["synthesis_criteria_accepted_count"] == 12
    for key in [
        "synthesis_packet_prepared",
        "synthesis_packet_accepted",
        "A_ck_rule_family_synthesized",
        "three_rule_family_synthesized",
        "three_A_relevant_ck_admissibility_rules_synthesized",
        "source_bridge_transport_rules_synthesized",
        "source_admissibility_rule_synthesized",
        "bridge_admissibility_rule_synthesized",
        "transport_consistency_rule_synthesized",
        "source_admissibility_rule_preserved",
        "bridge_admissibility_rule_preserved",
        "transport_consistency_rule_preserved",
        "c_k_acquired_three_concrete_A_relevant_rule_roles",
        "source_rule_decides_A_conserved_vacuum_source_permission",
        "bridge_rule_decides_A_vacuum_route_consistency",
        "transport_rule_decides_A_derivation_chain_coherence",
        "all_three_rules_admissibility_only",
        "all_three_rules_not_action_terms",
        "all_three_rules_not_dynamical_laws",
        "all_three_rules_not_current_coupled",
        "rule_family_interprets_ck_as_seam_admissibility_layer",
        "result_review_authorized",
    ]:
        assert packet[key] is True, key
    for key in [
        "review_executed",
        "another_A_route_selected",
        "current_route_derived",
        "current_source_route_constructed",
        "J_nu_derived",
        "psi_current_route_constructed",
        "external_current_native_derivation_selected",
        "sourced_maxwell_equation_derived",
        "matter_current_exchange_route_proved",
        "constraint_as_action_term_selected",
        "dynamical_action_embedding_selected",
        "dynamical_law_claimed",
        "C_k_action_embedding_constructed",
        "C_k_variation_executed",
        "bridge_admissibility_proved",
        "route_alignment_verified",
        "full_route_alignment_proved",
        "source_admissibility_proved",
        "transport_consistency_proved",
        "transport_proof_claimed",
        "transport_components_proved",
        "transport_candidate_functional_defined",
        "fully_concrete_ck_functional_defined",
        "full_em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_claimed",
        "empirical_validation_claimed",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "canonical_master_action_promoted",
        "phase2_readiness_claim",
        "pillar_completion_inferred",
        "seam_closure_claim",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "source, bridge, and transport",
        "vacuum U(1) admissibility-only rules",
        "not action terms",
        "not dynamical laws",
        "not current-coupled rules",
        "not sourced Maxwell",
        "not EM closure",
        "not QFT-GR closure",
        "not master-action promotion",
        "does not derive J^nu",
        "does not prove matter/current exchange",
        "does not execute C_k variation",
        "does not prove transport consistency",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_a_ck_source_bridge_transport_synthesis_validation_policy() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert packet["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert packet["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert packet["full_toeformal_aggregate_passed"] is False
    assert packet["full_toeformal_aggregate_failed"] is False
    assert packet["full_toeformal_aggregate_timed_out"] is False


def test_a_ck_source_bridge_transport_synthesis_rotates_to_review() -> None:
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
        "ToeNativeACKSourceBridgeTransportRuleFamilySynthesisPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_PACKET_"
        "20260624_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["three_rule_family_synthesized"] == "yes"
    assert consumed["all_three_rules_admissibility_only"] == "yes"
    assert consumed["all_three_rules_not_action_terms"] == "yes"
    assert consumed["all_three_rules_not_current_coupled"] == "yes"
    assert consumed["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["sourced_maxwell_equation_derived"] == "no"
    assert consumed["full_em_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["packet_result"] == OUTCOME_ID
    assert active_row["review_executed"] == "no"
    assert active_row["synthesis_packet_prepared"] == "yes"
    assert active_row["three_rule_family_synthesized"] == "yes"
    assert active_row["all_three_rules_admissibility_only"] == "yes"
    assert active_row["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert active_row["C_k_variation_executed"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["full_em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_ck_source_bridge_transport_synthesis_mirrors() -> None:
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
        "ToeNativeACKSourceBridgeTransportRuleFamilySynthesisPacket",
        (
            "CURRENT_LIVE_NEXT_TARGET_v0: "
            "review_toe_native_A_ck_source_bridge_transport_rule_family_synthesis_packet_result"
        ),
        SOURCE_RULE_DISPLAY_FORM,
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        A_BRIDGE_CONSTRAINT_EQUATION,
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        RULE_FAMILY_CLASSIFICATION,
        "source admissibility",
        "bridge admissibility",
        "transport consistency",
        "admissibility-only",
        "not action terms",
        "not dynamical laws",
        "not current-coupled",
        "not sourced Maxwell",
        "not EM closure",
        "not QFT-GR closure",
        "not master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_a_ck_source_bridge_transport_synthesis_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_ck_source_bridge_transport_rule_family_synthesis_packet_gate.py"
    )
