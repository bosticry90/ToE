from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_ck_source_bridge_transport_rule_family_synthesis_packet_report import (
    ARTIFACT_ID,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
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
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
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
    build_phi_ck_source_bridge_transport_rule_family_synthesis_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_ck_source_bridge_transport_rule_family_synthesis_packet_report.py"
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


def test_phi_ck_source_bridge_transport_rule_family_synthesis_packet_files_exist() -> None:
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


def test_phi_ck_source_bridge_transport_rule_family_synthesis_packet_accepts_closeout() -> None:
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
    assert build_phi_ck_source_bridge_transport_rule_family_synthesis_packet() == packet


def test_phi_ck_source_bridge_transport_rule_family_synthesis_packet_preserves_triad() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["phi_ck_admissibility_rule_family_count"] == 3
    assert packet["rule_family_classification"] == RULE_FAMILY_CLASSIFICATION
    assert packet["concrete_phi_ck_rule_roles"] == [
        "source admissibility",
        "bridge admissibility",
        "transport consistency",
    ]
    assert packet["rule_family_display_forms"] == [
        SOURCE_RULE_DISPLAY_FORM,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    ]
    assert packet["source_rule_classification"] == SOURCE_RULE_CLASSIFICATION
    assert packet["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert packet["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert packet["source_candidate_constraint_equation"] == (
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert packet["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert packet["source_rule_display_form"] == SOURCE_RULE_DISPLAY_FORM
    assert packet["bridge_rule_classification"] == BRIDGE_RULE_CLASSIFICATION
    assert packet["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert packet["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert packet["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
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
        "phi_source_admissibility_ck_rule",
        "phi_bridge_admissibility_ck_rule",
        "phi_transport_consistency_ck_rule",
    }


def test_phi_ck_source_bridge_transport_rule_family_synthesis_packet_blocks_claims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["synthesis_criteria_count"] == 12
    assert packet["synthesis_criteria_accepted_count"] == 12
    for key in [
        "synthesis_packet_prepared",
        "synthesis_packet_accepted",
        "phi_ck_rule_family_synthesized",
        "three_rule_family_synthesized",
        "three_phi_relevant_ck_admissibility_rule_candidates_synthesized",
        "source_bridge_transport_rules_synthesized",
        "source_admissibility_rule_synthesized",
        "bridge_admissibility_rule_synthesized",
        "transport_consistency_rule_synthesized",
        "source_admissibility_rule_preserved",
        "bridge_admissibility_rule_preserved",
        "transport_consistency_rule_preserved",
        "c_k_acquired_three_concrete_phi_relevant_rule_roles",
        "source_rule_decides_phi_source_permission",
        "bridge_rule_decides_phi_route_consistency",
        "transport_rule_decides_derivation_chain_coherence",
        "all_three_rules_admissibility_only",
        "all_three_rules_rule_candidates",
        "all_three_rules_not_action_terms",
        "all_three_rules_not_dynamical_laws",
        "none_of_three_rules_derives_phi",
        "none_of_three_rules_derives_v_phi",
        "rule_family_interprets_ck_as_seam_admissibility_layer",
        "result_review_authorized",
    ]:
        assert packet[key] is True, key
    for key in [
        "review_executed",
        "another_phi_derivation_selected",
        "constraint_as_action_term_selected",
        "dynamical_action_embedding_selected",
        "dynamical_law_claimed",
        "ck_action_embedding_claimed",
        "ck_variation_executed",
        "ck_variation_authorized",
        "bridge_admissibility_proved",
        "route_alignment_verified",
        "full_route_alignment_proved",
        "source_admissibility_proved",
        "transport_consistency_proved",
        "transport_proof_claimed",
        "transport_components_proved",
        "native_phi_derivation_claimed",
        "phi_generated_by_ck_claimed",
        "v_phi_derivation_claimed",
        "potential_derived",
        "new_conservation_proof_claimed",
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
        "admissibility-only rule candidates",
        "not action terms",
        "not dynamical laws",
        "not native phi derivations",
        "not V(phi) derivations",
        "not QFT-GR closure",
        "not master-action promotion",
        "does not execute C_k variation",
        "does not prove transport consistency",
        "does not prove full route alignment",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_phi_ck_source_bridge_transport_rule_family_synthesis_packet_validation_policy() -> None:
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


def test_phi_ck_source_bridge_transport_rule_family_synthesis_packet_rotates_to_review() -> None:
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
        "PhiCKSourceBridgeTransportRuleFamilySynthesisPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_PACKET_20260619_v0.json"
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
    assert consumed["none_of_three_rules_derives_phi"] == "yes"
    assert consumed["none_of_three_rules_derives_v_phi"] == "yes"
    assert consumed["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
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
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_ck_source_bridge_transport_rule_family_synthesis_packet_mirrors() -> None:
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
        "PhiCKSourceBridgeTransportRuleFamilySynthesisPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: review_phi_ck_source_bridge_transport_rule_family_synthesis_packet_result",
        SOURCE_RULE_DISPLAY_FORM,
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        "three phi-relevant C_k admissibility-rule candidates",
        "source admissibility",
        "bridge admissibility",
        "transport consistency",
        "admissibility-only",
        "not action terms",
        "not dynamical laws",
        "not native phi derivations",
        "not V(phi) derivations",
        "not QFT-GR closure",
        "not master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_phi_ck_source_bridge_transport_rule_family_synthesis_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_ck_source_bridge_transport_rule_family_synthesis_packet_gate.py"
    )
