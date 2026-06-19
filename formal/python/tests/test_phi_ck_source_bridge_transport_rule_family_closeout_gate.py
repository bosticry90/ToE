from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_ck_source_bridge_transport_rule_family_closeout_report import (
    ARTIFACT_ID,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_RULE_CLASSIFICATION,
    CLOSEOUT_RESULT,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FIRST_TRIAD_FAMILY_CLASSIFICATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RECOMMENDED_NEXT_MASTER_ACTION_SURFACE,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RULE_FAMILY_CLASSIFICATION,
    RULE_FAMILY_EPISTEMIC_STATUS,
    SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLASSIFICATION,
    SOURCE_RULE_DISPLAY_FORM,
    TRIAD_RESULT_REVIEW_OUTCOME,
    TRIAD_RESULT_REVIEW_PATH,
    TRIAD_REVIEW_RESULT,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_DISPLAY_FORM,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
    build_phi_ck_source_bridge_transport_rule_family_closeout,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_ck_source_bridge_transport_rule_family_closeout_report.py"
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


def test_phi_ck_source_bridge_transport_rule_family_closeout_files_exist() -> None:
    for path in [
        TRIAD_RESULT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_ck_source_bridge_transport_rule_family_closeout_accepts_review() -> None:
    review = _json(TRIAD_RESULT_REVIEW_PATH)
    closeout = _json(DEFAULT_OUT)
    assert review["outcome_id"] == TRIAD_RESULT_REVIEW_OUTCOME
    assert review["review_result"] == TRIAD_REVIEW_RESULT
    assert review["selected_next_target"] == CONSUMED_TARGET
    assert closeout["artifact_id"] == ARTIFACT_ID
    assert closeout["schema_id"] == SCHEMA_ID
    assert closeout["packet_id"] == PACKET_ID
    assert closeout["prepared"] is True
    assert closeout["accepted"] is True
    assert closeout["outcome_id"] == OUTCOME_ID
    assert closeout["closeout_result"] == CLOSEOUT_RESULT
    assert closeout["packet_classification"] == PACKET_CLASSIFICATION
    assert closeout["consumed_target"] == CONSUMED_TARGET
    assert closeout["selected_next_target"] == NEXT_TARGET
    assert closeout["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_phi_ck_source_bridge_transport_rule_family_closeout() == closeout


def test_phi_ck_source_bridge_transport_rule_family_closeout_preserves_triad() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["family_classification"] == FIRST_TRIAD_FAMILY_CLASSIFICATION
    assert closeout["family_epistemic_status"] == RULE_FAMILY_EPISTEMIC_STATUS
    assert closeout["rule_family_classification"] == RULE_FAMILY_CLASSIFICATION
    assert closeout["phi_ck_admissibility_rule_family_count"] == 3
    assert closeout["concrete_phi_ck_rule_roles"] == [
        "source admissibility",
        "bridge admissibility",
        "transport consistency",
    ]
    assert closeout["rule_family_display_forms"] == [
        SOURCE_RULE_DISPLAY_FORM,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        TRANSPORT_RULE_DISPLAY_FORM,
    ]
    assert closeout["source_rule_classification"] == SOURCE_RULE_CLASSIFICATION
    assert closeout["source_rule_display_form"] == SOURCE_RULE_DISPLAY_FORM
    assert closeout["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert closeout["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert closeout["source_candidate_constraint_equation"] == (
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert closeout["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert closeout["bridge_rule_classification"] == BRIDGE_RULE_CLASSIFICATION
    assert closeout["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert closeout["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert closeout["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert closeout["transport_rule_classification"] == "transport-consistency rule candidate"
    assert closeout["transport_rule_epistemic_status"] == (
        TRANSPORT_RULE_EPISTEMIC_STATUS
    )
    assert closeout["transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert closeout["transport_candidate_type"] == TRANSPORT_CANDIDATE_TYPE
    assert closeout["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert closeout["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert closeout["transport_admissibility_constraint_form"] == (
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert closeout["transport_component_forms"] == [
        row["component_form"] for row in TRANSPORT_COMPONENTS
    ]


def test_phi_ck_source_bridge_transport_rule_family_closeout_blocks_claims() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["closeout_criteria_count"] == 10
    assert closeout["closeout_criteria_accepted_count"] == 10
    for key in [
        "closeout_prepared",
        "closeout_accepted",
        "first_phi_relevant_three_rule_ck_family_closed",
        "source_bridge_transport_admissibility_rule_family_closed",
        "source_admissibility_rule_closed_in_family",
        "bridge_admissibility_rule_closed_in_family",
        "transport_consistency_rule_closed_in_family",
        "c_k_source_permission_role_closed",
        "c_k_bridge_permission_role_closed",
        "c_k_transport_stability_role_closed",
        "all_three_rules_admissibility_only",
        "all_three_rules_rule_candidates",
        "all_three_rules_not_action_terms",
        "all_three_rules_not_action_embedded",
        "all_three_rules_not_varied",
        "all_three_rules_not_promoted",
        "all_three_rules_not_dynamical_laws",
        "none_of_three_rules_derives_phi",
        "none_of_three_rules_derives_v_phi",
        "selector_target_authorized",
        "a_surface_gauge_route_recommended",
        "psi_surface_deferred_as_harder",
        "rho_surface_deferred_as_more_speculative",
        "further_phi_ck_elaboration_deferred",
    ]:
        assert closeout[key] is True, key
    assert closeout["selector_target_prepared"] is False
    assert closeout["recommended_next_master_action_surface"] == (
        RECOMMENDED_NEXT_MASTER_ACTION_SURFACE
    )
    for key in [
        "next_master_action_surface_selected",
        "next_ck_constraint_family_selected",
        "another_phi_derivation_selected",
        "constraint_as_action_term_selected",
        "dynamical_action_embedding_selected",
        "dynamical_law_claimed",
        "candidate_recorded_as_new_physical_law",
        "candidate_recorded_as_action_term",
        "ck_action_embedding_claimed",
        "ck_variation_executed",
        "ck_variation_authorized",
        "lambda_variation_executed",
        "metric_variation_executed",
        "phi_variation_executed",
        "bridge_admissibility_proved",
        "route_alignment_verified",
        "full_route_alignment_proved",
        "source_admissibility_proved",
        "source_conservation_proved",
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
        assert closeout[key] is False, key
    for phrase in [
        "first phi-relevant three-rule C_k family",
        "admissibility-only",
        "not action-embedded",
        "not varied",
        "not promoted",
        "not action terms",
        "not dynamical laws",
        "not native phi derivation",
        "not V(phi) derivation",
        "not QFT-GR closure",
        "not semiclassical coupling",
        "not empirical validation",
        "not master-action promotion",
        "does not execute C_k variation",
        "A_surface_gauge_route recommended but not selected here",
    ]:
        assert phrase in closeout["non_claim_boundary"], phrase


def test_phi_ck_source_bridge_transport_rule_family_closeout_validation_policy() -> None:
    closeout = _json(DEFAULT_OUT)
    policy = closeout["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["aggregate_lean_validation_status_allowed_values"] == ["NOT_RUN"]
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert closeout["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert closeout["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert closeout["full_toeformal_aggregate_passed"] is False
    assert closeout["full_toeformal_aggregate_failed"] is False
    assert closeout["full_toeformal_aggregate_timed_out"] is False


def test_phi_ck_source_bridge_transport_rule_family_closeout_rotates_to_surface_selector() -> None:
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
        "PhiCKSourceBridgeTransportRuleFamilyCloseout.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_CLOSEOUT_20260619_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["first_phi_relevant_three_rule_ck_family_closed"] == "yes"
    assert consumed["source_bridge_transport_admissibility_rule_family_closed"] == "yes"
    assert consumed["selector_target_authorized"] == "yes"
    assert consumed["selector_target_prepared"] == "no"
    assert consumed["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["closeout_result"] == OUTCOME_ID
    assert active_row["selection_result"] == "PENDING"
    assert active_row["selector_executed"] == "no"
    assert active_row["recommended_next_master_action_surface"] == (
        RECOMMENDED_NEXT_MASTER_ACTION_SURFACE
    )
    assert active_row["a_surface_gauge_route_recommended"] == "yes"
    assert active_row["next_master_action_surface_selected"] == "no"
    assert active_row["next_ck_constraint_family_selected"] == "no"
    assert active_row["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_ck_source_bridge_transport_rule_family_closeout_mirrors() -> None:
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
        CLOSEOUT_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        RECOMMENDED_NEXT_MASTER_ACTION_SURFACE,
        "PhiCKSourceBridgeTransportRuleFamilyCloseout",
        "CURRENT_LIVE_NEXT_TARGET_v0: select_next_master_action_surface_after_phi_ck_triad",
        SOURCE_RULE_DISPLAY_FORM,
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        "first phi-relevant three-rule C_k family",
        "source admissibility",
        "bridge admissibility",
        "transport consistency",
        "admissibility-only",
        "not action-embedded",
        "not varied",
        "not promoted",
        "not QFT-GR closure",
        "not master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_phi_ck_source_bridge_transport_rule_family_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_ck_source_bridge_transport_rule_family_closeout_gate.py"
    )
