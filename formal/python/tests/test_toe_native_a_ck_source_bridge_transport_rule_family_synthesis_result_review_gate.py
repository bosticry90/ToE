from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_ck_source_bridge_transport_rule_family_synthesis_result_review_report import (
    ALTERNATE_AFTER_CLOSEOUT_SELECTOR_TARGET,
    ARTIFACT_ID,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_RULE_CLASSIFICATION,
    CLOSEOUT_OUTCOME_HINT,
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
    QFTGR_AGGREGATE_PATH,
    RECOMMENDED_AFTER_CLOSEOUT_SELECTOR_TARGET,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    RULE_FAMILY_CLASSIFICATION,
    SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLASSIFICATION,
    SOURCE_RULE_DISPLAY_FORM,
    SYNTHESIS_PACKET_OUTCOME,
    SYNTHESIS_PACKET_PATH,
    SYNTHESIS_PACKET_RESULT,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_DISPLAY_FORM,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
    build_toe_native_a_ck_source_bridge_transport_rule_family_synthesis_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_ck_source_bridge_transport_rule_family_synthesis_result_review_report.py"
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


def test_A_ck_source_bridge_transport_rule_family_synthesis_result_review_files_exist() -> None:
    for path in [
        SYNTHESIS_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_A_ck_source_bridge_transport_rule_family_synthesis_result_review_accepts_packet() -> None:
    packet = _json(SYNTHESIS_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == SYNTHESIS_PACKET_OUTCOME
    assert packet["packet_result"] == SYNTHESIS_PACKET_RESULT
    assert packet["selected_next_target"] == CONSUMED_TARGET
    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["closeout_outcome_hint"] == CLOSEOUT_OUTCOME_HINT
    assert (
        build_toe_native_a_ck_source_bridge_transport_rule_family_synthesis_result_review()
        == review
    )


def test_A_ck_source_bridge_transport_rule_family_synthesis_result_review_preserves_triad() -> None:
    review = _json(DEFAULT_OUT)
    assert review["A_ck_admissibility_rule_family_count"] == 3
    assert review["rule_family_classification"] == RULE_FAMILY_CLASSIFICATION
    assert review["concrete_A_ck_rule_roles"] == [
        "source admissibility",
        "bridge admissibility",
        "transport consistency",
    ]
    assert review["rule_family_display_forms"] == [
        SOURCE_RULE_DISPLAY_FORM,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        TRANSPORT_RULE_DISPLAY_FORM,
    ]
    assert review["source_rule_classification"] == SOURCE_RULE_CLASSIFICATION
    assert review["source_rule_display_form"] == SOURCE_RULE_DISPLAY_FORM
    assert review["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert review["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert review["source_candidate_constraint_equation"] == (
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert review["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["bridge_rule_classification"] == BRIDGE_RULE_CLASSIFICATION
    assert review["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert review["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert review["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["transport_closeout_rule_classification"] == (
        TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION
    )
    assert review["transport_rule_epistemic_status"] == (
        TRANSPORT_RULE_EPISTEMIC_STATUS
    )
    assert review["transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert review["transport_candidate_type"] == TRANSPORT_CANDIDATE_TYPE
    assert review["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert review["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert review["transport_admissibility_constraint_form"] == (
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["transport_component_forms"] == [
        row["component_form"] for row in TRANSPORT_COMPONENTS
    ]


def test_A_ck_source_bridge_transport_rule_family_synthesis_result_review_blocks_claims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_criteria_count"] == 10
    assert review["review_criteria_accepted_count"] == 10
    for key in [
        "review_executed",
        "result_review_prepared",
        "result_review_accepted",
        "synthesis_packet_accepted",
        "source_rule_synthesis_accepted",
        "bridge_rule_synthesis_accepted",
        "transport_rule_synthesis_accepted",
        "source_bridge_transport_rule_synthesis_accepted",
        "three_rule_family_review_accepted",
        "c_k_instantiated_as_three_admissibility_rules",
        "c_k_source_permission_role_accepted",
        "c_k_bridge_permission_role_accepted",
        "c_k_transport_stability_role_accepted",
        "all_three_rules_admissibility_only",
        "all_three_rules_rule_candidates",
        "all_three_rules_not_action_terms",
        "all_three_rules_not_dynamical_laws",
        "no_J_nu_derivation",
        "no_sourced_maxwell_derivation",
        "triad_closeout_authorized",
    ]:
        assert review[key] is True, key
    assert review["triad_closeout_prepared"] is False
    for key in [
        "selector_after_closeout_authorized",
        "next_master_action_surface_selected",
        "next_ck_constraint_family_selected",
        "another_A_route_selected",
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
        "A_variation_executed",
        "bridge_admissibility_proved",
        "route_alignment_verified",
        "full_route_alignment_proved",
        "source_admissibility_proved",
        "source_conservation_proved",
        "transport_consistency_proved",
        "transport_proof_claimed",
        "transport_components_proved",
        "current_route_derived",
        "current_source_route_constructed",
        "matter_current_J_nu_derived",
        "J_nu_derived",
        "psi_current_route_constructed",
        "external_current_native_derivation_selected",
        "matter_current_exchange_route_proved",
        "matter_gauge_energy_exchange_proved",
        "sourced_maxwell_equation_derived",
        "sourced_maxwell_route_derived",
        "full_em_closure_claimed",
        "em_closure_claimed",
        "em_qft_closure_claimed",
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
        assert review[key] is False, key
    for phrase in [
        "no action embedding",
        "no action term",
        "no C_k variation",
        "no dynamical-law claim",
        "no current route",
        "no J^nu derivation",
        "no sourced Maxwell derivation",
        "no matter/current exchange",
        "no EM closure",
        "no QFT-GR closure",
        "no semiclassical coupling",
        "no empirical validation",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in review["non_claim_boundary"], phrase


def test_A_ck_source_bridge_transport_rule_family_synthesis_result_review_validation_policy() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert review["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert review["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert review["full_toeformal_aggregate_passed"] is False
    assert review["full_toeformal_aggregate_failed"] is False
    assert review["full_toeformal_aggregate_timed_out"] is False


def test_A_ck_source_bridge_transport_rule_family_synthesis_result_review_rotates_to_closeout() -> None:
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
        "ToeNativeACKSourceBridgeTransportRuleFamilySynthesisResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_"
        "20260624_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["three_rule_family_review_accepted"] == "yes"
    assert consumed["all_three_rules_admissibility_only"] == "yes"
    assert consumed["all_three_rules_not_action_terms"] == "yes"
    assert consumed["no_J_nu_derivation"] == "yes"
    assert consumed["no_sourced_maxwell_derivation"] == "yes"
    assert consumed["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["closeout_outcome_hint"] == CLOSEOUT_OUTCOME_HINT
    assert active_row["triad_closeout_authorized"] == "yes"
    assert active_row["triad_closeout_prepared"] == "no"
    assert active_row["selected_next_target"] == NEXT_TARGET
    assert active_row["all_three_rules_admissibility_only"] == "yes"
    assert active_row["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_A_ck_source_bridge_transport_rule_family_synthesis_result_review_mirrors() -> None:
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
        REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        CLOSEOUT_OUTCOME_HINT,
        RECOMMENDED_AFTER_CLOSEOUT_SELECTOR_TARGET,
        ALTERNATE_AFTER_CLOSEOUT_SELECTOR_TARGET,
        "ToeNativeACKSourceBridgeTransportRuleFamilySynthesisResultReview",
        "prepare_toe_native_A_ck_source_bridge_transport_rule_family_closeout",
        SOURCE_RULE_DISPLAY_FORM,
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        "first A-relevant three-rule C_k admissibility family",
        "source admissibility",
        "bridge admissibility",
        "transport consistency",
        "admissibility-only",
        "not action terms",
        "not dynamical laws",
        "not current-coupled",
        "no J^nu derivation",
        "no sourced Maxwell",
        "no EM closure",
        "not QFT-GR closure",
        "not master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_A_ck_source_bridge_transport_rule_family_synthesis_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_ck_source_bridge_transport_rule_family_synthesis_result_review_gate.py"
    )
