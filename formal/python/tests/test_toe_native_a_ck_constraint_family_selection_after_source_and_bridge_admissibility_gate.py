from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_ck_constraint_family_selection_after_source_and_bridge_admissibility_report import (
    ARTIFACT_ID,
    BRIDGE_CLOSEOUT_OUTCOME,
    BRIDGE_CLOSEOUT_PATH,
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
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS,
    SELECTION_RESULT,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_PLAIN_MEANING,
    TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
    TRANSPORT_CANDIDATE_TUPLE_PREVIEW,
    TRANSPORT_CHAIN_FORM,
    TRANSPORT_CHAIN_STEPS,
    TRANSPORT_CONSISTENCY_QUESTION,
    TRANSPORT_TUPLE_COMPONENTS,
    build_toe_native_a_ck_constraint_family_selection_after_source_and_bridge_admissibility,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_ck_constraint_family_selection_after_source_and_bridge_admissibility_report.py"
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


def test_a_source_bridge_selector_files_exist() -> None:
    for path in [
        BRIDGE_CLOSEOUT_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_source_bridge_selector_accepts_bridge_closeout() -> None:
    closeout = _json(BRIDGE_CLOSEOUT_PATH)
    selection = _json(DEFAULT_OUT)
    assert closeout["outcome_id"] == BRIDGE_CLOSEOUT_OUTCOME
    assert closeout["selected_next_target"] == CONSUMED_TARGET
    assert selection["artifact_id"] == ARTIFACT_ID
    assert selection["schema_id"] == SCHEMA_ID
    assert selection["packet_id"] == PACKET_ID
    assert selection["prepared"] is True
    assert selection["accepted"] is True
    assert selection["outcome_id"] == OUTCOME_ID
    assert selection["selection_result"] == SELECTION_RESULT
    assert selection["packet_classification"] == PACKET_CLASSIFICATION
    assert selection["consumed_target"] == CONSUMED_TARGET
    assert selection["selected_next_target"] == NEXT_TARGET
    assert selection["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert (
        build_toe_native_a_ck_constraint_family_selection_after_source_and_bridge_admissibility()
        == selection
    )


def test_a_source_bridge_selector_preserves_closed_source_and_bridge_rules() -> None:
    selection = _json(DEFAULT_OUT)
    assert (
        selection["source_candidate_constraint_form"]
        == SOURCE_CANDIDATE_CONSTRAINT_FORM
    )
    assert (
        selection["source_admissibility_constraint_form"]
        == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert selection["A_bridge_constraint_equation"] == "C_bridge^A = 0"
    assert selection["bridge_admissibility_constraint_form"] == "C_bridge^A = 0"
    assert selection["closed_A_ck_rule_family_count"] == 2
    assert selection["closed_A_ck_rule_roles"] == [
        "source admissibility",
        "bridge admissibility",
    ]
    assert selection["A_ck_source_bridge_rule_family_summary"][0]["rule_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert selection["A_ck_source_bridge_rule_family_summary"][1]["rule_form"] == (
        "C_bridge^A = 0"
    )
    assert selection["source_and_bridge_rules_retained_as_context"] is True
    assert selection["source_admissibility_rule_retained_as_context"] is True
    assert selection["bridge_admissibility_rule_retained_as_context"] is True
    assert selection["source_admissibility_family_reselected"] is False
    assert selection["bridge_admissibility_family_reselected"] is False


def test_a_source_bridge_selector_selects_transport_family_only() -> None:
    selection = _json(DEFAULT_OUT)
    assert selection["selected_A_ck_option_class"] == SELECTED_A_CK_OPTION_CLASS
    assert selection["selected_A_ck_constraint_family"] == (
        SELECTED_A_CK_CONSTRAINT_FAMILY
    )
    assert selection["selected_family_selection_status"] == (
        "selected_as_next_A_ck_family_after_source_and_bridge_admissibility"
    )
    assert selection["selector_target_prepared"] is True
    assert selection["selector_target_accepted"] is True
    assert selection["selection_executed"] is True
    assert selection["transport_consistency_family_selected"] is True
    assert selection["transport_consistency_recommended_only"] is False
    assert selection["transport_consistency_candidate_packet_authorized"] is True
    assert selection["transport_consistency_candidate_packet_prepared"] is False


def test_a_source_bridge_selector_records_transport_contract() -> None:
    selection = _json(DEFAULT_OUT)
    assert selection["transport_consistency_question"] == (
        TRANSPORT_CONSISTENCY_QUESTION
    )
    assert selection["transport_candidate_shape_preview"] == (
        TRANSPORT_CANDIDATE_SHAPE_PREVIEW
    )
    assert selection["transport_candidate_tuple_preview"] == (
        TRANSPORT_CANDIDATE_TUPLE_PREVIEW
    )
    assert selection["transport_tuple_components"] == TRANSPORT_TUPLE_COMPONENTS
    assert selection["transport_tuple_component_count"] == 5
    assert selection["transport_candidate_plain_meaning"] == (
        TRANSPORT_CANDIDATE_PLAIN_MEANING
    )
    assert selection["transport_chain_steps"] == TRANSPORT_CHAIN_STEPS
    assert selection["transport_chain_form"] == TRANSPORT_CHAIN_FORM
    assert selection["transport_chain_step_count"] == 5
    assert selection["transport_candidate_shape_preview_recorded"] is True
    assert selection["transport_candidate_tuple_preview_recorded"] is True
    assert selection["transport_chain_recorded"] is True
    assert selection["transport_candidate_constructed"] is False
    assert selection["transport_candidate_functional_defined"] is False
    assert selection["transport_consistency_proved"] is False
    assert selection["selection_criteria_count"] == 11
    assert selection["selection_criteria_accepted_count"] == 11
    assert {row["row_id"] for row in selection["selection_criteria"]} == {
        "selector_consumes_authorized_source_bridge_target",
        "bridge_closeout_accepted",
        "source_rule_retained",
        "bridge_rule_retained",
        "source_bridge_family_closed_but_not_promoted",
        "transport_consistency_family_selected",
        "transport_question_matches_A_derivation_chain",
        "transport_candidate_shape_only_previewed",
        "transport_tuple_preview_recorded_for_next_packet",
        "next_transport_candidate_packet_authorized",
        "no_transport_proof_action_variation_current_or_closure",
    }


def test_a_source_bridge_selector_records_family_options() -> None:
    selection = _json(DEFAULT_OUT)
    options = selection["candidate_family_options"]
    assert selection["candidate_family_option_count"] == 4
    assert [row["constraint_option_class"] for row in options] == [
        "source_admissibility_constraint",
        "bridge_admissibility_constraint",
        SELECTED_A_CK_OPTION_CLASS,
        "current_or_sourced_EM_constraint",
    ]
    assert options[0]["selection_status"] == (
        "closed_as_retained_context_not_reselected"
    )
    assert options[1]["selection_status"] == (
        "closed_as_retained_context_not_reselected"
    )
    assert options[2]["candidate_packet_target"] == NEXT_TARGET
    assert options[2]["transport_consistency_proved"] is False
    assert options[3]["J_nu_derived"] is False
    assert options[3]["sourced_maxwell_equation_derived"] is False
    assert options[3]["matter_current_exchange_route_proved"] is False
    assert options[3]["em_closure_claimed"] is False


def test_a_source_bridge_selector_blocks_shortcuts() -> None:
    selection = _json(DEFAULT_OUT)
    for key in [
        "transport_consistency_candidate_packet_prepared",
        "transport_candidate_constructed",
        "transport_candidate_functional_defined",
        "transport_candidate_functional_selected",
        "transport_proof_claimed",
        "transport_consistency_proved",
        "transport_chain_compatibility_proved",
        "residual_regime_route_proved",
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "candidate_action_insertion_executed",
        "constraint_as_action_term_selected",
        "constraint_term_selected",
        "ck_action_embedding_claimed",
        "ck_action_embedding_constructed",
        "C_k_action_embedding_constructed",
        "ck_variation_executed",
        "C_k_variation_executed",
        "lambda_variation_executed",
        "metric_variation_executed",
        "A_variation_executed",
        "new_conservation_proof_claimed",
        "source_admissibility_proved",
        "source_conservation_proved",
        "bridge_admissibility_proved",
        "bridge_route_alignment_verified",
        "route_consistency_tuple_proved",
        "current_route_derived",
        "current_source_route_constructed",
        "J_nu_derived",
        "psi_current_route_constructed",
        "external_current_native_derivation_selected",
        "matter_current_exchange_route_proved",
        "matter_gauge_energy_exchange_proved",
        "sourced_maxwell_equation_derived",
        "sourced_maxwell_closure_claimed",
        "sourced_maxwell_route_derived",
        "nonabelian_route_selected",
        "yang_mills_equations_derived",
        "field_equations_derived",
        "full_em_closure_claimed",
        "em_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "semiclassical_source_established",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "public_submission_authorized",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "canonical_master_action_promoted",
        "phase2_readiness_claim",
        "pillar_completion_inferred",
        "seam_closure_claim",
    ]:
        assert selection[key] is False, key
    for phrase in [
        "only chooses A_transport_consistency_constraint_family",
        "only as the next packet preview",
        "does not prepare the transport candidate packet",
        "does not define a concrete C_transport^A functional",
        "does not prove transport consistency",
        "does not execute C_k variation",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "does not promote the master action",
        "does not authorize Phase 2",
    ]:
        assert phrase in selection["non_claim_boundary"], phrase


def test_a_source_bridge_selector_validation_policy_not_run() -> None:
    selection = _json(DEFAULT_OUT)
    policy = selection["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_STATUS
    )
    assert policy["full_toeformal_aggregate_status_for_packet"] == (
        FULL_TOEFORMAL_STATUS
    )
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_source_bridge_selector_rotates_to_transport_candidate_packet() -> None:
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
        "ToeNativeACKConstraintFamilySelectionAfterSourceAndBridgeAdmissibility.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_AND_BRIDGE_"
        "ADMISSIBILITY_20260623_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["selection_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_A_ck_option_class"] == SELECTED_A_CK_OPTION_CLASS
    assert consumed["selected_A_ck_constraint_family"] == (
        SELECTED_A_CK_CONSTRAINT_FAMILY
    )
    assert consumed["transport_consistency_family_selected"] == "yes"
    assert consumed["transport_candidate_functional_defined"] == "no"
    assert consumed["transport_consistency_proved"] == "no"
    assert consumed["C_k_variation_executed"] == "no"
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
    assert active_row["selection_result"] == OUTCOME_ID
    assert active_row["transport_consistency_candidate_packet_authorized"] == "yes"
    assert active_row["transport_consistency_candidate_packet_prepared"] == "no"
    assert active_row["selected_A_ck_option_class"] == SELECTED_A_CK_OPTION_CLASS
    assert active_row["selected_A_ck_constraint_family"] == (
        SELECTED_A_CK_CONSTRAINT_FAMILY
    )
    assert active_row["transport_candidate_shape_preview"] == (
        TRANSPORT_CANDIDATE_SHAPE_PREVIEW
    )
    assert active_row["transport_candidate_tuple_preview"] == (
        TRANSPORT_CANDIDATE_TUPLE_PREVIEW
    )
    assert active_row["transport_candidate_functional_defined"] == "no"
    assert active_row["transport_consistency_proved"] == "no"
    assert active_row["C_k_variation_executed"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["full_em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_source_bridge_selector_mirrors() -> None:
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
        SELECTION_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "ToeNativeACKConstraintFamilySelectionAfterSourceAndBridgeAdmissibility",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_transport_consistency_ck_constraint_candidate_packet",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "select_next_toe_native_A_ck_constraint_family_after_source_and_bridge_admissibility",
        SELECTED_A_CK_OPTION_CLASS,
        SELECTED_A_CK_CONSTRAINT_FAMILY,
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "C_bridge^A = 0",
        TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
        TRANSPORT_CANDIDATE_TUPLE_PREVIEW,
        TRANSPORT_CHAIN_FORM,
        "does not define a concrete C_transport^A functional",
        "does not execute C_k variation",
        "does not prove transport consistency",
        "no QFT-GR closure",
        "NOT_RUN",
    ]:
        assert token in joined


def test_a_source_bridge_selector_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_ck_constraint_family_selection_after_source_and_bridge_admissibility_gate.py"
    )
