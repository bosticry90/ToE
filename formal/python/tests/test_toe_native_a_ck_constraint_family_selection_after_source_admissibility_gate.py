from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_ck_constraint_family_selection_after_source_admissibility_report import (
    A_ADDITIONAL_SOURCE_RULE_ELABORATION,
    A_ADDITIONAL_SOURCE_RULE_ELABORATION_STATUS,
    A_BRIDGE_CANDIDATE_PLAIN_MEANING,
    A_BRIDGE_CANDIDATE_SHAPE_PREVIEW,
    A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
    A_CURRENT_COUPLING_CONSTRAINT_FAMILY,
    A_CURRENT_COUPLING_FAMILY_STATUS,
    A_NONABELIAN_CONSTRAINT_FAMILY_DISPLAY,
    A_NONABELIAN_FAMILY_STATUS,
    A_TRANSPORT_CONSISTENCY_CONSTRAINT_FAMILY,
    A_TRANSPORT_CONSISTENCY_FAMILY_STATUS,
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
    PREVIOUS_A_CK_CONSTRAINT_FAMILY,
    PREVIOUS_A_CK_OPTION_CLASS,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS,
    SELECTION_RESULT,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    SOURCE_RULE_CLOSEOUT_PATH,
    build_toe_native_a_ck_constraint_family_selection_after_source_admissibility,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_ck_constraint_family_selection_after_source_admissibility_report.py"
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


def test_a_ck_family_selector_files_exist() -> None:
    for path in [
        SOURCE_RULE_CLOSEOUT_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_ck_family_selector_accepts_source_closeout() -> None:
    closeout = _json(SOURCE_RULE_CLOSEOUT_PATH)
    selection = _json(DEFAULT_OUT)
    assert closeout["outcome_id"] == SOURCE_RULE_CLOSEOUT_OUTCOME
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
        build_toe_native_a_ck_constraint_family_selection_after_source_admissibility()
        == selection
    )


def test_a_ck_family_selector_selects_bridge_family_only() -> None:
    selection = _json(DEFAULT_OUT)
    assert selection["source_selected_A_ck_option_class"] == PREVIOUS_A_CK_OPTION_CLASS
    assert (
        selection["source_selected_A_ck_constraint_family"]
        == PREVIOUS_A_CK_CONSTRAINT_FAMILY
    )
    assert selection["source_family_status"] == (
        "closed_as_vacuum_gauge_source_rule_reference_not_reselected"
    )
    assert selection["selected_A_ck_option_class"] == SELECTED_A_CK_OPTION_CLASS
    assert selection["selected_A_ck_constraint_family"] == SELECTED_A_CK_CONSTRAINT_FAMILY
    assert selection["selected_family_selection_status"] == (
        "selected_as_next_abstract_A_relevant_family"
    )
    assert selection["selector_target_prepared"] is True
    assert selection["selector_target_accepted"] is True
    assert selection["selection_executed"] is True
    assert selection["A_bridge_admissibility_family_selected"] is True
    assert selection["A_bridge_admissibility_recommended_only"] is False
    assert selection["A_bridge_admissibility_candidate_packet_authorized"] is True
    assert selection["A_bridge_admissibility_candidate_packet_prepared"] is False


def test_a_ck_family_selector_preserves_source_rule_context() -> None:
    selection = _json(DEFAULT_OUT)
    assert selection["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert selection["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert (
        selection["source_candidate_constraint_equation"]
        == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert (
        selection["source_admissibility_constraint_form"]
        == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert selection["gauge_group_policy"] == "U(1) / Abelian test route"
    assert selection["vacuum_euler_lagrange_route"] == "nabla_mu F^{mu nu} = 0"
    assert selection["on_shell_vacuum_conservation_identity"] == (
        "nabla_mu T_A^{mu nu} = 0"
    )
    assert selection["source_route_still_blocked"] == "nabla_mu F^{mu nu} = J^nu"
    assert selection["source_admissibility_family_reselected"] is False
    assert selection["source_admissibility_family_completed"] is False
    assert selection["source_rule_candidate_retained_as_context"] is True
    assert selection["source_rule_candidate_reopened"] is False


def test_a_ck_family_selector_records_five_family_comparison() -> None:
    selection = _json(DEFAULT_OUT)
    options = selection["candidate_family_options"]
    assert selection["candidate_family_option_count"] == 5
    assert [row["constraint_family_id"] for row in options] == [
        SELECTED_A_CK_CONSTRAINT_FAMILY,
        A_TRANSPORT_CONSISTENCY_CONSTRAINT_FAMILY,
        A_CURRENT_COUPLING_CONSTRAINT_FAMILY,
        "non_Abelian_A_constraint_family",
        A_ADDITIONAL_SOURCE_RULE_ELABORATION,
    ]
    assert options[0]["selection_status"] == (
        "selected_as_next_abstract_A_relevant_family"
    )
    assert options[1]["selection_status"] == A_TRANSPORT_CONSISTENCY_FAMILY_STATUS
    assert options[2]["selection_status"] == A_CURRENT_COUPLING_FAMILY_STATUS
    assert options[3]["constraint_family_display"] == A_NONABELIAN_CONSTRAINT_FAMILY_DISPLAY
    assert options[3]["selection_status"] == A_NONABELIAN_FAMILY_STATUS
    assert options[4]["selection_status"] == A_ADDITIONAL_SOURCE_RULE_ELABORATION_STATUS
    assert selection["A_transport_consistency_family_deferred"] is True
    assert selection["A_current_coupling_family_blocked_pending_J_nu_policy"] is True
    assert selection["nonabelian_A_family_deferred"] is True
    assert selection["additional_source_rule_elaboration_deferred"] is True


def test_a_ck_family_selector_records_next_bridge_packet_contract() -> None:
    selection = _json(DEFAULT_OUT)
    assert selection["A_bridge_candidate_shape_preview"] == A_BRIDGE_CANDIDATE_SHAPE_PREVIEW
    assert selection["A_bridge_candidate_plain_meaning"] == A_BRIDGE_CANDIDATE_PLAIN_MEANING
    assert selection["A_bridge_route_alignment_sequence"] == A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE
    assert selection["A_bridge_route_alignment_sequence_count"] == 7
    assert selection["A_bridge_candidate_shape_preview_recorded"] is True
    assert selection["A_bridge_candidate_constructed"] is False
    assert selection["bridge_C_k_candidate_constructed"] is False
    assert selection["A_bridge_route_alignment_sequence_recorded"] is True
    assert selection["A_bridge_route_alignment_verified"] is False
    assert selection["selection_criteria_count"] == 11
    assert selection["selection_criteria_accepted_count"] == 11
    assert {row["row_id"] for row in selection["selection_criteria"]} == {
        "selector_consumes_authorized_target",
        "source_admissibility_rule_closeout_accepted",
        "source_rule_context_retained_not_reselected",
        "bridge_family_selected_as_next_A_relevant_family",
        "transport_family_deferred_until_bridge_exists",
        "current_coupling_family_blocked_pending_J_nu_policy",
        "nonabelian_family_deferred_beyond_selected_U1",
        "additional_source_rule_elaboration_deferred_after_closeout",
        "bridge_candidate_shape_only_previewed",
        "next_candidate_packet_authorized",
        "no_candidate_action_variation_current_or_closure",
    }


def test_a_ck_family_selector_blocks_shortcuts() -> None:
    selection = _json(DEFAULT_OUT)
    for key in [
        "A_bridge_candidate_constructed",
        "bridge_C_k_candidate_constructed",
        "A_bridge_candidate_functional_defined",
        "A_bridge_candidate_functional_selected",
        "A_bridge_candidate_rule_proved",
        "A_bridge_route_alignment_verified",
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "candidate_action_insertion_executed",
        "ck_action_embedding_constructed",
        "C_k_action_embedding_constructed",
        "ck_variation_executed",
        "C_k_variation_executed",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "A_variation_of_candidate_executed",
        "constraint_multiplier_type_selected",
        "constraint_term_selected",
        "lambda_nu_domain_selected",
        "higher_derivative_scope_resolved",
        "boundary_terms_controlled",
        "new_conservation_proof_claimed",
        "new_source_admissibility_proof_claimed",
        "full_source_admissibility_review_accepted",
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
        "nonabelian_route_selected",
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
        assert selection[key] is False, key
    for phrase in [
        "only chooses the A bridge-admissibility C_k family",
        "does not construct C_bridge^A",
        "does not embed C_k in the action",
        "does not execute C_k variation",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "does not promote the master action",
    ]:
        assert phrase in selection["non_claim_boundary"], phrase


def test_a_ck_family_selector_validation_policy_not_run() -> None:
    selection = _json(DEFAULT_OUT)
    policy = selection["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == FULL_TOEFORMAL_STATUS
    assert policy["full_toeformal_aggregate_status_for_packet"] == FULL_TOEFORMAL_STATUS
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_ck_family_selector_rotates_to_bridge_candidate_packet() -> None:
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
        "ToeNativeACKConstraintFamilySelectionAfterSourceAdmissibility.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY_"
        "20260622_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["selection_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_A_ck_option_class"] == SELECTED_A_CK_OPTION_CLASS
    assert consumed["selected_A_ck_constraint_family"] == SELECTED_A_CK_CONSTRAINT_FAMILY
    assert consumed["A_bridge_admissibility_family_selected"] == "yes"
    assert consumed["bridge_C_k_candidate_constructed"] == "no"
    assert consumed["C_k_action_embedding_constructed"] == "no"
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
    assert active_row["selection_result"] == OUTCOME_ID
    assert active_row["A_bridge_admissibility_candidate_packet_authorized"] == "yes"
    assert active_row["A_bridge_admissibility_candidate_packet_prepared"] == "no"
    assert active_row["selected_A_ck_option_class"] == SELECTED_A_CK_OPTION_CLASS
    assert active_row["selected_A_ck_constraint_family"] == SELECTED_A_CK_CONSTRAINT_FAMILY
    assert active_row["A_bridge_candidate_shape_preview"] == A_BRIDGE_CANDIDATE_SHAPE_PREVIEW
    assert active_row["bridge_C_k_candidate_constructed"] == "no"
    assert active_row["C_k_action_embedding_constructed"] == "no"
    assert active_row["C_k_variation_executed"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_closure_claimed"] == "no"
    assert active_row["full_em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_ck_family_selector_mirrors() -> None:
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
        "ToeNativeACKConstraintFamilySelectionAfterSourceAdmissibility",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_bridge_admissibility_ck_constraint_candidate_packet",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "select_next_toe_native_A_ck_constraint_family_after_source_admissibility",
        SELECTED_A_CK_OPTION_CLASS,
        SELECTED_A_CK_CONSTRAINT_FAMILY,
        A_TRANSPORT_CONSISTENCY_FAMILY_STATUS,
        A_CURRENT_COUPLING_FAMILY_STATUS,
        A_NONABELIAN_CONSTRAINT_FAMILY_DISPLAY,
        A_ADDITIONAL_SOURCE_RULE_ELABORATION,
        A_BRIDGE_CANDIDATE_SHAPE_PREVIEW,
        "master-action A surface",
        "vacuum source-admissibility rule",
        "does not construct C_bridge^A",
        "does not execute C_k variation",
        "no bridge C_k candidate",
        "no QFT-GR closure",
        "NOT_RUN",
    ]:
        assert token in joined


def test_a_ck_family_selector_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_ck_constraint_family_selection_after_source_admissibility_gate.py"
    )
