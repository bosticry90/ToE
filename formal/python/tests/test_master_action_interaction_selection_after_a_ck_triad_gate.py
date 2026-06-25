from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.master_action_interaction_selection_after_a_ck_triad_report import (
    A_CK_TRIAD_CLOSEOUT_OUTCOME,
    A_CK_TRIAD_CLOSEOUT_PATH,
    A_CK_TRIAD_CLOSEOUT_RESULT,
    ARTIFACT_ID,
    BLOCKED_CLAIMS,
    C_EXCHANGE_CANDIDATE_PREVIEW,
    CONSUMED_TARGET,
    CURRENT_CANDIDATE_PREVIEW,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_EQUATION_SHAPE_PREVIEW,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    POLICY_PACKET_REQUIRED_PINS,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_GAUGE_GROUP,
    SELECTED_INTERACTION_FIELDS,
    SELECTED_INTERACTION_ROUTE,
    SELECTED_MATTER_TYPE_SCOPE,
    SELECTED_ROUTE_LABEL,
    SELECTION_RESULT,
    SOURCED_GAUGE_EQUATION_PREVIEW,
    TOTAL_EXCHANGE_PREVIEW,
    build_master_action_interaction_selection_after_a_ck_triad,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "master_action_interaction_selection_after_a_ck_triad_report.py"
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


def test_master_action_interaction_selection_after_a_ck_triad_files_exist() -> None:
    for path in [
        A_CK_TRIAD_CLOSEOUT_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_master_action_interaction_selection_after_a_ck_triad_selects_psi_a_route() -> None:
    closeout = _json(A_CK_TRIAD_CLOSEOUT_PATH)
    selector = _json(DEFAULT_OUT)
    assert closeout["outcome_id"] == A_CK_TRIAD_CLOSEOUT_OUTCOME
    assert closeout["closeout_result"] == A_CK_TRIAD_CLOSEOUT_RESULT
    assert closeout["selected_next_target"] == CONSUMED_TARGET
    assert closeout["recommended_interaction_route"] == SELECTED_INTERACTION_ROUTE
    assert closeout["psi_A_current_exchange_route_selected"] is False

    assert selector["artifact_id"] == ARTIFACT_ID
    assert selector["schema_id"] == SCHEMA_ID
    assert selector["packet_id"] == PACKET_ID
    assert selector["prepared"] is True
    assert selector["accepted"] is True
    assert selector["outcome_id"] == OUTCOME_ID
    assert selector["selection_result"] == SELECTION_RESULT
    assert selector["route_selection_result"] == SELECTION_RESULT
    assert selector["packet_classification"] == PACKET_CLASSIFICATION
    assert selector["consumed_target"] == CONSUMED_TARGET
    assert selector["selected_next_target"] == NEXT_TARGET
    assert selector["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_master_action_interaction_selection_after_a_ck_triad() == selector


def test_master_action_interaction_selection_after_a_ck_triad_records_policy_inputs() -> None:
    selector = _json(DEFAULT_OUT)
    assert selector["a_ck_triad_closeout_result"] == A_CK_TRIAD_CLOSEOUT_RESULT
    assert selector["a_ck_triad_scope"] == "vacuum U(1)"
    assert selector["a_ck_triad_rule_forms"] == [
        "C_source^A = 0",
        "C_bridge^A = 0",
        "C_transport^A = 0",
    ]
    assert selector["a_ck_triad_reopened"] is False
    assert selector["phi_ck_triad_reopened"] is False
    assert selector["source_bridge_transport_pattern_reuse_result"] == (
        "architectural_reuse_witness_for_isolated_phi_and_vacuum_A"
    )
    assert selector["architectural_result_not_new_law_of_nature"] is True

    assert selector["selected_interaction_route"] == SELECTED_INTERACTION_ROUTE
    assert selector["selected_route_label"] == SELECTED_ROUTE_LABEL
    assert selector["selected_interaction_fields"] == SELECTED_INTERACTION_FIELDS
    assert selector["selected_matter_type_scope"] == SELECTED_MATTER_TYPE_SCOPE
    assert selector["selected_gauge_group"] == SELECTED_GAUGE_GROUP
    assert selector["selected_route_status"] == "selected_for_policy_packet_preparation"
    assert selector["selected_route_execution_status"] == "not_executed"
    assert selector["selected_route_packet_authorized"] is True
    assert selector["selected_route_execution_authorized"] is False

    assert selector["current_candidate_preview"] == CURRENT_CANDIDATE_PREVIEW
    assert selector["matter_equation_shape_preview"] == MATTER_EQUATION_SHAPE_PREVIEW
    assert selector["sourced_gauge_equation_preview"] == SOURCED_GAUGE_EQUATION_PREVIEW
    assert selector["total_exchange_preview"] == TOTAL_EXCHANGE_PREVIEW
    assert selector["c_exchange_candidate_preview"] == C_EXCHANGE_CANDIDATE_PREVIEW
    assert selector["c_exchange_functional_defined"] is False
    assert selector["c_exchange_rule_proved"] is False
    assert selector["policy_packet_required_pins"] == POLICY_PACKET_REQUIRED_PINS
    assert selector["blocked_claims"] == BLOCKED_CLAIMS


def test_master_action_interaction_selection_after_a_ck_triad_blocks_claims() -> None:
    selector = _json(DEFAULT_OUT)
    assert selector["selection_criteria_count"] == 10
    assert selector["selection_criteria_accepted_count"] == 10
    for key in [
        "selector_target_prepared",
        "selector_target_accepted",
        "selection_executed",
        "master_action_interaction_selection_executed",
        "psi_A_u1_current_and_exchange_route_selected",
        "psi_A_u1_policy_packet_preparation_selected",
        "policy_packet_preparation_authorized",
        "c_exchange_rule_family_introduced_as_likely_policy_target",
        "separate_sector_exchange_visible",
        "total_conservation_policy_required",
        "illegal_loss_vs_legal_transfer_distinction_required",
    ]:
        assert selector[key] is True, key
    for key in [
        "psi_A_u1_policy_packet_prepared",
        "current_route_derived",
        "matter_current_J_nu_derived",
        "J_nu_derived",
        "current_conservation_proved",
        "sourced_maxwell_equation_derived",
        "dirac_equation_derived",
        "matter_gauge_exchange_proved",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "quantized_electromagnetism_claimed",
        "anomaly_cancellation_claimed",
        "standard_model_derivation_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
    ]:
        assert selector[key] is False, key
    for phrase in [
        "selected for policy-packet preparation only",
        "does not derive J^nu",
        "does not prove current conservation",
        "does not derive sourced Maxwell",
        "does not derive the Dirac equation",
        "does not prove matter-gauge exchange",
        "does not close EM-QFT",
        "does not close QFT-GR",
        "does not authorize Phase 2",
        "does not promote the master action",
    ]:
        assert phrase in selector["non_claim_boundary"], phrase


def test_master_action_interaction_selection_after_a_ck_triad_validation_policy() -> None:
    selector = _json(DEFAULT_OUT)
    policy = selector["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["aggregate_lean_validation_status_allowed_values"] == ["NOT_RUN"]
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert selector["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert selector["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert selector["full_toeformal_aggregate_passed"] is False


def test_master_action_interaction_selection_after_a_ck_triad_rotates_to_policy_packet() -> None:
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
        "MasterActionInteractionSelectionAfterACKTriad.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "MASTER_ACTION_INTERACTION_SELECTION_AFTER_A_CK_TRIAD_20260624_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["selection_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_interaction_route"] == SELECTED_INTERACTION_ROUTE
    assert consumed["policy_packet_preparation_authorized"] == "yes"
    assert consumed["psi_A_u1_policy_packet_prepared"] == "no"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["sourced_maxwell_equation_derived"] == "no"
    assert consumed["matter_gauge_exchange_proved"] == "no"
    assert consumed["em_qft_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["selection_result"] == OUTCOME_ID
    assert active_row["packet_result"] == "PENDING"
    assert active_row["policy_packet_result"] == "PENDING"
    assert active_row["selected_interaction_route"] == SELECTED_INTERACTION_ROUTE
    assert active_row["policy_packet_target"] == NEXT_TARGET
    assert active_row["policy_packet_preparation_authorized"] == "yes"
    assert active_row["psi_A_u1_policy_packet_prepared"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["matter_gauge_exchange_proved"] == "no"
    assert active_row["em_qft_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_master_action_interaction_selection_after_a_ck_triad_mirrors() -> None:
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
        SELECTED_INTERACTION_ROUTE,
        SELECTED_ROUTE_LABEL,
        "MasterActionInteractionSelectionAfterACKTriad",
        (
            "CURRENT_LIVE_NEXT_TARGET_v0: "
            "prepare_toe_native_psi_A_u1_current_derivation_from_A_variation_packet"
        ),
        (
            "PREVIOUS_LIVE_NEXT_TARGET_v0: "
            "review_toe_native_psi_A_u1_interaction_action_block_definition_packet_result"
        ),
        (
            "ACTIVE_LANE_v0: "
            "prepare_toe_native_psi_A_u1_current_derivation_from_A_variation_packet"
        ),
        CURRENT_CANDIDATE_PREVIEW,
        TOTAL_EXCHANGE_PREVIEW,
        C_EXCHANGE_CANDIDATE_PREVIEW,
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not prove matter-gauge exchange",
        "does not close EM-QFT",
        "does not close QFT-GR",
        "does not promote the master action",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_master_action_interaction_selection_after_a_ck_triad_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_master_action_interaction_selection_after_a_ck_triad_gate.py"
    )
