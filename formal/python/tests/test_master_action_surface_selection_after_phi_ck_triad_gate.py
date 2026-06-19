from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.master_action_surface_selection_after_phi_ck_triad_report import (
    ALTERNATE_A_TARGET_NAME,
    ARTIFACT_ID,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_ROUTE_CHAIN_FORM,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PHI_CK_TRIAD_CLOSEOUT_OUTCOME,
    PHI_CK_TRIAD_CLOSEOUT_PATH,
    PHI_CK_TRIAD_CLOSEOUT_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_MASTER_ACTION_SURFACE,
    SELECTED_ROUTE_ID,
    SELECTED_ROUTE_LABEL,
    SELECTED_SURFACE_SYMBOL,
    SELECTION_RESULT,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SURFACE_SELECTOR_CANDIDATES,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    build_master_action_surface_selection_after_phi_ck_triad,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "master_action_surface_selection_after_phi_ck_triad_report.py"
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


def test_master_action_surface_selection_after_phi_ck_triad_files_exist() -> None:
    for path in [
        PHI_CK_TRIAD_CLOSEOUT_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_master_action_surface_selection_after_phi_ck_triad_selects_a_route() -> None:
    closeout = _json(PHI_CK_TRIAD_CLOSEOUT_PATH)
    selector = _json(DEFAULT_OUT)
    assert closeout["outcome_id"] == PHI_CK_TRIAD_CLOSEOUT_OUTCOME
    assert closeout["closeout_result"] == PHI_CK_TRIAD_CLOSEOUT_RESULT
    assert closeout["selected_next_target"] == CONSUMED_TARGET
    assert closeout["recommended_next_master_action_surface"] == (
        SELECTED_MASTER_ACTION_SURFACE
    )
    assert closeout["next_master_action_surface_selected"] is False

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
    assert selector["alternate_a_target_name"] == ALTERNATE_A_TARGET_NAME
    assert build_master_action_surface_selection_after_phi_ck_triad() == selector


def test_master_action_surface_selection_after_phi_ck_triad_preserves_context() -> None:
    selector = _json(DEFAULT_OUT)
    assert selector["phi_ck_triad_closeout_result"] == PHI_CK_TRIAD_CLOSEOUT_RESULT
    assert selector["phi_ck_triad_rule_forms"] == [
        "C_source^phi = 0",
        "C_bridge^phi = 0",
        "C_transport^phi = 0",
    ]
    assert selector["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert selector["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert selector["transport_admissibility_constraint_form"] == (
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert selector["phi_route_completed_admissibility_template"] is True
    assert selector["phi_ck_triad_reopened"] is False

    assert selector["surface_selector_candidates"] == SURFACE_SELECTOR_CANDIDATES
    assert selector["surface_option_count"] == 4
    assert selector["surface_options_selected_count"] == 1
    assert selector["surface_options_deferred_count"] == 3
    assert selector["selected_master_action_surface"] == SELECTED_MASTER_ACTION_SURFACE
    assert selector["selected_surface_symbol"] == SELECTED_SURFACE_SYMBOL
    assert selector["selected_route_id"] == SELECTED_ROUTE_ID
    assert selector["selected_route_label"] == SELECTED_ROUTE_LABEL
    assert selector["selected_route_status"] == "selected_for_packet_preparation"
    assert selector["selected_route_execution_status"] == "not_executed"
    assert selector["selected_route_packet_authorized"] is True
    assert selector["selected_route_execution_authorized"] is False
    assert selector["gauge_route_chain_form"] == GAUGE_ROUTE_CHAIN_FORM
    assert selector["gauge_route_chain_step_count"] == 6


def test_master_action_surface_selection_after_phi_ck_triad_blocks_claims() -> None:
    selector = _json(DEFAULT_OUT)
    assert selector["selection_criteria_count"] == 10
    assert selector["selection_criteria_accepted_count"] == 10
    for key in [
        "selector_target_prepared",
        "selector_target_accepted",
        "selection_executed",
        "master_action_surface_selection_executed",
        "a_surface_gauge_route_selected",
        "a_surface_gauge_route_packet_authorized",
        "psi_surface_deferred_as_harder",
        "rho_surface_deferred_as_more_speculative",
        "further_phi_ck_elaboration_deferred",
        "more_ck_elaboration_deferred",
    ]:
        assert selector[key] is True, key
    for key in [
        "a_surface_gauge_route_packet_prepared",
        "a_surface_gauge_route_execution_authorized",
        "a_surface_variation_executed",
        "a_surface_variation_route_prepared",
        "a_surface_variation_route_executed",
        "gauge_field_derived",
        "gauge_surface_derived",
        "maxwell_equations_derived",
        "yang_mills_equations_derived",
        "field_equations_derived",
        "current_source_route_constructed",
        "current_conservation_proved",
        "gauge_current_constraint_proved",
        "stress_energy_route_constructed",
        "stress_energy_source_admissibility_proved",
        "new_ck_rules_constructed",
        "source_bridge_transport_ck_analogues_constructed",
        "ck_action_embedding_claimed",
        "ck_variation_executed",
        "ck_variation_authorized",
        "native_phi_derivation_claimed",
        "v_phi_derivation_claimed",
        "qft_gr_closure_claimed",
        "qft_gr_solved",
        "qft_gr_seam_closed",
        "em_closure_claimed",
        "em_qft_closure_claimed",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "toe_native_matter_derivation_claimed",
        "standard_model_derivation_claimed",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "public_submission_authorized",
        "canonical_master_action_promoted",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "phase2_readiness_claim",
        "pillar_completion_inferred",
        "seam_closure_claim",
    ]:
        assert selector[key] is False, key
    for phrase in [
        "A_surface_gauge_route as selected",
        "next preparation packet only",
        "closed admissibility-rule template",
        "does not reopen the phi/C_k triad",
        "does not execute A variation",
        "does not derive a gauge field",
        "does not derive Maxwell equations",
        "does not derive Yang-Mills equations",
        "does not prove current conservation",
        "does not construct new C_k rules",
        "does not close QFT-GR",
        "does not close EM",
        "does not promote the master action",
    ]:
        assert phrase in selector["non_claim_boundary"], phrase


def test_master_action_surface_selection_after_phi_ck_triad_validation_policy() -> None:
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
    assert selector["full_toeformal_aggregate_failed"] is False
    assert selector["full_toeformal_aggregate_timed_out"] is False


def test_master_action_surface_selection_after_phi_ck_triad_rotates_to_a_packet() -> None:
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
        "MasterActionSurfaceSelectionAfterPhiCKTriad.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "MASTER_ACTION_SURFACE_SELECTION_AFTER_PHI_CK_TRIAD_20260619_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["selection_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_master_action_surface"] == SELECTED_MASTER_ACTION_SURFACE
    assert consumed["selected_route_execution_authorized"] == "no"
    assert consumed["a_surface_variation_executed"] == "no"
    assert consumed["gauge_field_derived"] == "no"
    assert consumed["maxwell_equations_derived"] == "no"
    assert consumed["current_conservation_proved"] == "no"
    assert consumed["new_ck_rules_constructed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["em_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["selection_result"] == OUTCOME_ID
    assert active_row["packet_result"] == "PENDING"
    assert active_row["selected_master_action_surface"] == SELECTED_MASTER_ACTION_SURFACE
    assert active_row["selected_route_target"] == NEXT_TARGET
    assert active_row["a_surface_gauge_route_selected"] == "yes"
    assert active_row["a_surface_gauge_route_packet_authorized"] == "yes"
    assert active_row["a_surface_gauge_route_packet_prepared"] == "no"
    assert active_row["selected_route_execution_authorized"] == "no"
    assert active_row["a_surface_variation_executed"] == "no"
    assert active_row["gauge_field_derived"] == "no"
    assert active_row["current_conservation_proved"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["em_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_master_action_surface_selection_after_phi_ck_triad_mirrors() -> None:
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
        SELECTED_MASTER_ACTION_SURFACE,
        SELECTED_ROUTE_ID,
        "MasterActionSurfaceSelectionAfterPhiCKTriad",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_toe_native_A_surface_variation_and_source_route_packet",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: select_next_master_action_surface_after_phi_ck_triad",
        "ACTIVE_LANE_v0: prepare_toe_native_A_surface_variation_and_source_route_packet",
        "A_surface_gauge_route",
        "psi_surface_fermion_matter_route",
        "rho_surface_statistical_entropy_route",
        "ck_further_constraint_family_elaboration",
        "does not execute A variation",
        "does not derive Maxwell",
        "does not prove current conservation",
        "does not construct new C_k rules",
        "no QFT-GR closure",
        "no EM closure",
        "no canonical master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_master_action_surface_selection_after_phi_ck_triad_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_master_action_surface_selection_after_phi_ck_triad_gate.py"
    )
