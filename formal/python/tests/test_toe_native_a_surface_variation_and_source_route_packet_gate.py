from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.master_action_surface_selection_after_phi_ck_triad_report import (
    DEFAULT_OUT as SURFACE_SELECTION_PATH,
    OUTCOME_ID as SURFACE_SELECTION_OUTCOME,
)
from formal.python.tools.toe_native_a_surface_variation_and_source_route_packet_report import (
    A_SURFACE_ROUTE_PACKET_RESULT,
    ARTIFACT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    GAUGE_ROUTE_STATUS_DECISION,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MASTER_A_LAGRANGIAN,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    RAW_GAUGE_ROUTE,
    RAW_VARIATION_ROUTE,
    SCHEMA_ID,
    SELECTED_MASTER_ACTION_SURFACE,
    SELECTED_ROUTE_ID,
    SELECTED_SURFACE_SYMBOL,
    SOURCE_FORM_ROUTE_SHAPE,
    SOURCE_FORM_ROUTE_STATUS,
    TOE_NATIVE_STATUS_DECISION,
    build_toe_native_a_surface_variation_and_source_route_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_surface_variation_and_source_route_packet_report.py"
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
QFTGR_AGGREGATE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
CURRENT_AUTHORITY_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
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


def test_a_surface_packet_files_exist() -> None:
    for path in [
        SURFACE_SELECTION_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_surface_packet_records_raw_route_and_blocks_source_derivation() -> None:
    surface_selection = _json(SURFACE_SELECTION_PATH)
    packet = _json(DEFAULT_OUT)
    assert surface_selection["outcome_id"] == SURFACE_SELECTION_OUTCOME
    assert surface_selection["selected_next_target"] == CONSUMED_TARGET
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["a_surface_route_packet_result"] == A_SURFACE_ROUTE_PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selected_master_action_surface"] == SELECTED_MASTER_ACTION_SURFACE
    assert packet["selected_surface_symbol"] == SELECTED_SURFACE_SYMBOL
    assert packet["selected_route_id"] == SELECTED_ROUTE_ID
    assert packet["master_A_lagrangian"] == MASTER_A_LAGRANGIAN
    assert packet["raw_gauge_route"] == RAW_GAUGE_ROUTE
    assert packet["raw_variation_route"] == RAW_VARIATION_ROUTE
    assert packet["source_form_route_shape"] == SOURCE_FORM_ROUTE_SHAPE
    assert packet["source_form_route_status"] == SOURCE_FORM_ROUTE_STATUS
    assert packet["gauge_route_status_decision"] == GAUGE_ROUTE_STATUS_DECISION
    assert packet["toe_native_status_decision"] == TOE_NATIVE_STATUS_DECISION
    assert build_toe_native_a_surface_variation_and_source_route_packet() == packet


def test_a_surface_packet_answers_required_questions() -> None:
    packet = _json(DEFAULT_OUT)
    questions = {row["question_id"]: row for row in packet["route_questions"]}
    assert list(questions) == [
        "q1_master_action_gauge_term_defined",
        "q2_raw_gauge_route",
        "q3_raw_variation_route",
        "q4_source_form_route",
        "q5_current_domain",
        "q6_ck_analogues",
        "q7_remaining_unproved",
    ]
    assert packet["route_question_count"] == 7
    assert questions["q1_master_action_gauge_term_defined"]["status"] == "surface_indexed"
    assert questions["q2_raw_gauge_route"]["answer"] == RAW_GAUGE_ROUTE
    assert questions["q3_raw_variation_route"]["answer"] == RAW_VARIATION_ROUTE
    assert questions["q4_source_form_route"]["status"] == "route_shape_only_not_derived"
    assert questions["q5_current_domain"]["status"] == "blocked_pending_current_policy"
    assert questions["q6_ck_analogues"]["status"] == "blocked_pending_C_k_analogues"
    assert questions["q7_remaining_unproved"]["status"] == "retained_blockers"


def test_a_surface_packet_retains_expected_blockers_and_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["retained_blocker_count"] == 15
    assert {row["blocker_id"] for row in packet["retained_blockers"]} == {
        "gauge_group_not_selected",
        "bundle_domain_for_A_not_selected",
        "definition_of_F_not_selected",
        "covariant_derivative_D_mu_convention_not_selected",
        "matter_current_J_nu_not_derived",
        "external_current_policy_not_selected",
        "gauge_fixing_not_selected",
        "boundary_terms_not_controlled",
        "stress_energy_T_A_not_derived",
        "source_admissibility_not_proved",
        "current_conservation_not_proved",
        "C_k_analogues_not_constructed",
        "EM_closure_not_claimed",
        "QFT_GR_closure_not_claimed",
        "master_action_promotion_not_claimed",
    }
    for key in [
        "a_surface_variation_route_prepared",
        "a_surface_indexed",
        "raw_gauge_variation_formula_recorded",
        "raw_A_to_F_route_recorded",
        "raw_variation_shape_recorded",
        "source_route_shape_recorded",
        "source_route_shape_only_not_derived",
        "symbolic_calculation_recorded",
    ]:
        assert packet[key] is True, key
    for key in [
        "formal_theorem_backed_gauge_derivation",
        "a_surface_variation_executed",
        "a_surface_variation_route_executed",
        "gauge_group_selected",
        "bundle_domain_for_A_selected",
        "definition_of_F_selected",
        "covariant_derivative_D_mu_convention_selected",
        "matter_current_J_nu_derived",
        "external_current_policy_selected",
        "gauge_fixing_selected",
        "boundary_terms_controlled",
        "stress_energy_T_A_derived",
        "source_admissibility_proved",
        "current_conservation_proved",
        "gauge_current_constraint_proved",
        "C_k_analogues_constructed",
        "source_bridge_transport_ck_analogues_constructed",
        "maxwell_equations_derived",
        "yang_mills_equations_derived",
        "field_equations_derived",
        "gauge_field_derived",
        "current_source_route_constructed",
        "stress_energy_route_constructed",
        "stress_energy_source_admissibility_proved",
        "toe_native_gauge_derivation_claimed",
        "toe_native_A_source_route_constructed",
        "toe_native_A_source_admissibility_claimed",
        "toe_native_A_current_conservation_claimed",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "source_map_closed",
        "qft_gr_solved",
        "qft_gr_closure_claimed",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_authorized",
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
        assert packet[key] is False, key
    assert "does not select a gauge group" in packet["non_claim_boundary"]
    assert "does not derive Maxwell or Yang-Mills equations" in packet["non_claim_boundary"]


def test_a_surface_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_surface_packet_rotates_live_target_to_result_review() -> None:
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
        "ToeNativeASurfaceVariationAndSourceRoutePacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_20260621_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["a_surface_route_packet_result"] == A_SURFACE_ROUTE_PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["a_surface_variation_route_prepared"] == "yes"
    assert consumed["source_route_shape_only_not_derived"] == "yes"
    assert consumed["gauge_group_selected"] == "no"
    assert consumed["matter_current_J_nu_derived"] == "no"
    assert consumed["current_conservation_proved"] == "no"
    assert consumed["C_k_analogues_constructed"] == "no"
    assert consumed["em_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["a_surface_route_packet_result"] == A_SURFACE_ROUTE_PACKET_RESULT
    assert active_row["selected_surface_symbol"] == "A"
    assert active_row["selected_route_id"] == SELECTED_ROUTE_ID
    assert active_row["a_surface_variation_route_prepared"] == "yes"
    assert active_row["source_route_shape_only_not_derived"] == "yes"
    assert active_row["em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_surface_packet_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_AGGREGATE_PATH,
            CURRENT_TARGET_AGGREGATE_PATH,
            CURRENT_AUTHORITY_AGGREGATE_PATH,
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
        A_SURFACE_ROUTE_PACKET_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        SELECTED_ROUTE_ID,
        "ToeNativeASurfaceVariationAndSourceRoutePacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: review_toe_native_A_surface_variation_and_source_route_result",
        "raw gauge variation/source-route shape",
        "route shape only, not as a derivation",
        "does not select a gauge group",
        "does not derive J^nu",
        "does not prove source admissibility or current conservation",
        "does not construct C_k analogues",
        "does not derive Maxwell or Yang-Mills equations",
        "does not close EM, QFT-GR, or EM-QFT",
        "does not promote the master action",
    ]:
        assert token in joined


def test_a_surface_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_surface_variation_and_source_route_packet_gate.py"
    )
