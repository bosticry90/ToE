from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_gauge_group_domain_and_current_policy_packet_report import (
    DEFAULT_OUT as A_GAUGE_POLICY_PACKET_PATH,
    OUTCOME_ID as A_GAUGE_POLICY_PACKET_OUTCOME,
)
from formal.python.tools.toe_native_a_vacuum_variation_retry_under_selected_u1_policy_packet_report import (
    A_VACUUM_VARIATION_RETRY_RESULT,
    ACTION_VARIATION_FORM,
    ARTIFACT_ID,
    BOUNDARY_POLICY_USED,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    DELTA_F_FORM,
    F_DEFINITION_POLICY,
    GAUGE_GROUP_POLICY,
    INTEGRATION_BY_PARTS_FORM,
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
    SELECTED_A_ACTION,
    VACUUM_EULER_LAGRANGE_ROUTE,
    build_toe_native_a_vacuum_variation_retry_under_selected_u1_policy_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_vacuum_variation_retry_under_selected_u1_policy_packet_report.py"
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
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
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


def test_a_vacuum_variation_retry_packet_files_exist() -> None:
    for path in [
        A_GAUGE_POLICY_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_vacuum_variation_retry_packet_constructs_vacuum_route_only() -> None:
    policy = _json(A_GAUGE_POLICY_PACKET_PATH)
    packet = _json(DEFAULT_OUT)
    assert policy["outcome_id"] == A_GAUGE_POLICY_PACKET_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["a_vacuum_variation_retry_result"] == A_VACUUM_VARIATION_RETRY_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["gauge_group_policy"] == GAUGE_GROUP_POLICY
    assert packet["F_definition_policy"] == F_DEFINITION_POLICY
    assert packet["selected_A_action"] == SELECTED_A_ACTION
    assert packet["delta_F_form"] == DELTA_F_FORM
    assert packet["action_variation_form"] == ACTION_VARIATION_FORM
    assert packet["integration_by_parts_form"] == INTEGRATION_BY_PARTS_FORM
    assert packet["boundary_policy_used"] == BOUNDARY_POLICY_USED
    assert packet["vacuum_euler_lagrange_route"] == VACUUM_EULER_LAGRANGE_ROUTE
    assert build_toe_native_a_vacuum_variation_retry_under_selected_u1_policy_packet() == packet


def test_a_vacuum_variation_retry_packet_retains_expected_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["calculation_step_count"] == 8
    assert packet["review_criteria_count"] == 12
    assert packet["review_criteria_accepted_count"] == 12
    assert [row["step_id"] for row in packet["calculation_steps"]] == [
        "state_selected_u1_action",
        "state_selected_u1_policy",
        "vary_F",
        "vary_action",
        "integrate_by_parts",
        "apply_boundary_policy",
        "read_vacuum_route",
        "retain_current_and_closure_blockers",
    ]
    for key in [
        "u1_policy_used",
        "minimal_abelian_route_selected",
        "A_as_smooth_real_one_form_selected",
        "F_definition_used",
        "delta_F_recorded",
        "action_variation_computed",
        "integration_by_parts_computed",
        "boundary_policy_used_for_variation",
        "boundary_terms_vanish_by_selected_policy",
        "boundary_terms_controlled",
        "vacuum_gauge_variation_route_constructed",
        "vacuum_u1_variation_route_constructed",
        "vacuum_euler_lagrange_route_constructed",
        "vacuum_route_recorded",
        "source_current_route_still_blocked",
        "current_derivation_blocked",
        "psi_derived_current_deferred",
        "external_current_not_selected_as_native_derivation",
        "symbolic_calculation_recorded",
        "a_surface_variation_executed",
        "a_surface_variation_route_executed",
    ]:
        assert packet[key] is True, key
    for key in [
        "current_route_derived",
        "current_source_route_constructed",
        "matter_current_J_nu_derived",
        "psi_derived_current",
        "external_current_policy_selected",
        "nonabelian_route_selected",
        "gauge_fixing_selected_as_physical_structure",
        "stress_energy_T_A_derived",
        "current_conservation_proved",
        "A_source_admissibility_proved",
        "A_relevant_C_k_rules_constructed",
        "em_closure_claimed",
        "qft_gr_closure_claimed",
        "canonical_master_action_promoted",
        "master_action_promoted",
        "empirical_validation_claimed",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "constructs the vacuum U(1) gauge variation route only",
        "does not derive J^nu",
        "does not derive a psi-current",
        "does not select an external current as native derivation",
        "does not select a non-Abelian route",
        "does not select gauge fixing as physical structure",
        "does not derive stress-energy T_A",
        "does not prove current conservation",
        "does not prove source admissibility",
        "does not construct A-relevant C_k rules",
        "does not close EM",
        "does not close QFT-GR",
        "does not promote the master action",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_a_vacuum_variation_retry_packet_rotates_live_target_to_result_review() -> None:
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
        "ToeNativeAVacuumVariationRetryUnderSelectedU1PolicyPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_PACKET_20260621_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["a_vacuum_variation_retry_result"] == A_VACUUM_VARIATION_RETRY_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["vacuum_euler_lagrange_route"] == VACUUM_EULER_LAGRANGE_ROUTE
    assert consumed["current_route_derived"] == "no"
    assert consumed["stress_energy_T_A_derived"] == "no"
    assert consumed["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed["em_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["vacuum_gauge_variation_route_constructed"] == "yes"
    assert active_row["source_current_route_still_blocked"] == "yes"
    assert active_row["current_route_derived"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_vacuum_variation_retry_packet_lean_and_surface_mirrors() -> None:
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
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "ToeNativeAVacuumVariationRetryUnderSelectedU1PolicyPacket",
        "HISTORICAL_TOE_NATIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_PACKET_CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_vacuum_variation_retry_under_selected_u1_policy",
        "HISTORICAL_TOE_NATIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_RESULT_REVIEW_CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_A_vacuum_variation_retry_under_selected_u1_policy_result",
        "nabla_mu F^{mu nu} = 0",
        "delta F_{mu nu}",
        "compact-support or fixed-boundary variation",
        "nabla_mu F^{mu nu} = J^nu remains route shape only",
        "A-relevant C_k",
        "does not close QFT-GR",
        "master-action promotion remain blocked",
    ]:
        assert token in joined


def test_a_vacuum_variation_retry_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_vacuum_variation_retry_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_vacuum_variation_retry_under_selected_u1_policy_packet_gate.py"
    )
