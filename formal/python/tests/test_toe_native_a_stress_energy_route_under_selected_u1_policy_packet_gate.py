from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_route_selection_after_vacuum_u1_variation_report import (
    DEFAULT_OUT as A_ROUTE_SELECTOR_PATH,
    OUTCOME_ID as A_ROUTE_SELECTOR_OUTCOME,
)
from formal.python.tools.toe_native_a_stress_energy_route_under_selected_u1_policy_packet_report import (
    A_STRESS_ENERGY_ROUTE_RESULT,
    ARTIFACT_ID,
    CONSUMED_TARGET,
    CONVENTION_SCOPE,
    DEFAULT_OUT,
    F_CONTRACTION_VARIATION_ROUTE,
    F_DEFINITION_POLICY,
    GAUGE_GROUP_POLICY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    METRIC_SIGNATURE_POLICY,
    METRIC_VARIATION_CONVENTION,
    METRIC_VARIATION_FORM,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_A_STRESS_ENERGY_ACTION,
    SOURCE_ROUTE_STILL_BLOCKED,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
    VOLUME_VARIATION_ROUTE,
    build_toe_native_a_stress_energy_route_under_selected_u1_policy_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_stress_energy_route_under_selected_u1_policy_packet_report.py"
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


def test_a_stress_energy_route_packet_files_exist() -> None:
    for path in [
        A_ROUTE_SELECTOR_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_stress_energy_route_packet_records_expected_route() -> None:
    selector = _json(A_ROUTE_SELECTOR_PATH)
    packet = _json(DEFAULT_OUT)
    assert selector["outcome_id"] == A_ROUTE_SELECTOR_OUTCOME
    assert selector["selected_next_target"] == CONSUMED_TARGET
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["a_stress_energy_route_result"] == A_STRESS_ENERGY_ROUTE_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["gauge_group_policy"] == GAUGE_GROUP_POLICY
    assert packet["F_definition_policy"] == F_DEFINITION_POLICY
    assert packet["metric_signature_policy"] == METRIC_SIGNATURE_POLICY
    assert packet["selected_A_stress_energy_action"] == SELECTED_A_STRESS_ENERGY_ACTION
    assert packet["metric_variation_convention"] == METRIC_VARIATION_CONVENTION
    assert packet["volume_variation_route"] == VOLUME_VARIATION_ROUTE
    assert packet["F_contraction_variation_route"] == F_CONTRACTION_VARIATION_ROUTE
    assert packet["metric_variation_form"] == METRIC_VARIATION_FORM
    assert (
        packet["stress_energy_under_selected_u1_policy"]
        == STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
    )
    assert packet["convention_scope"] == CONVENTION_SCOPE
    assert packet["vacuum_euler_lagrange_route"] == VACUUM_EULER_LAGRANGE_ROUTE
    assert packet["source_route_still_blocked"] == SOURCE_ROUTE_STILL_BLOCKED
    assert build_toe_native_a_stress_energy_route_under_selected_u1_policy_packet() == packet


def test_a_stress_energy_route_packet_retains_expected_boundaries() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["calculation_step_count"] == 9
    assert packet["review_criteria_count"] == 12
    assert packet["review_criteria_accepted_count"] == 12
    assert [row["step_id"] for row in packet["calculation_steps"]] == [
        "state_selected_u1_gauge_action",
        "preserve_selected_u1_policy",
        "state_metric_variation_convention",
        "vary_volume_form",
        "vary_raised_F_contraction",
        "read_metric_variation_form",
        "record_gauge_stress_energy_route",
        "record_convention_scope",
        "retain_current_ck_closure_blockers",
    ]
    for key in [
        "u1_policy_used",
        "minimal_abelian_route_selected",
        "A_as_smooth_real_one_form_selected",
        "F_definition_used",
        "metric_signature_policy_used",
        "metric_variation_convention_recorded",
        "metric_variation_computed",
        "metric_variation_route_recorded",
        "stress_energy_route_recorded",
        "gauge_stress_energy_route_recorded",
        "stress_energy_T_A_recorded",
        "stress_energy_T_A_derived",
        "stress_energy_derivation_executed",
        "stress_energy_route_constructed",
        "stress_energy_route_convention_sensitive",
        "stress_energy_sign_convention_verified_explicitly",
        "symbolic_calculation_recorded",
    ]:
        assert packet[key] is True, key
    for key in [
        "stress_energy_source_admissibility_proved",
        "stress_energy_as_gravity_source_authorized",
        "current_route_derived",
        "matter_current_J_nu_derived",
        "J_nu_derived",
        "psi_current_route_constructed",
        "external_current_policy_selected",
        "external_current_native_derivation_selected",
        "current_conservation_proved",
        "A_source_admissibility_proved",
        "A_relevant_C_k_rules_constructed",
        "sourced_maxwell_equation_derived",
        "em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "canonical_master_action_promoted",
        "master_action_promoted",
        "empirical_validation_claimed",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "records the convention-sensitive U(1) gauge stress-energy route only",
        "does not derive J^nu",
        "does not derive a psi-current route",
        "does not select an external current as native derivation",
        "does not prove current conservation",
        "does not prove A-source admissibility",
        "does not construct A-relevant C_k rules",
        "does not claim sourced Maxwell closure",
        "does not close EM",
        "does not close QFT-GR",
        "does not authorize semiclassical coupling",
        "does not promote the master action",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_a_stress_energy_route_packet_rotates_live_target_to_result_review() -> None:
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
        "ToeNativeAStressEnergyRouteUnderSelectedU1PolicyPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_PACKET_20260621_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["a_stress_energy_route_result"] == A_STRESS_ENERGY_ROUTE_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["stress_energy_route_recorded"] == "yes"
    assert consumed["stress_energy_T_A_derived"] == "yes"
    assert consumed["A_source_admissibility_proved"] == "no"
    assert consumed["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed["em_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["packet_result"] == "PENDING"
    assert active_row["result_review_pending"] == "yes"
    assert active_row["stress_energy_route_recorded"] == "yes"
    assert active_row["stress_energy_T_A_derived"] == "yes"
    assert active_row["current_route_derived"] == "no"
    assert active_row["A_source_admissibility_proved"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_stress_energy_route_packet_mirrors() -> None:
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
        "ToeNativeAStressEnergyRouteUnderSelectedU1PolicyPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_source_admissibility_review_for_vacuum_stress_energy",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "select_next_toe_native_A_route_after_stress_energy_route",
        "HISTORICAL_TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_PACKET_CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_stress_energy_route_under_selected_u1_policy",
        "HISTORICAL_TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_RESULT_REVIEW_CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_A_stress_energy_route_under_selected_u1_policy_result",
        "T^A_{mu nu} = - F_{mu alpha} F_{nu}{}^{alpha} + "
        "1/4 g_{mu nu} F_{alpha beta} F^{alpha beta}",
        "convention-sensitive",
        "does not derive J^nu",
        "does not prove A-source admissibility",
        "does not construct A-relevant C_k rules",
        "does not close QFT-GR",
        "master action",
    ]:
        assert token in joined


def test_a_stress_energy_route_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_stress_energy_route_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_stress_energy_route_under_selected_u1_policy_packet_gate.py"
    )
