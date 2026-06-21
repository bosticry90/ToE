from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_route_selection_after_vacuum_u1_variation_report import (
    ARTIFACT_ID,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    F_DEFINITION_POLICY,
    GAUGE_GROUP_POLICY,
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
    ROUTE_SELECTOR_CANDIDATES,
    SCHEMA_ID,
    SELECTED_ROUTE_ID,
    SELECTED_ROUTE_LABEL,
    SELECTION_RESULT,
    SOURCE_ROUTE_STILL_BLOCKED,
    VACUUM_EULER_LAGRANGE_ROUTE,
    build_toe_native_a_route_selection_after_vacuum_u1_variation,
)
from formal.python.tools.toe_native_a_vacuum_variation_retry_under_selected_u1_policy_result_review_report import (
    DEFAULT_OUT as A_VACUUM_RETRY_REVIEW_PATH,
    OUTCOME_ID as A_VACUUM_RETRY_REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_route_selection_after_vacuum_u1_variation_report.py"
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


def test_a_route_selection_after_vacuum_u1_files_exist() -> None:
    for path in [
        A_VACUUM_RETRY_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_route_selection_after_vacuum_u1_selects_stress_energy_route() -> None:
    review = _json(A_VACUUM_RETRY_REVIEW_PATH)
    selector = _json(DEFAULT_OUT)
    assert review["outcome_id"] == A_VACUUM_RETRY_REVIEW_OUTCOME
    assert review["selected_next_target"] == CONSUMED_TARGET
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
    assert selector["selected_route_id"] == SELECTED_ROUTE_ID
    assert selector["selected_route_label"] == SELECTED_ROUTE_LABEL
    assert selector["selected_route_status"] == "selected_for_packet_preparation"
    assert selector["selected_route_execution_status"] == "not_executed"
    assert build_toe_native_a_route_selection_after_vacuum_u1_variation() == selector


def test_a_route_selection_after_vacuum_u1_compares_expected_routes() -> None:
    selector = _json(DEFAULT_OUT)
    assert selector["gauge_group_policy"] == GAUGE_GROUP_POLICY
    assert selector["F_definition_policy"] == F_DEFINITION_POLICY
    assert selector["vacuum_euler_lagrange_route"] == VACUUM_EULER_LAGRANGE_ROUTE
    assert selector["source_route_still_blocked"] == SOURCE_ROUTE_STILL_BLOCKED
    assert selector["route_selector_candidates"] == ROUTE_SELECTOR_CANDIDATES
    assert selector["route_option_count"] == 5
    assert selector["route_options_selected_count"] == 1
    assert selector["route_options_deferred_count"] == 4
    assert selector["selection_criteria_count"] == 12
    assert selector["selection_criteria_accepted_count"] == 12
    statuses = {row["route_id"]: row["status"] for row in selector["route_options"]}
    assert statuses == {
        "A_stress_energy_route": "selected_for_packet_preparation",
        "A_current_coupling_route": "deferred_blocked_pending_J_nu_policy",
        "A_current_conservation_route": "deferred_premature_without_current_derivation",
        "A_relevant_C_k_source_bridge_transport_route": "deferred_premature_before_T_A_source_route",
        "A_nonabelian_route": "deferred_beyond_minimal_U1_route",
    }


def test_a_route_selection_after_vacuum_u1_blocks_derivation_and_closure() -> None:
    selector = _json(DEFAULT_OUT)
    for key in [
        "selector_prepared",
        "selector_executed",
        "route_selection_executed",
        "next_a_route_selected",
        "stress_energy_route_selected",
        "stress_energy_route_packet_authorized",
    ]:
        assert selector[key] is True, key
    for key in [
        "stress_energy_route_execution_authorized",
        "stress_energy_derivation_executed",
        "stress_energy_T_A_derived",
        "stress_energy_route_constructed",
        "J_nu_derived",
        "current_route_derived",
        "current_conservation_proved",
        "A_source_admissibility_proved",
        "A_relevant_C_k_rules_constructed",
        "nonabelian_route_selected",
        "em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "master_action_promoted",
        "empirical_validation_claimed",
    ]:
        assert selector[key] is False, key
    for phrase in [
        "selects the A stress-energy route",
        "next preparation packet only",
        "does not execute stress-energy derivation",
        "does not derive T_A_mu_nu",
        "does not derive J^nu",
        "does not prove current conservation",
        "does not construct A-relevant C_k rules",
        "does not select a non-Abelian route",
        "does not close EM",
        "does not close QFT-GR",
        "does not promote the master action",
    ]:
        assert phrase in selector["non_claim_boundary"], phrase


def test_a_route_selection_after_vacuum_u1_rotates_live_target_to_stress_energy() -> None:
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
        "ToeNativeARouteSelectionAfterVacuumU1Variation.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_U1_VARIATION_20260621_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["selection_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["stress_energy_route_selected"] == "yes"
    assert consumed["stress_energy_derivation_executed"] == "no"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["current_conservation_proved"] == "no"
    assert consumed["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed["nonabelian_route_selected"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["packet_result"] == "PENDING"
    assert active_row["selection_result"] == OUTCOME_ID
    assert active_row["stress_energy_route_selected"] == "yes"
    assert active_row["stress_energy_route_packet_authorized"] == "yes"
    assert active_row["stress_energy_derivation_executed"] == "no"
    assert active_row["stress_energy_T_A_derived"] == "no"
    assert active_row["current_route_derived"] == "no"
    assert active_row["em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_route_selection_after_vacuum_u1_mirrors() -> None:
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
        SELECTED_ROUTE_ID,
        "ToeNativeARouteSelectionAfterVacuumU1Variation",
        "HISTORICAL_TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_PACKET_CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_stress_energy_route_under_selected_u1_policy",
        "HISTORICAL_TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_U1_VARIATION_CURRENT_LIVE_NEXT_TARGET_v0: "
        "select_next_toe_native_A_route_after_vacuum_u1_variation",
        "A_current_coupling_route",
        "A_current_conservation_route",
        "A_relevant_C_k_source_bridge_transport_route",
        "A_nonabelian_route",
        "does not execute metric variation",
        "does not derive T_A_mu_nu",
        "does not derive J^nu",
        "does not close QFT-GR",
        "master action",
    ]:
        assert token in joined


def test_a_route_selection_after_vacuum_u1_validation_policy_is_bounded() -> None:
    selector = _json(DEFAULT_OUT)
    policy = selector["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_route_selection_after_vacuum_u1_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_route_selection_after_vacuum_u1_variation_gate.py"
    )
