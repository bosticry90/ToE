from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_route_selection_after_stress_energy_route_report import (
    DEFAULT_OUT as A_AFTER_STRESS_SELECTOR_PATH,
    OUTCOME_ID as A_AFTER_STRESS_SELECTOR_OUTCOME,
)
from formal.python.tools.toe_native_a_source_admissibility_review_for_vacuum_stress_energy_report import (
    ARTIFACT_ID,
    BIANCHI_IDENTITY_ROUTE,
    CONSUMED_TARGET,
    CURRENT_COUPLED_EXCHANGE_CAUTION,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    F_DEFINITION_POLICY,
    GAUGE_GROUP_POLICY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    ON_SHELL_VACUUM_CONSERVATION_ROUTE,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONDITION,
    SOURCE_ROUTE_STILL_BLOCKED,
    STRESS_ENERGY_DIVERGENCE_ROUTE,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
    build_toe_native_a_source_admissibility_review_for_vacuum_stress_energy,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_source_admissibility_review_for_vacuum_stress_energy_report.py"
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


def test_a_source_admissibility_review_preparation_files_exist() -> None:
    for path in [
        A_AFTER_STRESS_SELECTOR_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_source_admissibility_review_preparation_packet_shape() -> None:
    selector = _json(A_AFTER_STRESS_SELECTOR_PATH)
    packet = _json(DEFAULT_OUT)
    assert selector["outcome_id"] == A_AFTER_STRESS_SELECTOR_OUTCOME
    assert selector["selected_next_target"] == CONSUMED_TARGET
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["packet_result"] == "PREPARED"
    assert packet["a_source_admissibility_review_result"] == PACKET_RESULT
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_toe_native_a_source_admissibility_review_for_vacuum_stress_energy() == packet


def test_a_source_admissibility_review_preparation_records_vacuum_test_surface() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["gauge_group_policy"] == GAUGE_GROUP_POLICY
    assert packet["F_definition_policy"] == F_DEFINITION_POLICY
    assert packet["vacuum_euler_lagrange_route"] == VACUUM_EULER_LAGRANGE_ROUTE
    assert packet["source_route_still_blocked"] == SOURCE_ROUTE_STILL_BLOCKED
    assert (
        packet["stress_energy_under_selected_u1_policy"]
        == STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
    )
    assert packet["source_admissibility_condition"] == SOURCE_ADMISSIBILITY_CONDITION
    assert packet["bianchi_identity_route"] == BIANCHI_IDENTITY_ROUTE
    assert packet["stress_energy_divergence_route"] == STRESS_ENERGY_DIVERGENCE_ROUTE
    assert packet["on_shell_vacuum_conservation_route"] == ON_SHELL_VACUUM_CONSERVATION_ROUTE
    assert packet["current_coupled_exchange_caution"] == CURRENT_COUPLED_EXCHANGE_CAUTION
    assert packet["review_preparation_criteria_count"] == 12
    assert packet["review_preparation_criteria_prepared_count"] == 12


def test_a_source_admissibility_review_preparation_blocks_promotion() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "source_admissibility_review_prepared",
        "vacuum_gauge_source_admissibility_review_prepared",
        "local_on_shell_source_review_surface_prepared",
        "local_on_shell_source_route_candidate_recorded",
        "candidate_source_object_recorded",
        "source_admissibility_condition_recorded",
        "bianchi_identity_route_recorded",
        "stress_energy_divergence_route_recorded",
        "on_shell_vacuum_conservation_route_recorded",
        "current_coupled_exchange_caution_recorded",
        "result_review_authorized",
    ]:
        assert packet[key] is True, key
    for key in [
        "source_admissibility_review_executed",
        "source_admissibility_review_completed",
        "source_admissibility_executed",
        "source_admissibility_proved",
        "source_admissibility_claimed",
        "A_source_admissibility_proved",
        "stress_energy_source_admissibility_proved",
        "stress_energy_as_gravity_source_authorized",
        "J_nu_derived",
        "current_route_derived",
        "current_conservation_proved",
        "A_relevant_C_k_rules_constructed",
        "sourced_maxwell_equation_derived",
        "em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "master_action_promoted",
        "empirical_validation_claimed",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "prepares the vacuum U(1) gauge stress-energy source-admissibility review only",
        "does not execute the result review",
        "does not prove A-source admissibility",
        "does not derive J^nu",
        "does not construct a psi-current route",
        "does not select an external current as a native derivation",
        "does not prove a current conservation theorem",
        "does not construct A-relevant C_k rules",
        "does not claim sourced Maxwell closure",
        "does not close EM",
        "does not close QFT-GR",
        "does not promote the master action",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_a_source_admissibility_review_preparation_rotates_to_result_review() -> None:
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
        "ToeNativeASourceAdmissibilityReviewForVacuumStressEnergy.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_FOR_VACUUM_STRESS_ENERGY_"
        "20260621_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == "PREPARED"
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["source_admissibility_review_prepared"] == "yes"
    assert consumed["local_on_shell_source_route_candidate_recorded"] == "yes"
    assert consumed["source_admissibility_review_executed"] == "no"
    assert consumed["source_admissibility_proved"] == "no"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["packet_result"] == "PENDING"
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["result_review_pending"] == "yes"
    assert active_row["source_admissibility_review_prepared"] == "yes"
    assert active_row["source_admissibility_review_executed"] == "no"
    assert active_row["source_admissibility_proved"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_source_admissibility_review_preparation_mirrors() -> None:
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
        "ToeNativeASourceAdmissibilityReviewForVacuumStressEnergy",
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_FOR_VACUUM_STRESS_ENERGY_OUTCOME_v0",
        "HISTORICAL_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_FOR_VACUUM_STRESS_ENERGY_CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_source_admissibility_review_for_vacuum_stress_energy",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_A_source_admissibility_review_for_vacuum_stress_energy_result",
        SOURCE_ADMISSIBILITY_CONDITION,
        BIANCHI_IDENTITY_ROUTE,
        STRESS_ENERGY_DIVERGENCE_ROUTE,
        "does not prove A-source admissibility",
        "does not derive J^nu",
        "does not close QFT-GR",
        "master action",
    ]:
        assert token in joined


def test_a_source_admissibility_review_preparation_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_source_admissibility_review_preparation_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_source_admissibility_review_for_vacuum_stress_energy_gate.py"
    )
