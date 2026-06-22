from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_source_admissibility_review_for_vacuum_stress_energy_result_review_report import (
    DEFAULT_OUT as A_SOURCE_RESULT_REVIEW_PATH,
    OUTCOME_ID as A_SOURCE_RESULT_REVIEW_OUTCOME,
)
from formal.python.tools.toe_native_a_vacuum_source_admissibility_identity_packet_report import (
    A_FIELD_DOMAIN_POLICY,
    ANTISYMMETRY_ROUTE,
    ARTIFACT_ID,
    BIANCHI_IDENTITY_ROUTE,
    CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE,
    DEFAULT_OUT,
    DIVERGENCE_IDENTITY,
    F_DEFINITION_POLICY,
    GAUGE_GROUP_POLICY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    METRIC_COMPATIBILITY_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    ON_SHELL_VACUUM_CONSERVATION_ROUTE,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONDITION,
    SOURCE_ADMISSIBILITY_REVIEW_RETRY_TARGET,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
    build_toe_native_a_vacuum_source_admissibility_identity_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_vacuum_source_admissibility_identity_packet_report.py"
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
CONSUMED_TARGET = "prepare_toe_native_A_vacuum_source_admissibility_identity_packet"


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


def test_a_vacuum_source_identity_packet_files_exist() -> None:
    for path in [
        A_SOURCE_RESULT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_vacuum_source_identity_packet_shape() -> None:
    prior = _json(A_SOURCE_RESULT_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert prior["outcome_id"] == A_SOURCE_RESULT_REVIEW_OUTCOME
    assert prior["selected_next_target"] == CONSUMED_TARGET
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["packet_result"] == "PREPARED"
    assert packet["identity_packet_result"] == PACKET_RESULT
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_toe_native_a_vacuum_source_admissibility_identity_packet() == packet


def test_a_vacuum_source_identity_packet_constructs_on_shell_identity() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["gauge_group_policy"] == GAUGE_GROUP_POLICY
    assert packet["A_field_domain_policy"] == A_FIELD_DOMAIN_POLICY
    assert packet["F_definition_policy"] == F_DEFINITION_POLICY
    assert packet["F_antisymmetry_route"] == ANTISYMMETRY_ROUTE
    assert packet["bianchi_identity_route"] == BIANCHI_IDENTITY_ROUTE
    assert packet["vacuum_euler_lagrange_route"] == VACUUM_EULER_LAGRANGE_ROUTE
    assert packet["metric_compatibility_route"] == METRIC_COMPATIBILITY_ROUTE
    assert (
        packet["stress_energy_under_selected_u1_policy"]
        == STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
    )
    assert packet["source_admissibility_condition"] == SOURCE_ADMISSIBILITY_CONDITION
    assert packet["divergence_identity"] == DIVERGENCE_IDENTITY
    assert packet["stress_energy_divergence_route"] == DIVERGENCE_IDENTITY
    assert (
        packet["on_shell_vacuum_conservation_identity"]
        == ON_SHELL_VACUUM_CONSERVATION_IDENTITY
    )
    assert packet["on_shell_vacuum_conservation_route"] == (
        ON_SHELL_VACUUM_CONSERVATION_ROUTE
    )
    assert (
        packet["current_coupled_stress_exchange_route"]
        == CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE
    )
    assert (
        packet["source_admissibility_review_retry_target"]
        == SOURCE_ADMISSIBILITY_REVIEW_RETRY_TARGET
    )
    assert packet["derivation_step_count"] == 8
    assert packet["derivation_step_constructed_count"] == 7
    assert packet["identity_criteria_count"] == 12
    assert packet["identity_criteria_constructed_count"] == 10


def test_a_vacuum_source_identity_derivation_steps_are_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    steps = {row["step_id"]: row for row in packet["derivation_steps"]}
    assert list(steps) == [
        "state_selected_u1_assumptions",
        "state_candidate_stress_energy",
        "compute_divergence",
        "use_antisymmetry_and_bianchi",
        "reduce_to_vacuum_field_equation_residual",
        "insert_vacuum_u1_equation",
        "conclude_on_shell_vacuum_identity",
        "preserve_current_coupled_caution",
    ]
    assert BIANCHI_IDENTITY_ROUTE in steps["state_selected_u1_assumptions"][
        "mathematical_content"
    ]
    assert STRESS_ENERGY_UNDER_SELECTED_U1_POLICY in steps[
        "state_candidate_stress_energy"
    ]["mathematical_content"]
    assert DIVERGENCE_IDENTITY in steps[
        "reduce_to_vacuum_field_equation_residual"
    ]["mathematical_content"]
    assert VACUUM_EULER_LAGRANGE_ROUTE in steps["insert_vacuum_u1_equation"][
        "mathematical_content"
    ]
    assert ON_SHELL_VACUUM_CONSERVATION_IDENTITY in steps[
        "conclude_on_shell_vacuum_identity"
    ]["mathematical_content"]
    assert "J^alpha" in steps["preserve_current_coupled_caution"][
        "mathematical_content"
    ]


def test_a_vacuum_source_identity_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "identity_packet_prepared",
        "result_review_authorization_consumed",
        "selected_u1_policy_preserved",
        "F_dA_preserved",
        "F_antisymmetry_recorded",
        "bianchi_identity_recorded",
        "vacuum_equation_preserved",
        "levi_civita_connection_required",
        "metric_compatibility_required",
        "smooth_domain_required",
        "metric_signature_preserved",
        "stress_energy_route_preserved",
        "source_admissibility_condition_preserved",
        "divergence_identity_constructed",
        "divergence_identity_verified",
        "divergence_identity_proved",
        "source_admissibility_identity_executed",
        "source_admissibility_identity_verified",
        "source_admissibility_identity_constructed",
        "source_admissibility_identity_proved",
        "on_shell_vacuum_conservation_identity_constructed",
        "on_shell_vacuum_conservation_route_constructed",
        "local_on_shell_vacuum_source_route_constructed",
        "candidate_gravity_source_route_recorded",
        "review_target_authorized",
        "identity_result_review_authorized",
    ]:
        assert packet[key] is True, key
    for key in [
        "local_on_shell_vacuum_source_route_accepted",
        "full_source_admissibility_review_accepted",
        "source_admissibility_review_completed",
        "source_admissibility_executed",
        "source_admissibility_proved",
        "source_admissibility_claimed",
        "A_source_admissibility_proved",
        "stress_energy_as_gravity_source_authorized",
        "total_matter_gauge_stress_energy_conservation_proved",
        "total_matter_gauge_stress_energy_conservation_claimed",
        "J_nu_derived",
        "psi_current_route_constructed",
        "external_current_native_derivation_selected",
        "current_conservation_theorem_claimed",
        "A_relevant_C_k_rules_constructed",
        "sourced_maxwell_equation_derived",
        "em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "master_action_promoted",
        "empirical_validation_claimed",
    ]:
        assert packet[key] is False, key


def test_a_vacuum_source_identity_rotates_live_target_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    skip_if_not_current_target(registry, NEXT_TARGET)
    state = registry["current_target_state"]
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
    assert registry["live_next_target"] == NEXT_TARGET
    assert registry["previous_live_next_target"] == CONSUMED_TARGET
    assert registry["active_lane"] == NEXT_TARGET
    assert state["live_next_target"] == NEXT_TARGET
    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["active_lane"] == NEXT_TARGET
    assert registry["live_next_target_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "ToeNativeAVacuumSourceAdmissibilityIdentityPacket.lean"
    )
    assert registry["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_PACKET_20260621_v0.json"
    )
    assert registry["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == "PREPARED"
    assert consumed["identity_packet_result"] == PACKET_RESULT
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["divergence_identity_proved"] == "yes"
    assert consumed["source_admissibility_identity_proved"] == "yes"
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
    assert active_row["divergence_identity_proved"] == "yes"
    assert active_row["source_admissibility_identity_proved"] == "yes"
    assert active_row["full_source_admissibility_review_accepted"] == "no"
    assert active_row["source_admissibility_proved"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["A_relevant_C_k_rules_constructed"] == "no"
    assert active_row["em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_vacuum_source_identity_mirrors() -> None:
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
        "ToeNativeAVacuumSourceAdmissibilityIdentityPacket",
        "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_OUTCOME_v0",
        "HISTORICAL_TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_PACKET_CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_vacuum_source_admissibility_identity_packet",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_A_vacuum_source_admissibility_identity_packet_result",
        DIVERGENCE_IDENTITY,
        ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
        "does not accept the full source-admissibility review",
        "does not derive J^nu",
        "does not close QFT-GR",
        "master action",
    ]:
        assert token in joined, token


def test_a_vacuum_source_identity_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_vacuum_source_identity_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_vacuum_source_admissibility_identity_packet_gate.py"
    )
