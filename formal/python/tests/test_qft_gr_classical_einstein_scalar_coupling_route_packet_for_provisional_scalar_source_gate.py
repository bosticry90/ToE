from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source_report import (
    ARTIFACT_ID,
    CLASSICAL_EINSTEIN_SCALAR_COUPLING_RESULT,
    CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LEFT_HAND_SIDE_DIVERGENCE_IDENTITY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PROOF_DEPTH_LABEL,
    SCHEMA_ID,
    SEMICLASSICAL_GATE_PACKET_PATH,
    SOURCE_SIDE_CONSERVATION_REQUIREMENT,
    build_qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source,
)
from formal.python.tools.qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source_report import (
    DIVERGENCE_IDENTITY,
    SCALAR_EQUATION_OF_MOTION,
    STRESS_ENERGY_COVARIANT_EXPRESSION,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source_report.py"
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
SCALAR_SANDBOX_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRScalarSandbox.lean"
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


def test_classical_einstein_scalar_route_packet_files_exist() -> None:
    for path in [
        SEMICLASSICAL_GATE_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        SCALAR_SANDBOX_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_classical_einstein_scalar_route_packet_constructs_bounded_route() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["classical_einstein_scalar_coupling_result"] == (
        CLASSICAL_EINSTEIN_SCALAR_COUPLING_RESULT
    )
    assert packet["classical_einstein_scalar_coupling_equation"] == (
        CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM
    )
    assert packet["stress_energy_covariant_expression"] == (
        STRESS_ENERGY_COVARIANT_EXPRESSION
    )
    assert packet["scalar_equation_of_motion"] == SCALAR_EQUATION_OF_MOTION
    assert packet["weak_conservation_identity"] == DIVERGENCE_IDENTITY
    assert packet["left_hand_side_divergence_identity"] == (
        LEFT_HAND_SIDE_DIVERGENCE_IDENTITY
    )
    assert packet["source_side_conservation_requirement"] == (
        SOURCE_SIDE_CONSERVATION_REQUIREMENT
    )
    assert packet["route_internal_compatibility_constructed"] is True
    assert packet["classical_einstein_scalar_coupling_route_constructed"] is True
    assert packet["provisional_classical_sandbox_route_only"] is True
    assert (
        build_qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source()
        == packet
    )

    assert packet["acceptance_criteria"] == {
        "consumes_authorized_classical_route_target": True,
        "semiclassical_gate_packet_available": True,
        "classical_route_packet_authorized_by_gate": True,
        "semiclassical_route_remains_not_authorized": True,
        "local_scalar_source_admissibility_carried": True,
        "classical_coupling_equation_stated": True,
        "source_side_conservation_available_on_shell": True,
        "left_hand_side_divergence_free_under_scope": True,
        "solution_existence_and_wellposedness_not_claimed": True,
    }


def test_classical_route_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["bounded_positive_classical_source_route_witness_candidate"] is True
    assert packet["witness_closeout_completed"] is False
    for key in [
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "renormalized_stress_energy_expectation_constructed",
        "renormalized_expectation_value_constructed",
        "renormalized_stress_energy_constructed",
        "quantum_state_source_constructed",
        "quantum_state_supplied",
        "quantum_stress_energy_operator_constructed",
        "stress_energy_operator_constructed",
        "quantum_stress_energy_expectation_constructed",
        "renormalization_scheme_supplied",
        "renormalization_result_claimed",
        "state_domain_supplied",
        "state_expectation_functional_link_claimed",
        "anomaly_or_regularization_controls_supplied",
        "toe_native_matter_source_route_defined",
        "toe_native_matter_sector_defined",
        "toe_matter_model_derived",
        "toe_native_matter_derivation_claimed",
        "generic_source_admissibility_claimed",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "arbitrary_distributional_source_admissibility_claimed",
        "arbitrary_distributional_source_promoted",
        "solution_existence_claimed",
        "solution_uniqueness_claimed",
        "regularity_analysis_completed",
        "boundary_initial_data_supplied",
        "coupled_pde_solution_constructed",
        "coupled_einstein_scalar_system_solved",
        "global_wellposedness_claimed",
        "standard_model_derivation_claimed",
        "qft_gr_closure_claimed",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_authorized",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "public_submission_authorized",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "phase2_readiness_claim",
        "pillar_completion_inferred",
        "seam_closure_claim",
    ]:
        assert packet[key] is False, key
    for token in [
        "semiclassical_coupling",
        "renormalized_stress_energy_expectation",
        "quantum_state_or_source_construction",
        "ToE_native_matter_derivation",
        "generic_source_admissibility",
        "solution_existence_claim",
        "global_wellposedness_claim",
        "QFT_GR_seam_closure",
        "master_action_promotion",
    ]:
        assert token in packet["critical_gate_fail_conditions"]


def test_classical_route_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_status_allowed_values"] == [
        "PASSED",
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
        "FAILED",
        "NOT_RUN",
    ]
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False
    assert packet["proof_depth_label"] == PROOF_DEPTH_LABEL
    assert packet["formal_differential_geometry_theorem_backed"] is False
    assert packet["record_validated"] is True
    assert packet["symbolic_calculation_recorded"] is True


def test_classical_route_packet_rotates_live_target_to_result_review() -> None:
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
        "QFTGRClassicalEinsteinScalarCouplingRoutePacketForProvisionalScalarSource.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_FOR_"
        "PROVISIONAL_SCALAR_SOURCE_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert state["next_strict_target_coverage"][CONSUMED_TARGET][
        "status"
    ] == "completed_consumed_live_target"
    assert state["next_strict_target_coverage"][NEXT_TARGET][
        "status"
    ] == "active_live_next_target"

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["classical_einstein_scalar_coupling_route_constructed"] == "yes"
    assert consumed["classical_einstein_scalar_coupling_result"] == (
        CLASSICAL_EINSTEIN_SCALAR_COUPLING_RESULT
    )
    assert consumed["solution_existence_claimed"] == "no"
    assert consumed["global_wellposedness_claimed"] == "no"
    assert consumed["selected_next_target"] == NEXT_TARGET

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["classical_einstein_scalar_coupling_route_packet_prepared"] == (
        "yes"
    )
    assert active_row["route_internal_compatibility_constructed"] == "yes"
    assert active_row["bounded_positive_classical_source_route_witness_candidate"] == (
        "yes"
    )
    assert active_row["witness_closeout_completed"] == "no"
    assert active_row["semiclassical_coupling_claimed"] == "no"
    assert active_row["solution_existence_claimed"] == "no"
    assert active_row["global_wellposedness_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_classical_route_packet_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_AGGREGATE_PATH,
            SCALAR_SANDBOX_AGGREGATE_PATH,
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
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        CLASSICAL_EINSTEIN_SCALAR_COUPLING_RESULT,
        "QFTGRClassicalEinsteinScalarCouplingRoutePacketForProvisionalScalarSource",
        "ToeFormal.Derivation.QFTGRScalarSandbox",
        "ToeFormal.Derivation.CurrentTarget",
        "ToeFormal.Release.CurrentAuthority",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_qft_gr_classical_einstein_scalar_coupling_route_packet_result",
        "no coupled solution",
        "no solution existence",
        "no global well-posedness",
        "no semiclassical coupling",
        "no QFT-GR closure",
        "no ToE-native matter derivation",
    ]:
        assert token in joined


def test_classical_route_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source_gate.py"
    )
