from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_action_derivability_retry_with_provisional_matter_sector_report import (
    ACTION_DERIVABILITY_RESULT,
)
from formal.python.tools.qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source_report import (
    BIANCHI_COMPATIBILITY_RESULT,
)
from formal.python.tools.qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source_report import (
    CLASSICAL_EINSTEIN_SCALAR_COUPLING_RESULT,
    CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM,
)
from formal.python.tools.qft_gr_classical_einstein_scalar_coupling_route_packet_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PACKET_PATH,
    POSITIVE_LOCAL_CLASSICAL_SOURCE_WITNESS_CLASSIFICATION,
)
from formal.python.tools.qft_gr_provisional_scalar_classical_source_route_witness_closeout_report import (
    ARTIFACT_ID,
    AUXILIARY_HYGIENE_TARGET,
    CLOSEOUT_RESULT,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    SCHEMA_ID,
    build_qft_gr_provisional_scalar_classical_source_route_witness_closeout,
)
from formal.python.tools.qft_gr_source_admissibility_review_for_provisional_scalar_source_report import (
    PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT,
)
from formal.python.tools.qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source_report import (
    DIVERGENCE_IDENTITY,
    SCALAR_EQUATION_OF_MOTION,
    STRESS_ENERGY_COVARIANT_EXPRESSION,
    WEAK_CONSERVATION_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_provisional_scalar_classical_source_route_witness_closeout_report.py"
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


def test_scalar_classical_source_route_witness_closeout_files_exist() -> None:
    for path in [
        RESULT_REVIEW_PACKET_PATH,
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


def test_scalar_classical_source_route_witness_closeout_accepts_only_witness_scope() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["closeout_result"] == CLOSEOUT_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["positive_local_classical_source_witness_classification"] == (
        POSITIVE_LOCAL_CLASSICAL_SOURCE_WITNESS_CLASSIFICATION
    )
    assert packet["positive_local_classical_source_witness_closed"] is True
    assert packet["witness_closeout_completed"] is True
    assert packet["scalar_sandbox_branch_closed"] is True
    assert packet["default_scalar_sandbox_extension_authorized"] is False
    assert packet["toe_native_matter_sector_definition_packet_authorized"] is True
    assert packet["auxiliary_hygiene_target_queued"] == AUXILIARY_HYGIENE_TARGET
    assert packet["auxiliary_hygiene_target_supersedes_qft_gr_live_target"] is False
    assert (
        build_qft_gr_provisional_scalar_classical_source_route_witness_closeout()
        == packet
    )


def test_scalar_classical_source_route_witness_closeout_carries_route_inputs() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["action_derivability_result"] == ACTION_DERIVABILITY_RESULT
    assert packet["stress_energy_covariant_expression"] == STRESS_ENERGY_COVARIANT_EXPRESSION
    assert packet["scalar_equation_of_motion"] == SCALAR_EQUATION_OF_MOTION
    assert packet["weak_conservation_result"] == WEAK_CONSERVATION_RESULT
    assert packet["weak_conservation_identity"] == DIVERGENCE_IDENTITY
    assert packet["on_shell_required"] is True
    assert packet["bianchi_compatibility_result"] == BIANCHI_COMPATIBILITY_RESULT
    assert (
        packet["provisional_scalar_source_admissibility_result"]
        == PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT
    )
    assert (
        packet["classical_einstein_scalar_coupling_result"]
        == CLASSICAL_EINSTEIN_SCALAR_COUPLING_RESULT
    )
    assert (
        packet["classical_einstein_scalar_coupling_equation"]
        == CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM
    )
    assert packet["route_internal_compatibility_constructed"] is True
    assert packet["provisional_classical_sandbox_route_only"] is True
    assert packet["imported_provisional_scalar_sector_only"] is True


def test_scalar_classical_source_route_witness_closeout_requirements_are_satisfied() -> None:
    packet = _json(DEFAULT_OUT)
    rows = {row["row_id"]: row for row in packet["closeout_requirements"]}
    assert list(rows) == [
        "scalar_action_derived_source_carried_forward",
        "on_shell_weak_conservation_carried_forward",
        "on_shell_bianchi_compatibility_carried_forward",
        "classical_coupling_route_result_reviewed",
        "witness_classified_provisional_imported_classical",
        "toe_native_matter_derivation_false",
        "semiclassical_coupling_false",
        "qft_gr_closure_false",
        "master_action_promotion_false",
    ]
    assert packet["closeout_requirement_count"] == 9
    assert packet["closeout_requirement_satisfied_count"] == 9
    for row in rows.values():
        assert row["status"] in {
            "closed_as_positive_witness_input",
            "closed_as_positive_witness",
            "nonclaim_preserved",
        }
    assert packet["acceptance_criteria"] == {
        "consumes_expected_witness_closeout_target": True,
        "result_review_packet_available_and_accepted": True,
        "scalar_action_derived_source_carried_forward": True,
        "on_shell_weak_conservation_carried_forward": True,
        "on_shell_bianchi_compatibility_carried_forward": True,
        "classical_coupling_route_result_reviewed": True,
        "witness_classified_provisional_imported_classical": True,
        "toe_native_matter_derivation_false": True,
        "semiclassical_coupling_false": True,
        "qft_gr_closure_false": True,
        "master_action_promotion_false": True,
        "closeout_requirements_all_satisfied": True,
    }


def test_scalar_classical_source_route_witness_closeout_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "source_map_closed",
        "qft_gr_solved",
        "semiclassical_source_established",
        "toe_matter_sector_derived",
        "canonical_master_action_promoted",
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
    assert packet["forbidden_claims"] == [
        "source_map_closed",
        "qft_gr_solved",
        "semiclassical_source_established",
        "toe_matter_sector_derived",
        "canonical_master_action_promoted",
    ]
    for token in [
        "source-map closure",
        "QFT-GR solution",
        "semiclassical source establishment",
        "ToE-native matter-sector derivation",
        "canonical master-action promotion",
    ]:
        assert token in packet["non_claim_boundary"]


def test_scalar_classical_source_route_witness_closeout_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False
    assert packet["formal_differential_geometry_theorem_backed"] is False
    assert packet["record_validated"] is True
    assert packet["symbolic_calculation_recorded"] is True


def test_scalar_classical_source_route_witness_closeout_rotates_live_target_to_native_matter_definition() -> None:
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
        "QFTGRProvisionalScalarClassicalSourceRouteWitnessCloseout.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_PROVISIONAL_SCALAR_CLASSICAL_SOURCE_ROUTE_WITNESS_CLOSEOUT_"
        "20260618_v0.json"
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
    assert consumed["closeout_result"] == CLOSEOUT_RESULT
    assert consumed["witness_closeout_completed"] == "yes"
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["qft_gr_source_map_closure_authorized"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["closeout_result"] == CLOSEOUT_RESULT
    assert active_row["positive_local_classical_source_witness_closed"] == "yes"
    assert active_row["witness_closeout_completed"] == "yes"
    assert active_row["scalar_sandbox_branch_closed"] == "yes"
    assert active_row["default_scalar_sandbox_extension_authorized"] == "no"
    assert active_row["toe_native_matter_sector_definition_packet_authorized"] == "yes"
    assert active_row["imported_provisional_scalar_sector_only"] == "yes"
    assert active_row["provisional_classical_sandbox_route_only"] == "yes"
    assert active_row["semiclassical_coupling_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["qft_gr_seam_closed"] == "no"
    assert active_row["toe_native_matter_derivation_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_scalar_classical_source_route_witness_closeout_lean_and_surface_mirrors() -> None:
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
        CLOSEOUT_RESULT,
        POSITIVE_LOCAL_CLASSICAL_SOURCE_WITNESS_CLASSIFICATION,
        "QFTGRProvisionalScalarClassicalSourceRouteWitnessCloseout",
        "ToeFormal.Derivation.QFTGRScalarSandbox",
        "ToeFormal.Derivation.CurrentTarget",
        "ToeFormal.Release.CurrentAuthority",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_toe_native_matter_sector_definition_packet",
        "positive local classical source witness",
        "no QFT-GR source-map or seam closure",
        "no ToE-native matter derivation",
        "no master-action promotion",
        "stale-current-token quarantine remains queued",
    ]:
        assert token in joined


def test_scalar_classical_source_route_witness_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_provisional_scalar_classical_source_route_witness_closeout_gate.py"
    )
