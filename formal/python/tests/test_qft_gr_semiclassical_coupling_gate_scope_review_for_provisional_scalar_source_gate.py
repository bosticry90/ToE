from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_source_report import (
    ARTIFACT_ID,
    AUXILIARY_HYGIENE_TARGET,
    CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM,
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
    PROOF_DEPTH_LABEL,
    SCHEMA_ID,
    SEMICLASSICAL_COUPLING_GATE_RESULT,
    SEMICLASSICAL_COUPLING_NOT_AUTHORIZED_RESULT,
    SEMICLASSICAL_EINSTEIN_EXPECTATION_FORM,
    SOURCE_ADMISSIBILITY_PACKET_PATH,
    TOE_NATIVE_ROUTE_STATUS,
    build_qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_source,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_source_report.py"
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


def test_semiclassical_gate_scope_review_files_exist() -> None:
    for path in [
        SOURCE_ADMISSIBILITY_PACKET_PATH,
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


def test_semiclassical_gate_scope_packet_records_route_split() -> None:
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
    assert packet["semiclassical_coupling_gate_result"] == (
        SEMICLASSICAL_COUPLING_GATE_RESULT
    )
    assert packet["semiclassical_coupling_not_authorized_result"] == (
        SEMICLASSICAL_COUPLING_NOT_AUTHORIZED_RESULT
    )
    assert packet["proof_depth_label"] == PROOF_DEPTH_LABEL
    assert packet["classical_einstein_scalar_equation_form"] == (
        CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM
    )
    assert packet["semiclassical_einstein_expectation_form"] == (
        SEMICLASSICAL_EINSTEIN_EXPECTATION_FORM
    )
    assert (
        build_qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_source()
        == packet
    )

    rows = {row["route_id"]: row for row in packet["route_review_rows"]}
    assert rows["classical_einstein_scalar_coupling"]["status"] == (
        "route_recorded_classical_sandbox_packet_authorized"
    )
    assert rows["semiclassical_quantum_expectation_coupling"]["status"] == (
        "not_authorized"
    )
    assert rows["toe_native_matter_source_route"]["status"] == "not_defined"
    assert rows["toe_native_matter_source_route"]["reason"] == TOE_NATIVE_ROUTE_STATUS
    assert rows["semiclassical_quantum_expectation_coupling"][
        "missing_requirements"
    ] == [
        "quantum_state",
        "stress_energy_operator",
        "renormalized_expectation_value",
        "state_domain",
        "renormalization_scheme",
        "anomaly_or_regularization_controls",
    ]


def test_semiclassical_gate_denies_required_overclaim_paths() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["classical_einstein_scalar_coupling_route_recorded"] is True
    assert packet["classical_einstein_scalar_coupling_route_packet_authorized"] is True
    assert packet["classical_einstein_scalar_coupling_constructed"] is False
    for key in [
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "semiclassical_quantum_expectation_route_authorized",
        "quantum_state_supplied",
        "stress_energy_operator_constructed",
        "quantum_stress_energy_expectation_constructed",
        "renormalized_expectation_value_constructed",
        "renormalized_stress_energy_constructed",
        "renormalization_scheme_supplied",
        "renormalization_result_claimed",
        "state_domain_supplied",
        "state_expectation_functional_link_claimed",
        "anomaly_or_regularization_controls_supplied",
        "toe_native_matter_source_route_defined",
        "toe_native_matter_sector_defined",
        "toe_matter_model_derived",
        "toe_native_matter_derivation_claimed",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "arbitrary_distributional_source_admissibility_claimed",
        "arbitrary_distributional_source_promoted",
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
        "semiclassical_coupling_authorized",
        "semiclassical_Einstein_equation_derivation",
        "quantum_stress_energy_expectation_construction",
        "renormalization_result",
        "state_domain_supplied",
        "ToE_native_matter_derivation",
        "QFT_GR_closure",
        "master_action_promotion",
    ]:
        assert token in packet["critical_gate_fail_conditions"]


def test_semiclassical_gate_validation_policy_records_bounded_status() -> None:
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
    assert policy["aggregate_timeout_with_steady_progress_interpretation"] == (
        "incomplete_validation_not_mathematical_failure"
    )
    assert packet["formal_differential_geometry_theorem_backed"] is False
    assert packet["record_validated"] is True
    assert packet["symbolic_calculation_recorded"] is True
    assert packet["auxiliary_hygiene_target_queued"] == AUXILIARY_HYGIENE_TARGET
    assert packet["auxiliary_hygiene_target_supersedes_qft_gr_live_target"] is False


def test_semiclassical_gate_rotates_live_target_to_classical_route_packet() -> None:
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
        "QFTGRSemiclassicalCouplingGateScopeReviewForProvisionalScalarSource.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_SEMICLASSICAL_COUPLING_GATE_SCOPE_REVIEW_FOR_PROVISIONAL_"
        "SCALAR_SOURCE_20260618_v0.json"
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
    assert consumed["semiclassical_coupling_gate_scope_review_completed"] == "yes"
    assert consumed["semiclassical_coupling_gate_result"] == (
        SEMICLASSICAL_COUPLING_GATE_RESULT
    )
    assert consumed["semiclassical_coupling_authorized"] == "no"
    assert consumed["selected_next_target"] == NEXT_TARGET

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["classical_einstein_scalar_coupling_route_recorded"] == "yes"
    assert active_row["classical_einstein_scalar_coupling_route_packet_authorized"] == (
        "yes"
    )
    assert active_row["classical_einstein_scalar_coupling_constructed"] == "no"
    assert active_row["semiclassical_coupling_authorized"] == "no"
    assert active_row["semiclassical_coupling_claimed"] == "no"
    assert active_row["semiclassical_einstein_equation_derived"] == "no"
    assert active_row["quantum_state_supplied"] == "no"
    assert active_row["renormalized_expectation_value_constructed"] == "no"
    assert active_row["state_domain_supplied"] == "no"
    assert active_row["proof_depth_label"] == PROOF_DEPTH_LABEL
    assert active_row["auxiliary_hygiene_target_queued"] == AUXILIARY_HYGIENE_TARGET
    assert active_row["auxiliary_hygiene_target_supersedes_qft_gr_live_target"] == "no"


def test_semiclassical_gate_lean_and_surface_mirrors() -> None:
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
        SEMICLASSICAL_COUPLING_GATE_RESULT,
        SEMICLASSICAL_COUPLING_NOT_AUTHORIZED_RESULT,
        PROOF_DEPTH_LABEL,
        AUXILIARY_HYGIENE_TARGET,
        "QFTGRSemiclassicalCouplingGateScopeReviewForProvisionalScalarSource",
        "ToeFormal.Derivation.QFTGRScalarSandbox",
        "ToeFormal.Derivation.CurrentTarget",
        "ToeFormal.Release.CurrentAuthority",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source",
        "CURRENT_AUXILIARY_HYGIENE_TARGET_QUEUED_v0",
        "no semiclassical coupling",
        "no QFT-GR closure",
        "no ToE-native matter derivation",
    ]:
        assert token in joined


def test_semiclassical_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_source_gate.py"
    )
