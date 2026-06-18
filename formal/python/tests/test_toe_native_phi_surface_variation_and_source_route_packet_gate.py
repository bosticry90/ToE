from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_matter_sector_calculation_route_selection_report import (
    DEFAULT_OUT as ROUTE_SELECTION_PATH,
    OUTCOME_ID as ROUTE_SELECTION_OUTCOME,
)
from formal.python.tools.toe_native_phi_surface_variation_and_source_route_packet_report import (
    ARTIFACT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    IMPORTED_SCALAR_COMPARISON_DECISION,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MASTER_PHI_LAGRANGIAN,
    MASTER_STRESS_ENERGY_CANDIDATE,
    METRIC_SIGNATURE_DECISION,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PHI_ROUTE_PACKET_RESULT,
    PHI_VARIATION_NO_SEAM_EQUATION,
    PHI_VARIATION_RAW_EQUATION,
    SCHEMA_ID,
    SELECTED_ROUTE_ID,
    SELECTED_SURFACE_SYMBOL,
    SOURCE_ROUTE_STATUS_DECISION,
    TOE_NATIVE_STATUS_DECISION,
    build_toe_native_phi_surface_variation_and_source_route_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_phi_surface_variation_and_source_route_packet_report.py"
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


def test_phi_surface_packet_files_exist() -> None:
    for path in [
        ROUTE_SELECTION_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_surface_packet_records_raw_route_and_blocks_native_derivation() -> None:
    route_selection = _json(ROUTE_SELECTION_PATH)
    packet = _json(DEFAULT_OUT)
    assert route_selection["outcome_id"] == ROUTE_SELECTION_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["phi_route_packet_result"] == PHI_ROUTE_PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selected_surface_symbol"] == SELECTED_SURFACE_SYMBOL
    assert packet["selected_route_id"] == SELECTED_ROUTE_ID
    assert packet["master_phi_lagrangian"] == MASTER_PHI_LAGRANGIAN
    assert packet["metric_signature_decision"] == METRIC_SIGNATURE_DECISION
    assert packet["phi_variation_raw_equation"] == PHI_VARIATION_RAW_EQUATION
    assert packet["phi_variation_no_seam_equation"] == PHI_VARIATION_NO_SEAM_EQUATION
    assert packet["master_stress_energy_candidate"] == MASTER_STRESS_ENERGY_CANDIDATE
    assert packet["source_route_status_decision"] == SOURCE_ROUTE_STATUS_DECISION
    assert packet["imported_scalar_comparison_decision"] == IMPORTED_SCALAR_COMPARISON_DECISION
    assert packet["toe_native_status_decision"] == TOE_NATIVE_STATUS_DECISION
    assert build_toe_native_phi_surface_variation_and_source_route_packet() == packet


def test_phi_surface_packet_answers_required_questions() -> None:
    packet = _json(DEFAULT_OUT)
    questions = {row["question_id"]: row for row in packet["route_questions"]}
    assert list(questions) == [
        "q1_master_action_scalar_term_defined",
        "q2_metric_signature_used",
        "q3_exact_scalar_lagrangian",
        "q4_phi_variation",
        "q5_metric_variation",
        "q6_imported_scalar_sandbox_reproduction",
        "q7_seam_constraint_modification",
        "q8_native_or_copied",
        "q9_remaining_unproved",
    ]
    assert packet["route_question_count"] == 9
    assert questions["q1_master_action_scalar_term_defined"]["status"] == "partially_defined"
    assert questions["q2_metric_signature_used"]["status"] == "blocked_pending_explicit_convention"
    assert questions["q3_exact_scalar_lagrangian"]["answer"] == MASTER_PHI_LAGRANGIAN
    assert questions["q4_phi_variation"]["answer"] == PHI_VARIATION_RAW_EQUATION
    assert questions["q5_metric_variation"]["answer"].startswith("delta S_phi^MA")
    assert questions["q6_imported_scalar_sandbox_reproduction"]["status"] == (
        "partial_after_convention_normalization_only"
    )
    assert questions["q7_seam_constraint_modification"]["status"] == (
        "blocked_pending_C_k_definition"
    )
    assert questions["q8_native_or_copied"]["status"] == "not_native_derived"
    assert questions["q9_remaining_unproved"]["status"] == "retained_blockers"


def test_phi_surface_packet_retains_expected_blockers_and_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["retained_blocker_count"] == 6
    assert {row["blocker_id"] for row in packet["retained_blockers"]} == {
        "phi_metric_signature_convention_missing",
        "phi_field_content_and_index_set_missing",
        "phi_potential_not_generated",
        "seam_constraints_variational_content_missing",
        "source_admissibility_not_established",
        "native_generation_rule_missing",
    }
    assert packet["phi_surface_variation_route_prepared"] is True
    assert packet["raw_phi_variation_formula_recorded"] is True
    assert packet["raw_metric_variation_formula_recorded"] is True
    assert packet["stress_energy_candidate_formula_recorded"] is True
    assert packet["symbolic_calculation_recorded"] is True
    for key in [
        "formal_theorem_backed_matter_derivation",
        "phi_variation_route_executed",
        "phi_variation_derived_as_toe_native",
        "phi_stress_energy_derived_as_toe_native",
        "toe_native_phi_source_route_constructed",
        "toe_native_phi_source_admissibility_claimed",
        "toe_native_phi_source_conservation_claimed",
        "toe_native_matter_derivation_claimed",
        "toe_native_matter_sector_derived",
        "toe_native_matter_sector_defined",
        "toe_matter_sector_derived",
        "toe_matter_model_derived",
        "standard_model_derivation_claimed",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "weak_conservation_claimed",
        "bianchi_compatibility_claimed",
        "source_map_closed",
        "qft_gr_solved",
        "qft_gr_closure_claimed",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_authorized",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "semiclassical_source_established",
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
    assert "does not claim a ToE-native matter derivation" in packet["non_claim_boundary"]


def test_phi_surface_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_surface_packet_rotates_live_target_to_result_review() -> None:
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
        "ToeNativePhiSurfaceVariationAndSourceRoutePacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_PHI_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["phi_route_packet_result"] == PHI_ROUTE_PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["phi_route_packet_result"] == PHI_ROUTE_PACKET_RESULT
    assert active_row["selected_surface_symbol"] == "phi"
    assert active_row["selected_route_id"] == SELECTED_ROUTE_ID
    assert active_row["phi_surface_variation_route_prepared"] == "yes"
    assert active_row["toe_native_status_decision"] == TOE_NATIVE_STATUS_DECISION
    assert active_row["toe_native_matter_derivation_claimed"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["semiclassical_coupling_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_surface_packet_lean_and_surface_mirrors() -> None:
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
        PHI_ROUTE_PACKET_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        SELECTED_ROUTE_ID,
        "ToeNativePhiSurfaceVariationAndSourceRoutePacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: review_toe_native_phi_surface_variation_and_source_route_result",
        "raw symbolic variation/source route",
        "signature, C_k, and native generation gaps",
        "no ToE-native matter derivation",
        "no source admissibility or conservation",
        "no canonical master-action promotion",
        "no QFT-GR source-map or seam closure",
        "no semiclassical coupling",
    ]:
        assert token in joined


def test_phi_surface_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_phi_surface_variation_and_source_route_packet_gate.py"
    )
