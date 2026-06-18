from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_matter_sector_calculation_route_selection_report import (
    ARTIFACT_ID,
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
    ROUTE_SELECTION_RESULT,
    SELECTED_ROUTE_ID,
    SELECTED_ROUTE_LABEL,
    SELECTED_SURFACE_SYMBOL,
    SCHEMA_ID,
    build_toe_native_matter_sector_calculation_route_selection,
)
from formal.python.tools.toe_native_matter_sector_definition_packet_result_review_report import (
    DEFAULT_OUT as DEFINITION_RESULT_REVIEW_PATH,
    OUTCOME_ID as DEFINITION_RESULT_REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_matter_sector_calculation_route_selection_report.py"
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


def test_route_selection_files_exist() -> None:
    for path in [
        DEFINITION_RESULT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_route_selection_selects_phi_packet_preparation_only() -> None:
    review = _json(DEFINITION_RESULT_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert review["outcome_id"] == DEFINITION_RESULT_REVIEW_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["route_selection_result"] == ROUTE_SELECTION_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selected_surface_symbol"] == SELECTED_SURFACE_SYMBOL
    assert packet["selected_route_id"] == SELECTED_ROUTE_ID
    assert packet["selected_route_label"] == SELECTED_ROUTE_LABEL
    assert packet["selected_route_packet_authorized"] is True
    assert packet["selected_route_execution_authorized"] is False
    assert (
        build_toe_native_matter_sector_calculation_route_selection()
        == packet
    )


def test_route_selection_criteria_and_options_are_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    rows = {row["row_id"]: row for row in packet["selection_criteria"]}
    assert list(rows) == [
        "selector_consumes_current_target",
        "definition_review_accepts_surface_index_only",
        "phi_hint_is_nonbinding_selector_input",
        "phi_surface_available_for_bounded_route_preparation",
        "selected_route_prepares_packet_only",
        "non_selected_routes_deferred_without_rejection",
        "no_toe_native_matter_derivation_claim",
        "no_standard_model_derivation_claim",
        "no_qft_gr_or_semiclassical_closure",
        "no_master_action_promotion",
    ]
    assert packet["selection_criteria_count"] == 10
    assert packet["selection_criteria_accepted_count"] == 10
    assert packet["acceptance_criteria"] == {
        "consumes_current_route_selection_target": True,
        "definition_result_review_available_and_accepted": True,
        "prior_phi_hint_is_nonbinding": True,
        "phi_surface_indexed": True,
        "phi_route_has_reference_witness_but_not_native_derivation": True,
        "selected_route_is_packet_preparation_only": True,
        "selected_route_options_exactly_one_selected": True,
        "non_selected_routes_deferred": True,
        "selection_criteria_all_accepted": True,
        "no_toe_native_matter_derivation_claim": True,
        "no_standard_model_derivation_claim": True,
        "no_qft_gr_or_semiclassical_closure": True,
        "no_master_action_promotion": True,
    }
    options = {row["route_id"]: row for row in packet["route_options"]}
    assert packet["route_option_count"] == 4
    assert packet["route_options_selected_count"] == 1
    assert packet["route_options_deferred_count"] == 3
    assert options[SELECTED_ROUTE_ID]["status"] == "selected_for_packet_preparation"
    assert options[SELECTED_ROUTE_ID]["execution_status"] == "not_executed"
    for route_id in [
        "toe_native_gauge_current_route",
        "toe_native_fermion_stress_energy_route",
        "quantum_expectation_source_prerequisite_map",
    ]:
        assert options[route_id]["status"] == "deferred"
        assert options[route_id]["execution_status"] == "not_executed"


def test_route_selection_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "selected_route_execution_authorized",
        "scalar_witness_reopened",
        "scalar_witness_used_as_toe_native_derivation",
        "direct_phi_route_execution_authorized",
        "phi_variation_route_prepared",
        "phi_variation_route_executed",
        "phi_variation_derived",
        "phi_stress_energy_derived",
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
    assert packet["comparison_witness_use"] == "reference_only_not_derivation"
    assert "does not execute the phi route" in packet["non_claim_boundary"]
    assert packet["proof_depth_label"] == "RECORD_ONLY_SELECTOR_VALIDATED"
    assert packet["record_validated"] is True
    assert packet["symbolic_calculation_recorded"] is False
    assert packet["formal_theorem_backed_matter_derivation"] is False


def test_route_selection_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_route_selection_rotates_live_target_to_phi_packet_preparation() -> None:
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
        "ToeNativeMatterSectorCalculationRouteSelection.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_MATTER_SECTOR_CALCULATION_ROUTE_SELECTION_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["route_selection_result"] == ROUTE_SELECTION_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["route_selection_result"] == ROUTE_SELECTION_RESULT
    assert active_row["selected_surface_symbol"] == "phi"
    assert active_row["selected_route_id"] == SELECTED_ROUTE_ID
    assert active_row["selected_route_packet_authorized"] == "yes"
    assert active_row["selected_route_execution_authorized"] == "no"
    assert active_row["scalar_witness_used_as_toe_native_derivation"] == "no"
    assert active_row["toe_native_matter_derivation_claimed"] == "no"
    assert active_row["standard_model_derivation_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["semiclassical_coupling_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_route_selection_lean_and_surface_mirrors() -> None:
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
        ROUTE_SELECTION_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        SELECTED_ROUTE_ID,
        "ToeNativeMatterSectorCalculationRouteSelection",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_toe_native_phi_surface_variation_and_source_route_packet",
        "route selector chooses the phi surface variation/source route",
        "no phi route execution",
        "no ToE-native matter derivation",
        "no Standard Model derivation",
        "no canonical master-action promotion",
        "no QFT-GR source-map or seam closure",
        "no semiclassical coupling",
    ]:
        assert token in joined


def test_route_selection_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_matter_sector_calculation_route_selection_gate.py"
    )
