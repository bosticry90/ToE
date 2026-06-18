from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_matter_sector_definition_packet_report import (
    ARTIFACT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    DEFINITION_RESULT,
    FIRST_CALCULATION_ROUTE_CANDIDATES,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MASTER_ACTION_DOC_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    POST_REVIEW_ROUTE_SELECTION_TARGET,
    SCALAR_WITNESS_CLOSEOUT_PACKET_PATH,
    SCHEMA_ID,
    build_toe_native_matter_sector_definition_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_matter_sector_definition_packet_report.py"
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


def test_toe_native_matter_sector_definition_packet_files_exist() -> None:
    for path in [
        SCALAR_WITNESS_CLOSEOUT_PACKET_PATH,
        MASTER_ACTION_DOC_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_toe_native_matter_sector_definition_packet_accepts_candidate_surface_index() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["definition_result"] == DEFINITION_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["post_review_route_selection_target"] == (
        POST_REVIEW_ROUTE_SELECTION_TARGET
    )
    assert packet["first_calculation_route_candidates"] == (
        FIRST_CALCULATION_ROUTE_CANDIDATES
    )
    assert packet["candidate_master_action_surface"] == "S_ToE[g, psi, A, phi, rho]"
    assert packet["candidate_symbols"] == ["psi", "A", "phi", "rho", "C_k"]
    assert packet["candidate_surface_count"] == 5
    assert packet["native_candidate_surface_defined_nonpromotionally"] is True
    assert packet["master_action_matter_surfaces_indexed_as_native_candidates"] is True
    assert (
        build_toe_native_matter_sector_definition_packet()
        == packet
    )


def test_toe_native_matter_sector_definition_packet_inventory_requirements() -> None:
    packet = _json(DEFAULT_OUT)
    rows = {row["row_id"]: row for row in packet["inventory_requirements"]}
    assert list(rows) == [
        "matter_sector_candidates_listed",
        "source_of_each_candidate_identified",
        "imported_vs_native_candidate_status_marked",
        "variation_route_specified_or_blocked",
        "stress_energy_route_specified_or_blocked",
        "quantum_operator_route_specified_or_blocked",
        "seam_constraint_dependency_recorded",
        "next_calculation_target_selected",
    ]
    assert packet["inventory_requirement_count"] == 8
    assert packet["inventory_requirement_satisfied_count"] == 8
    for row in rows.values():
        assert row["satisfied"] is True, row
    assert packet["acceptance_criteria"] == {
        "consumes_expected_live_target": True,
        "scalar_witness_closeout_available_and_accepted": True,
        "master_action_document_available": True,
        "master_action_working_form_noncanonical": True,
        "matter_sector_candidates_listed": True,
        "source_of_each_candidate_identified": True,
        "imported_vs_native_candidate_status_marked": True,
        "variation_route_specified_or_blocked": True,
        "stress_energy_route_specified_or_blocked": True,
        "quantum_operator_route_specified_or_blocked": True,
        "seam_constraint_dependency_recorded": True,
        "next_calculation_target_selected": True,
        "gate_nonclaims_preserved": True,
    }


def test_toe_native_matter_sector_definition_packet_surface_rows_are_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    surfaces = {row["symbol"]: row for row in packet["matter_surface_inventory"]}
    assert list(surfaces) == ["psi", "A", "phi", "rho", "C_k"]

    assert surfaces["psi"]["imported_known_physics_term"] is True
    assert surfaces["psi"]["provisional_toe_native_candidate"] is True
    assert surfaces["psi"]["variation_route_status"] == "specified_but_blocked"
    assert surfaces["psi"]["stress_energy_route_status"] == "specified_but_blocked"
    assert surfaces["psi"]["quantum_operator_route_status"] == "blocked"

    assert surfaces["A"]["imported_known_physics_term"] is True
    assert surfaces["A"]["provisional_toe_native_candidate"] is True
    assert surfaces["A"]["variation_route_status"] == "specified_but_blocked"

    assert (
        surfaces["phi"]["variation_route_status"]
        == "partially_witnessed_for_imported_scalar_blocked_for_toe_native"
    )
    assert (
        surfaces["phi"]["stress_energy_route_status"]
        == "partially_witnessed_for_imported_scalar_blocked_for_toe_native"
    )
    assert "imported sandbox witness" in surfaces["phi"]["stress_energy_route"]

    assert surfaces["rho"]["pure_organizing_placeholder"] is True
    assert surfaces["rho"]["variation_route_status"] == "blocked"
    assert surfaces["C_k"]["pure_organizing_placeholder"] is True
    assert surfaces["C_k"]["variation_route_status"] == "blocked"
    for surface in surfaces.values():
        assert surface["source_of_candidate_identified"] is True
        assert surface["insufficiently_defined"] is True
        assert surface["seam_constraint_dependency"], surface


def test_toe_native_matter_sector_definition_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["scalar_witness_closeout_preserved_as_reference"] is True
    assert packet["scalar_sandbox_reopened"] is False
    assert packet["master_action_working_form_noncanonical"] is True
    assert packet["definition_packet_only"] is True
    assert packet["promotion_packet"] is False
    for key in [
        "canonical_toe_native_matter_sector_defined",
        "toe_native_matter_sector_defined",
        "toe_native_matter_sector_derived",
        "toe_native_matter_derivation_claimed",
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
        "renormalized_stress_energy_expectation_constructed",
        "quantum_state_source_constructed",
        "quantum_stress_energy_operator_constructed",
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
    assert packet["critical_gate_fail_conditions"] == [
        "ToE-native matter derivation",
        "Standard Model derivation",
        "canonical master-action promotion",
        "QFT-GR closure",
        "semiclassical coupling",
        "empirical validation",
        "public readiness",
    ]


def test_toe_native_matter_sector_definition_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False
    assert packet["proof_depth_label"] == "RECORD_ONLY_INDEX_VALIDATED"
    assert packet["formal_theorem_backed_matter_derivation"] is False
    assert packet["record_validated"] is True
    assert packet["symbolic_calculation_recorded"] is False


def test_toe_native_matter_sector_definition_packet_rotates_live_target_to_result_review() -> None:
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
        "ToeNativeMatterSectorDefinitionPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/TOE_NATIVE_MATTER_SECTOR_DEFINITION_PACKET_20260618_v0.json"
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
    assert consumed["definition_result"] == DEFINITION_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["definition_result"] == DEFINITION_RESULT
    assert active_row["candidate_surface_count"] == "5"
    assert active_row["candidate_symbols"] == "psi,A,phi,rho,C_k"
    assert active_row["master_action_working_form_noncanonical"] == "yes"
    assert (
        active_row["master_action_matter_surfaces_indexed_as_native_candidates"]
        == "yes"
    )
    assert active_row["toe_native_matter_sector_candidate_surface_defined"] == "yes"
    assert active_row["toe_native_matter_sector_defined"] == "no"
    assert active_row["toe_native_matter_derivation_claimed"] == "no"
    assert active_row["standard_model_derivation_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["semiclassical_coupling_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"
    assert (
        active_row["next_after_definition_review_suggested"]
        == POST_REVIEW_ROUTE_SELECTION_TARGET
    )


def test_toe_native_matter_sector_definition_packet_lean_and_surface_mirrors() -> None:
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
        DEFINITION_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        POST_REVIEW_ROUTE_SELECTION_TARGET,
        "ToeNativeMatterSectorDefinitionPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_matter_sector_definition_packet_result",
        "psi, A, phi, rho, and C_k",
        "working-form non-canonical master action",
        "no ToE-native matter derivation",
        "no Standard Model derivation",
        "no canonical master-action promotion",
        "no QFT-GR source-map or seam closure",
        "no semiclassical coupling",
        "stale-current-token quarantine remains queued",
    ]:
        assert token in joined


def test_toe_native_matter_sector_definition_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_matter_sector_definition_packet_gate.py"
    )
