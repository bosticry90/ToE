from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_matter_sector_definition_packet_report import (
    DEFAULT_OUT as DEFINITION_PACKET_PATH,
    OUTCOME_ID as DEFINITION_PACKET_OUTCOME,
)
from formal.python.tools.toe_native_matter_sector_definition_packet_result_review_report import (
    ARTIFACT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    DEFINITION_RESULT,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    RECOMMENDED_FIRST_ROUTE_HINT,
    RECOMMENDED_FIRST_ROUTE_STATUS,
    RECOMMENDED_FIRST_ROUTE_TARGET_HINT,
    REVIEW_RESULT,
    SCHEMA_ID,
    build_toe_native_matter_sector_definition_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_matter_sector_definition_packet_result_review_report.py"
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


def test_definition_result_review_files_exist() -> None:
    for path in [
        DEFINITION_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_definition_result_review_accepts_surface_index_only() -> None:
    definition = _json(DEFINITION_PACKET_PATH)
    packet = _json(DEFAULT_OUT)
    assert definition["outcome_id"] == DEFINITION_PACKET_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["review_result"] == REVIEW_RESULT
    assert packet["definition_result"] == DEFINITION_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["candidate_symbols"] == ["psi", "A", "phi", "rho", "C_k"]
    assert packet["candidate_surface_count"] == 5
    assert packet["master_action_surface_index_accepted"] is True
    assert packet["route_selection_authorized"] is True
    assert (
        build_toe_native_matter_sector_definition_packet_result_review()
        == packet
    )


def test_definition_result_review_criteria_accept_required_scope() -> None:
    packet = _json(DEFAULT_OUT)
    rows = {row["row_id"]: row for row in packet["review_criteria"]}
    assert list(rows) == [
        "required_surfaces_indexed",
        "surface_classifications_are_bounded",
        "variation_stress_energy_quantum_and_seam_routes_marked",
        "scalar_witness_preserved_only_as_reference",
        "master_action_working_form_status_preserved",
        "no_toe_native_matter_derivation_claim",
        "no_standard_model_derivation_claim",
        "no_canonical_master_action_promotion",
        "no_qft_gr_or_semiclassical_closure",
        "route_selection_authorized_only_after_review",
    ]
    assert packet["review_criteria_count"] == 10
    assert packet["review_criteria_accepted_count"] == 10
    for row in rows.values():
        assert row["status"] == "accepted", row
    assert packet["acceptance_criteria"] == {
        "consumes_expected_result_review_target": True,
        "definition_packet_available_and_accepted": True,
        "required_surfaces_indexed": True,
        "surface_classifications_are_bounded": True,
        "variation_stress_energy_quantum_and_seam_routes_marked": True,
        "scalar_witness_preserved_only_as_reference": True,
        "master_action_working_form_status_preserved": True,
        "no_toe_native_matter_derivation_claim": True,
        "no_standard_model_derivation_claim": True,
        "no_canonical_master_action_promotion": True,
        "no_qft_gr_or_semiclassical_closure": True,
        "review_criteria_all_accepted": True,
        "next_target_is_route_selection_only": True,
    }


def test_definition_result_review_phi_hint_is_nonbinding() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["recommended_first_route_hint"] == RECOMMENDED_FIRST_ROUTE_HINT
    assert (
        packet["recommended_first_route_target_hint"]
        == RECOMMENDED_FIRST_ROUTE_TARGET_HINT
    )
    assert packet["recommended_first_route_status"] == RECOMMENDED_FIRST_ROUTE_STATUS
    assert packet["selected_next_target"] == "select_toe_native_matter_sector_calculation_route"
    assert packet["critical_gate_fail_conditions"][-1] == (
        "direct phi route execution without selector"
    )
    progression = {row["stage"]: row for row in packet["downstream_progression"]}
    assert progression["recommended_phi_route"]["status"] == (
        "recorded_as_nonbinding_selector_input"
    )
    assert progression["toe_native_matter_sector_calculation_route_selection"][
        "status"
    ] == "NEXT_TARGET_AUTHORIZED"


def test_definition_result_review_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
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
    assert "execute the phi route before route selection" in packet["non_claim_boundary"]
    assert packet["proof_depth_label"] == "RECORD_ONLY_REVIEW_VALIDATED"
    assert packet["record_validated"] is True
    assert packet["symbolic_calculation_recorded"] is False
    assert packet["formal_theorem_backed_matter_derivation"] is False


def test_definition_result_review_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_definition_result_review_rotates_live_target_to_route_selection() -> None:
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
        "ToeNativeMatterSectorDefinitionPacketResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_MATTER_SECTOR_DEFINITION_PACKET_RESULT_REVIEW_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == REVIEW_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["review_result"] == REVIEW_RESULT
    assert active_row["route_selection_authorized"] == "yes"
    assert active_row["recommended_first_route_hint"] == "phi"
    assert (
        active_row["recommended_first_route_target_hint"]
        == "prepare_toe_native_phi_surface_variation_and_source_route_packet"
    )
    assert active_row["recommended_first_route_status"] == (
        "recorded_as_nonbinding_selector_input"
    )
    assert active_row["direct_phi_route_execution_authorized"] == "no"
    assert active_row["recommended_phi_route_binding"] == "no"
    assert active_row["toe_native_matter_derivation_claimed"] == "no"
    assert active_row["standard_model_derivation_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["semiclassical_coupling_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_definition_result_review_lean_and_surface_mirrors() -> None:
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
        REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        RECOMMENDED_FIRST_ROUTE_TARGET_HINT,
        "ToeNativeMatterSectorDefinitionPacketResultReview",
        "CURRENT_LIVE_NEXT_TARGET_v0: select_toe_native_matter_sector_calculation_route",
        "phi is recorded as a nonbinding selector input",
        "no ToE-native matter derivation",
        "no Standard Model derivation",
        "no canonical master-action promotion",
        "no QFT-GR source-map or seam closure",
        "no semiclassical coupling",
        "no direct phi route execution",
    ]:
        assert token in joined


def test_definition_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_matter_sector_definition_packet_result_review_gate.py"
    )
