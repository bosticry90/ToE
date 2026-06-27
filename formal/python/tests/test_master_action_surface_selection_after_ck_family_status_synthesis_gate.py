from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_historical_target_recorded,
    assert_public_surfaces_match_registry,
)
from formal.python.tools.master_action_ck_family_status_synthesis_result_review_report import (
    DEFAULT_OUT as REVIEW_OUT,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as REVIEW_OUTCOME,
)
from formal.python.tools.master_action_ck_family_gap_review_after_phi_a_and_psi_a_report import (
    DEFAULT_OUT as GAP_REVIEW_OUT,
    LEAN_PACKET_PATH as GAP_REVIEW_LEAN_PACKET_PATH,
    NEXT_TARGET as GAP_REVIEW_NEXT_TARGET,
    NEXT_TARGET_KIND as GAP_REVIEW_NEXT_TARGET_KIND,
    OUTCOME_ID as GAP_REVIEW_OUTCOME,
)
from formal.python.tools.master_action_surface_selection_after_ck_family_status_synthesis_report import (
    ARTIFACT_ID,
    BLOCKED_CLAIMS,
    C_BRIDGE_CLASSIFICATION,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CLASSIFICATION,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_SOURCE_CLASSIFICATION,
    C_TRANSPORT_CLASSIFICATION,
    CURRENT_CANDIDATE,
    DEFAULT_OUT,
    GAP_REVIEW_INSPECTION_QUESTIONS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_MASTER_ACTION_SURFACE,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    build_master_action_surface_selection_after_ck_family_status_synthesis,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "master_action_surface_selection_after_ck_family_status_synthesis_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
CURRENT_TARGET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
CURRENT_AUTHORITY_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
)
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
    return path.read_text(encoding="utf-8-sig")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_master_action_surface_selection_after_ck_family_status_synthesis_files_exist() -> None:
    for path in [
        REVIEW_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_master_action_surface_selection_after_ck_family_status_synthesis_selects_gap_review() -> None:
    review = _json(REVIEW_OUT)
    selector = _json(DEFAULT_OUT)

    assert review["outcome_id"] == REVIEW_OUTCOME
    assert review["selected_next_target"] == CONSUMED_TARGET

    assert selector["artifact_id"] == ARTIFACT_ID
    assert selector["schema_id"] == SCHEMA_ID
    assert selector["packet_id"] == PACKET_ID
    assert selector["prepared"] is True
    assert selector["accepted"] is True
    assert selector["outcome_id"] == OUTCOME_ID
    assert selector["selection_result"] == OUTCOME_ID
    assert selector["packet_result"] == OUTCOME_ID
    assert selector["packet_classification"] == PACKET_CLASSIFICATION
    assert selector["consumed_target"] == CONSUMED_TARGET
    assert selector["selected_next_target"] == NEXT_TARGET
    assert selector["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert selector["selected_master_action_surface"] == SELECTED_MASTER_ACTION_SURFACE
    assert build_master_action_surface_selection_after_ck_family_status_synthesis() == selector


def test_master_action_surface_selection_after_ck_family_status_synthesis_preserves_scope() -> None:
    selector = _json(DEFAULT_OUT)

    assert selector["selector_choices_count"] == 4
    assert selector["surface_option_count"] == 4
    assert selector["surface_options_selected_count"] == 1
    assert selector["surface_options_deferred_count"] == 3
    assert selector["gap_review_inspection_questions"] == GAP_REVIEW_INSPECTION_QUESTIONS
    assert selector["gap_review_inspection_question_count"] == 8
    assert selector["blocked_claims"] == BLOCKED_CLAIMS
    assert selector["blocked_claim_count"] == 14
    assert selector["selection_criteria_count"] == 9
    assert selector["selection_criteria_accepted_count"] == 9

    for key in [
        "selector_target_prepared",
        "selector_target_accepted",
        "selection_executed",
        "master_action_surface_selector_executed",
        "master_action_surface_selection_executed",
        "next_master_action_surface_selected",
        "master_action_surface_selected",
        "ck_family_gap_review_selected",
        "ck_family_gap_review_preparation_authorized",
    ]:
        assert selector[key] is True, key
    for key in [
        "ck_family_gap_review_prepared",
        "gap_review_prepared",
        "gap_review_executed",
        "new_physics_created",
        "new_field_or_interaction_expansion_selected",
        "immediate_new_field_or_interaction_expansion_selected",
        "return_to_qft_gr_source_admissibility_lane_selected",
        "public_plain_language_status_packet_prepared",
        "next_interaction_surface_selected",
    ]:
        assert selector[key] is False, key

    assert selector["C_source_classification"] == C_SOURCE_CLASSIFICATION
    assert selector["C_bridge_classification"] == C_BRIDGE_CLASSIFICATION
    assert selector["C_transport_classification"] == C_TRANSPORT_CLASSIFICATION
    assert selector["C_exchange_classification"] == C_EXCHANGE_CLASSIFICATION
    for token in [
        CURRENT_CANDIDATE,
        SOURCED_GAUGE_ROUTE,
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        C_EXCHANGE_CONSTRAINT_FORM,
        C_EXCHANGE_ADMISSIBILITY_CONDITION,
    ]:
        assert token in selector["mathematical_statement"], token


def test_master_action_surface_selection_after_ck_family_status_synthesis_preserves_nonclaims() -> None:
    selector = _json(DEFAULT_OUT)
    for key in [
        "C_k_action_embedding_claimed",
        "C_k_action_embedding_selected",
        "C_k_action_variation_executed",
        "C_k_action_variation_authorized",
        "multiplier_route_selected",
        "multiplier_action_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_claimed",
        "direct_dynamical_law_interpretation_selected",
        "full_maxwell_closure_claimed",
        "full_Maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "standard_model_derivation_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
        "master_action_promotion",
    ]:
        assert selector[key] is False, key
    for phrase in [
        "creates no new physics",
        "does not expand immediately to another field or interaction",
        "what remains theorem-linked, policy-level, assumption-supplied, or route-check-only",
        "no C_k action embedding",
        "no C_k action variation",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no master-action promotion",
        "working-form, noncanonical, non-promoted organizing surface",
        "full ToeFormal aggregate is kept as NOT_RUN",
    ]:
        assert phrase in selector["non_claim_boundary"], phrase


def test_master_action_surface_selection_after_ck_family_status_synthesis_rotates_to_gap_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == _rel(DEFAULT_OUT)
    assert consumed["selection_result"] == OUTCOME_ID
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["result_token"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["master_action_surface_selector_executed"] == "yes"
    assert consumed["master_action_surface_selected"] == "yes"
    assert consumed["ck_family_gap_review_selected"] == "yes"
    assert consumed["ck_family_gap_review_prepared"] == "no"

    if not is_current:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]

        gap_row = _workstream(registry, NEXT_TARGET)
        assert gap_row["status"] == "paused"
        assert gap_row["authorization_evidence"] == _rel(GAP_REVIEW_LEAN_PACKET_PATH)
        assert gap_row["report"] == _rel(GAP_REVIEW_OUT)
        assert gap_row["packet_result"] == GAP_REVIEW_OUTCOME
        assert gap_row["review_result"] == GAP_REVIEW_OUTCOME
        assert gap_row["outcome_id"] == GAP_REVIEW_OUTCOME
        assert gap_row["result_token"] == GAP_REVIEW_OUTCOME
        assert gap_row["selected_next_target"] == GAP_REVIEW_NEXT_TARGET
        assert gap_row["selected_next_target_kind"] == GAP_REVIEW_NEXT_TARGET_KIND
        assert gap_row["gap_review_prepared"] == "yes"
        assert gap_row["gap_review_executed"] == "yes"
        assert str(gap_row["gap_count"]) == "8"
        assert str(gap_row["open_gap_count"]) == "8"
        assert str(gap_row["closed_gap_count"]) == "0"
        assert gap_row["result_review_prepared"] == "no"
        assert gap_row["C_k_action_variation_executed"] == "no"
        assert gap_row["em_qft_closure_claimed"] == "no"
        assert gap_row["qft_gr_closure_claimed"] == "no"
        assert gap_row["gr_qm_closure_claimed"] == "no"
        assert gap_row["master_action_promoted"] == "no"

        active = _workstream(registry, GAP_REVIEW_NEXT_TARGET)
        assert active["status"] == "active"
        assert active["workstream_id"] == GAP_REVIEW_NEXT_TARGET
        assert active["active_lane"] == GAP_REVIEW_NEXT_TARGET
        assert active["authorized_next_strict_target"] == GAP_REVIEW_NEXT_TARGET
        assert active["authorized_target"] == GAP_REVIEW_NEXT_TARGET
        assert active["authorization_evidence"] == _rel(GAP_REVIEW_LEAN_PACKET_PATH)
        assert active["report"] == _rel(GAP_REVIEW_OUT)
        assert active["consumed_target"] == NEXT_TARGET
        assert active["packet_result"] == "PENDING"
        assert active["review_result"] == "PENDING"
        assert active["outcome_id"] == GAP_REVIEW_OUTCOME
        assert active["result_token"] == GAP_REVIEW_OUTCOME
        assert active["selected_next_target"] == GAP_REVIEW_NEXT_TARGET
        assert active["selected_next_target_kind"] == GAP_REVIEW_NEXT_TARGET_KIND
        assert active["gap_review_prepared"] == "yes"
        assert active["gap_review_executed"] == "yes"
        assert active["result_review_prepared"] == "no"
        assert active["result_review_accepted"] == "no"
        assert active["C_k_action_variation_executed"] == "no"
        assert active["em_qft_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["gr_qm_closure_claimed"] == "no"
        assert active["master_action_promoted"] == "no"
        return

    assert NEXT_TARGET not in registry["completed_targets"]
    assert NEXT_TARGET not in registry["consumed_targets"]
    assert NEXT_TARGET not in registry["paused_lanes"]

    active = _workstream(registry, NEXT_TARGET)
    assert active["status"] == "active"
    assert active["workstream_id"] == NEXT_TARGET
    assert active["active_lane"] == NEXT_TARGET
    assert active["authorized_next_strict_target"] == NEXT_TARGET
    assert active["authorized_target"] == NEXT_TARGET
    assert active["authorization_evidence"] == evidence
    assert active["report"] == _rel(DEFAULT_OUT)
    assert active["consumed_target"] == CONSUMED_TARGET
    assert active["packet_result"] == "PENDING"
    assert active["review_result"] == "PENDING"
    assert active["outcome_id"] == OUTCOME_ID
    assert active["result_token"] == OUTCOME_ID
    assert active["selected_next_target"] == NEXT_TARGET
    assert active["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert active["ck_family_gap_review_preparation_authorized"] == "yes"
    assert active["ck_family_gap_review_prepared"] == "no"
    assert active["gap_review_executed"] == "no"
    assert active["C_k_action_variation_executed"] == "no"
    assert active["em_qft_closure_claimed"] == "no"
    assert active["qft_gr_closure_claimed"] == "no"
    assert active["gr_qm_closure_claimed"] == "no"
    assert active["master_action_promoted"] == "no"


def test_master_action_surface_selection_after_ck_family_status_synthesis_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_AGGREGATE_PATH,
            CURRENT_TARGET_PATH,
            CURRENT_AUTHORITY_PATH,
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
        "MasterActionSurfaceSelectionAfterCKFamilyStatusSynthesis",
        CONSUMED_TARGET,
        NEXT_TARGET,
        SELECTED_MASTER_ACTION_SURFACE,
        "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS_OUTCOME_v0",
        "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS_NONCLAIM_BOUNDARY_v0",
        C_SOURCE_CLASSIFICATION,
        C_BRIDGE_CLASSIFICATION,
        C_TRANSPORT_CLASSIFICATION,
        C_EXCHANGE_CLASSIFICATION,
        "What would be required for action embedding?",
        "What would be required for C_k variation?",
        "What would be required for seam closure?",
        "What would be required for empirical prediction?",
        "no C_k action embedding",
        "no C_k action variation",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_master_action_surface_selection_after_ck_family_status_synthesis_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_master_action_surface_selection_after_ck_family_status_synthesis_gate.py"
    )
