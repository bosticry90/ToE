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
from formal.python.tools.master_action_ck_family_status_synthesis_after_phi_a_and_psi_a_report import (
    C_BRIDGE_CLASSIFICATION,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CLASSIFICATION,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_SOURCE_CLASSIFICATION,
    C_TRANSPORT_CLASSIFICATION,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    DEFAULT_OUT as SYNTHESIS_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as SYNTHESIS_LEAN_PACKET_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as SYNTHESIS_OUTCOME,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
)
from formal.python.tools.master_action_ck_family_status_synthesis_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    ARTIFACT_ID,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    RECOMMENDED_SELECTOR_CHOICE,
    REVIEW_RESULT,
    SCHEMA_ID,
    SELECTOR_CHOICES,
    build_master_action_ck_family_status_synthesis_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "master_action_ck_family_status_synthesis_result_review_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
QFTGR_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
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


def test_master_action_ck_family_status_synthesis_result_review_files_exist() -> None:
    for path in [
        SYNTHESIS_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        SYNTHESIS_LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_master_action_ck_family_status_synthesis_result_review_accepts_synthesis() -> None:
    synthesis = _json(SYNTHESIS_OUT)
    review = _json(DEFAULT_OUT)

    assert synthesis["outcome_id"] == SYNTHESIS_OUTCOME
    assert synthesis["selected_next_target"] == CONSUMED_TARGET

    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_result"] == OUTCOME_ID
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["recommended_selector_choice"] == RECOMMENDED_SELECTOR_CHOICE
    assert review["selector_choices"] == SELECTOR_CHOICES
    assert build_master_action_ck_family_status_synthesis_result_review() == review


def test_master_action_ck_family_status_synthesis_result_review_preserves_acceptance_scope() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["accepted_review_findings_count"] == 5
    assert review["review_criteria_count"] == 11
    assert review["review_criteria_accepted_count"] == 11
    for key in [
        "result_review_prepared",
        "result_review_accepted",
        "synthesis_result_review_prepared",
        "synthesis_result_review_accepted",
        "phi_source_bridge_transport_family_synthesized",
        "A_source_bridge_transport_family_synthesized",
        "psi_A_current_source_exchange_total_conservation_family_synthesized",
        "C_exchange_recognized_as_interaction_exchange_balance_admissibility_rule",
        "all_C_k_families_admissibility_only",
        "all_summarized_rules_admissibility_only",
        "master_action_surface_selector_authorized",
    ]:
        assert review[key] is True, key
    assert review["master_action_surface_selector_executed"] is False
    assert review["master_action_surface_selected"] is False
    assert review["ck_family_gap_review_prepared"] is False
    assert review["C_source_classification"] == C_SOURCE_CLASSIFICATION
    assert review["C_bridge_classification"] == C_BRIDGE_CLASSIFICATION
    assert review["C_transport_classification"] == C_TRANSPORT_CLASSIFICATION
    assert review["C_exchange_classification"] == C_EXCHANGE_CLASSIFICATION
    for token in [
        CURRENT_CANDIDATE,
        CURRENT_CONSERVATION_RESULT,
        SOURCED_GAUGE_ROUTE,
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        C_EXCHANGE_CONSTRAINT_FORM,
        C_EXCHANGE_ADMISSIBILITY_CONDITION,
    ]:
        assert token in review["mathematical_statement"], token


def test_master_action_ck_family_status_synthesis_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
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
        "master_action_surface_selected",
        "master_action_surface_selector_executed",
    ]:
        assert review[key] is False, key
    for phrase in [
        "accepts only that the phi source-bridge-transport family",
        "C_exchange is recognized as an interaction exchange-balance admissibility rule",
        "all C_k families remain admissibility-only",
        "no C_k action embedding",
        "no C_k action variation",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no master-action promotion",
        "working-form, noncanonical, non-promoted organizing surface",
        "full ToeFormal aggregate is kept as NOT_RUN",
    ]:
        assert phrase in review["non_claim_boundary"], phrase
    assert review["aggregate_lean_validation_status_for_review"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert review["full_toeformal_aggregate_status_for_review"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert review["full_toeformal_aggregate_passed"] is False
    assert review["full_toeformal_aggregate_failed"] is False
    assert review["full_toeformal_aggregate_timed_out"] is False


def test_master_action_ck_family_status_synthesis_result_review_rotates_to_selector() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert is_current
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET not in registry["completed_targets"]
    assert NEXT_TARGET not in registry["consumed_targets"]
    assert NEXT_TARGET not in registry["paused_lanes"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == _rel(DEFAULT_OUT)
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["result_token"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["result_review_prepared"] == "yes"
    assert consumed["result_review_accepted"] == "yes"
    assert consumed["master_action_surface_selector_authorized"] == "yes"
    assert consumed["master_action_surface_selector_executed"] == "no"
    assert consumed["master_action_surface_selected"] == "no"

    active_row = _workstream(registry, NEXT_TARGET)
    assert active_row["status"] == "active"
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["active_lane"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["authorization_evidence"] == evidence
    assert active_row["report"] == _rel(DEFAULT_OUT)
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["packet_result"] == "PENDING"
    assert active_row["review_result"] == "PENDING"
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["result_token"] == OUTCOME_ID
    assert active_row["selected_next_target"] == NEXT_TARGET
    assert active_row["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert active_row["recommended_selector_choice"] == RECOMMENDED_SELECTOR_CHOICE
    assert active_row["master_action_surface_selector_authorized"] == "yes"
    assert active_row["master_action_surface_selector_executed"] == "no"
    assert active_row["master_action_surface_selected"] == "no"
    assert active_row["ck_family_gap_review_prepared"] == "no"
    assert active_row["C_k_action_variation_executed"] == "no"
    assert active_row["em_qft_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["gr_qm_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_master_action_ck_family_status_synthesis_result_review_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_PATH,
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
        REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        "MasterActionCKFamilyStatusSynthesisAfterPhiAAndPsiAResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        f"CURRENT_LIVE_NEXT_TARGET_v0: {NEXT_TARGET}",
        f"PREVIOUS_LIVE_NEXT_TARGET_v0: {CONSUMED_TARGET}",
        f"ACTIVE_LANE_v0: {NEXT_TARGET}",
        f"CURRENT_LIVE_TARGET_EVIDENCE_v0: {_rel(LEAN_PACKET_PATH)}",
        f"CURRENT_LIVE_TARGET_REPORT_v0: {_rel(DEFAULT_OUT)}",
        f"CURRENT_LIVE_TARGET_OUTCOME_v0: {OUTCOME_ID}",
        "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUTCOME_v0",
        "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        C_SOURCE_CLASSIFICATION,
        C_BRIDGE_CLASSIFICATION,
        C_TRANSPORT_CLASSIFICATION,
        C_EXCHANGE_CLASSIFICATION,
        RECOMMENDED_SELECTOR_CHOICE,
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no C_k action variation",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_master_action_ck_family_status_synthesis_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_master_action_ck_family_status_synthesis_result_review_gate.py"
    )
