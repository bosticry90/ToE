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
from formal.python.tools.master_action_ck_family_gap_review_after_phi_a_and_psi_a_report import (
    DEFAULT_OUT as GAP_REVIEW_OUT,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as GAP_REVIEW_OUTCOME,
)
from formal.python.tools.master_action_ck_family_gap_review_after_phi_a_and_psi_a_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    ARTIFACT_ID,
    BLOCKED_CLAIMS,
    C_BRIDGE_CLASSIFICATION,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CLASSIFICATION,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_SOURCE_CLASSIFICATION,
    C_TRANSPORT_CLASSIFICATION,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    EXPECTED_GAP_LABELS,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAP_REVIEW_INSPECTION_QUESTIONS,
    LEAN_PACKET_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RECOMMENDED_SELECTOR_CHOICE,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    SELECTOR_CHOICES,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    build_master_action_ck_family_gap_review_after_phi_a_and_psi_a_result_review,
)
from formal.python.tools.master_action_surface_selection_after_ck_family_gap_review_report import (
    DEFAULT_OUT as SURFACE_SELECTION_OUT,
    LEAN_PACKET_PATH as SURFACE_SELECTION_LEAN_PACKET_PATH,
    NEXT_TARGET as SURFACE_SELECTION_NEXT_TARGET,
    NEXT_TARGET_KIND as SURFACE_SELECTION_NEXT_TARGET_KIND,
    OUTCOME_ID as SURFACE_SELECTION_OUTCOME,
    SELECTED_FOLLOW_ON_TARGET as SURFACE_SELECTION_FOLLOW_ON_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "master_action_ck_family_gap_review_after_phi_a_and_psi_a_result_review_report.py"
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


def test_master_action_ck_family_gap_review_result_review_files_exist() -> None:
    for path in [
        GAP_REVIEW_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_master_action_ck_family_gap_review_result_review_accepts_gap_review() -> None:
    gap_review = _json(GAP_REVIEW_OUT)
    review = _json(DEFAULT_OUT)

    assert gap_review["outcome_id"] == GAP_REVIEW_OUTCOME
    assert gap_review["selected_next_target"] == CONSUMED_TARGET

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
    assert (
        build_master_action_ck_family_gap_review_after_phi_a_and_psi_a_result_review()
        == review
    )


def test_master_action_ck_family_gap_review_result_review_accepts_open_gaps_only() -> None:
    review = _json(DEFAULT_OUT)
    rows = review["gap_rows"]

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["accepted_review_findings_count"] == 8
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["blocked_claim_count"] == 14
    assert review["review_criteria_count"] == 10
    assert review["review_criteria_accepted_count"] == 10
    assert review["gap_count"] == 8
    assert review["open_gap_count"] == 8
    assert review["closed_gap_count"] == 0
    assert [row["gap_id"] for row in rows] == [f"GAP-{index}" for index in range(1, 9)]
    assert [row["gap_label"] for row in rows] == EXPECTED_GAP_LABELS
    assert all(row["resolution_status"] == "open_indexed_only" for row in rows)
    assert review["gap_review_inspection_questions"] == GAP_REVIEW_INSPECTION_QUESTIONS
    for key in [
        "gap_1_through_gap_8_indexed",
        "all_gaps_remain_open",
        "no_gap_discharged",
        "no_gap_closed",
        "no_rule_promoted",
        "no_C_k_functionalization_occurs",
        "no_C_k_variation_occurs",
        "no_seam_closure_occurs",
        "no_master_action_promotion_occurs",
        "admissibility_to_functionalization_gaps_indexed",
        "rule_family_gaps_indexed",
        "theorem_linkage_gap_indexed",
        "assumption_gap_indexed",
        "functionalization_gap_indexed",
        "variation_gap_indexed",
        "physical_meaning_gap_indexed",
        "interaction_generalization_gap_indexed",
        "seam_closure_gap_indexed",
        "empirical_discriminator_gap_indexed",
    ]:
        assert review[key] is True, key


def test_master_action_ck_family_gap_review_result_review_preserves_context_and_nonclaims() -> None:
    review = _json(DEFAULT_OUT)

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
        "No indexed gap is discharged",
    ]:
        assert token in review["mathematical_statement"], token

    for key in [
        "C_k_action_embedding_claimed",
        "C_k_action_embedding_selected",
        "C_k_action_embedding_authorized",
        "C_k_action_variation_executed",
        "C_k_action_variation_authorized",
        "multiplier_route_selected",
        "multiplier_action_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_claimed",
        "direct_dynamical_law_interpretation_selected",
        "functional_action_embedding_claimed",
        "functionalization_authorized",
        "theorem_linkage_completed",
        "assumption_discharge_completed",
        "gap_review_closes_any_gap",
        "gap_discharged",
        "any_gap_discharged",
        "any_gap_closed",
        "rule_promoted",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "standard_model_derivation_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
        "master_action_promotion",
        "post_review_selector_executed",
        "theorem_linkage_obligation_index_prepared",
        "theorem_linkage_obligation_index_selected",
    ]:
        assert review[key] is False, key
    for phrase in [
        "accepts only that GAP-1 through GAP-8 were indexed and remain open",
        "discharges no gap",
        "promotes no rule",
        "creates no C_k functionalization",
        "executes no C_k variation",
        "closes no seam",
        "no C_k action embedding",
        "no multiplier route",
        "no penalty route",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no empirical validation",
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


def test_master_action_ck_family_gap_review_result_review_rotates_to_selector() -> None:
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
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["result_token"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["result_review_prepared"] == "yes"
    assert consumed["result_review_accepted"] == "yes"
    assert str(consumed["gap_count"]) == "8"
    assert str(consumed["open_gap_count"]) == "8"
    assert str(consumed["closed_gap_count"]) == "0"
    assert consumed["no_gap_discharged"] == "yes"
    assert consumed["no_rule_promoted"] == "yes"
    assert consumed["no_C_k_functionalization_occurs"] == "yes"
    assert consumed["no_C_k_variation_occurs"] == "yes"
    assert consumed["no_seam_closure_occurs"] == "yes"
    assert consumed["master_action_promoted"] == "no"
    assert consumed["theorem_linkage_obligation_index_prepared"] == "no"

    if not is_current:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]

        selector = _workstream(registry, NEXT_TARGET)
        assert selector["status"] == "paused"
        assert selector["authorization_evidence"] == _rel(SURFACE_SELECTION_LEAN_PACKET_PATH)
        assert selector["report"] == _rel(SURFACE_SELECTION_OUT)
        assert selector["selection_result"] == SURFACE_SELECTION_OUTCOME
        assert selector["packet_result"] == SURFACE_SELECTION_OUTCOME
        assert selector["outcome_id"] == SURFACE_SELECTION_OUTCOME
        assert selector["selected_next_target"] == SURFACE_SELECTION_NEXT_TARGET
        assert selector["selected_next_target_kind"] == SURFACE_SELECTION_NEXT_TARGET_KIND
        assert selector["selected_follow_on_target_after_review"] == (
            SURFACE_SELECTION_FOLLOW_ON_TARGET
        )
        assert selector["theorem_linkage_obligation_index_selected"] == "yes"
        assert selector["theorem_linkage_obligation_index_prepared"] == "no"
        assert selector["no_gap_discharged"] == "yes"
        assert selector["no_rule_promoted"] == "yes"
        assert selector["master_action_promoted"] == "no"

        active_review = _workstream(registry, SURFACE_SELECTION_NEXT_TARGET)
        assert active_review["status"] == "active"
        assert active_review["workstream_id"] == SURFACE_SELECTION_NEXT_TARGET
        assert active_review["active_lane"] == SURFACE_SELECTION_NEXT_TARGET
        assert active_review["authorization_evidence"] == _rel(
            SURFACE_SELECTION_LEAN_PACKET_PATH
        )
        assert active_review["report"] == _rel(SURFACE_SELECTION_OUT)
        assert active_review["consumed_target"] == NEXT_TARGET
        assert active_review["packet_result"] == "PENDING"
        assert active_review["review_result"] == "PENDING"
        assert active_review["outcome_id"] == SURFACE_SELECTION_OUTCOME
        assert active_review["selected_next_target"] == SURFACE_SELECTION_NEXT_TARGET
        assert active_review["selected_next_target_kind"] == SURFACE_SELECTION_NEXT_TARGET_KIND
        assert active_review["selected_follow_on_target_after_review"] == (
            SURFACE_SELECTION_FOLLOW_ON_TARGET
        )
        assert active_review["theorem_linkage_obligation_index_selected"] == "yes"
        assert active_review["theorem_linkage_obligation_index_prepared"] == "no"
        assert active_review["master_action_promoted"] == "no"
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
    assert active["recommended_selector_choice"] == RECOMMENDED_SELECTOR_CHOICE
    assert active["post_review_selector_authorized"] == "yes"
    assert active["post_review_selector_executed"] == "no"
    assert active["theorem_linkage_obligation_index_prepared"] == "no"
    assert active["theorem_linkage_obligation_index_selected"] == "no"
    assert active["master_action_surface_selector_executed"] == "no"
    assert active["master_action_surface_selected"] == "no"
    assert active["master_action_promoted"] == "no"


def test_master_action_ck_family_gap_review_result_review_mirrors() -> None:
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
        REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        "MasterActionCKFamilyGapReviewAfterPhiAAndPsiAResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        RECOMMENDED_SELECTOR_CHOICE,
        "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_OUTCOME_v0",
        "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "GAP-1",
        "GAP-8",
        "open_indexed_only",
        "no C_k action embedding",
        "no C_k action variation",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_master_action_ck_family_gap_review_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_master_action_ck_family_gap_review_after_phi_a_and_psi_a_result_review_gate.py"
    )
