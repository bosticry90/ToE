from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.tests.strict_physics_state_helpers import (
    README_PATH,
    REPO_ROOT,
    STATE_PATH,
    STRICT_MAP_PATH,
    active_workstream,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_forbidden_promotions_closed,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
    loop_registry,
    read_text,
    workstream,
)


SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostQMStatEntropyLogDomainReductionBoundedAttackSelection.lean"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropyLogDomainZeroHandlingReductionResultReview.lean"
)
REDUCTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropyLogDomainZeroHandlingReduction.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_BOUNDED_ATTACK_SELECTION_20260510_v0.json"
)
REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_20260510_v0.json"
)
REDUCTION_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_20260510_v0.json"
)
CURRENT_AUTHORITATIVE_SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)

REPORT_ID = (
    "POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_BOUNDED_ATTACK_SELECTION_20260510_v0"
)
SURFACE_ID = "post_qm_stat_entropy_log_domain_reduction_bounded_attack_selection_v0"
ACTIVE_LANE = "post_qm_stat_entropy_log_domain_reduction_bounded_attack_selection"
PREVIOUS_LANE = "qm_stat_entropy_log_domain_zero_handling_reduction_result_review"
REDUCTION_LANE = "qm_stat_entropy_log_domain_zero_handling_reduction"
SELECTION_TARGET = "select_next_post_qm_stat_entropy_log_domain_reduction_bounded_attack"
CONSUMED_REVIEW_TARGET = "review_qm_stat_entropy_log_domain_zero_handling_reduction_result"
CONSUMED_REVIEW_TOKEN = (
    "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_CONSUMED_LEAN_BACKED"
)
OUTPUT_TOKEN = "POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_NEXT_ATTACK_SELECTED"
SELECTED_TARGET = "prepare_qm_stat_entropy_assumption_reduction_candidate_selection"
ALTERNATE_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
REDUCED_ASSUMPTION = "log_domain_zero_handling_convention_required"
RECOMMENDED_CANDIDATE = "normalization_or_probability_mass_condition_required"
REDUCTION_TOKEN = "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_ASSUMPTION_REDUCED_LEAN_BACKED"
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REDUCTION_EVIDENCE = str(REDUCTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_REPORT_EVIDENCE = str(REVIEW_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
REDUCTION_REPORT_EVIDENCE = str(REDUCTION_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)


def _read(path: Path) -> str:
    return read_text(path)


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_post_qm_stat_entropy_log_domain_reduction_selection_surface_records_target() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        SELECTION_TARGET,
        CONSUMED_REVIEW_TOKEN,
        OUTPUT_TOKEN,
        SELECTED_TARGET,
        ALTERNATE_TARGET,
        RECOMMENDED_CANDIDATE,
        "PostQMStatEntropyLogDomainReductionBoundedAttackSelectionStatus",
        "PostQMStatEntropyLogDomainReductionBoundedAttackSelectionDecision",
        "prepareQMStatEntropyAssumptionReductionCandidateSelection",
        "post_qm_stat_entropy_log_domain_reduction_selection_consumes_live_target_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_consumes_review_token_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_review_consumed_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_local_only_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_remaining_count_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_remaining_active_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_exactly_one_target_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_output_token_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_decision_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_selected_target_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_recommended_candidate_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_candidate_count_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_frontier_target_v0",
    }:
        assert token in text

    assert (
        "import ToeFormal.Derivation.PostQMStatEntropyLogDomainReductionBoundedAttackSelection"
        in aggregate_text
    )


def test_post_qm_stat_entropy_log_domain_reduction_selection_surface_preserves_nonclaims() -> None:
    text = _read(SELECTION_PATH)

    for theorem in {
        "post_qm_stat_entropy_log_domain_reduction_selection_does_not_execute_target_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_no_lean_backed_entropy_semantics_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_supplied_only_preserved_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_no_entropy_theorem_discharge_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_no_qm_stat_completion_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_no_seam_closure_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_no_phase2_readiness_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_no_empirical_adequacy_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_no_canonical_toe_claim_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_master_action_not_promoted_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_qft_gr_not_authorized_v0",
        "post_qm_stat_entropy_log_domain_reduction_selection_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_post_qm_stat_entropy_log_domain_reduction_selection_report_selects_candidate_selection() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_selection_only"
    assert report["current_target"] == SELECTION_TARGET
    assert report["consumed_review_target"] == CONSUMED_REVIEW_TARGET
    assert report["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert report["output_token"] == OUTPUT_TOKEN
    assert report["source_review_surface"] == REVIEW_EVIDENCE
    assert report["source_review_report"] == REVIEW_REPORT_EVIDENCE
    assert report["source_reduction_surface"] == REDUCTION_EVIDENCE
    assert report["source_reduction_report"] == REDUCTION_REPORT_EVIDENCE
    assert report["selection_surface"] == SELECTION_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_post_qm_stat_entropy_log_domain_reduction_bounded_attack_selection_gate.py"
    )
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_TARGET"
    assert report["selection_executes_target"] is False
    assert report["selection_count"] == 1
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selected_decision"] == SELECTED_TARGET
    assert report["recommended_next_candidate"] == RECOMMENDED_CANDIDATE

    selected = [
        row for row in report["candidate_next_targets"] if row["selection"] == "selected"
    ]
    assert len(selected) == 1
    assert selected[0]["target_id"] == SELECTED_TARGET
    assert {row["target_id"] for row in report["candidate_next_targets"]} == {
        SELECTED_TARGET,
        ALTERNATE_TARGET,
    }


def test_post_qm_stat_entropy_log_domain_reduction_selection_report_preserves_review_boundary() -> None:
    report = _json(REPORT_PATH)

    assert report["review_interpretation"] == {
        "log_domain_zero_handling_reduction_result_review_consumed": True,
        "reduced_assumption_class_id": REDUCED_ASSUMPTION,
        "reduced_assumption_authority": "Lean-backed local convention",
        "local_convention_reduction_only": True,
        "remaining_assumption_class_count": 7,
        "remaining_supporting_assumptions_active": True,
        "target_stat_entropy_semantics_theorem_gap_authority": "supplied-only",
        "target_stat_entropy_semantics_lean_backed": False,
        "entropy_semantics_theorem_discharged": False,
    }
    assert report["next_target_expectations"] == {
        "target_id": SELECTED_TARGET,
        "candidate_selection_should_rank_remaining_assumptions": True,
        "candidate_selection_should_select_exactly_one_assumption": True,
        "recommended_candidate": RECOMMENDED_CANDIDATE,
        "selector_executes_selected_target": False,
        "must_preserve_supplied_only_qm_stat_entropy_semantics_boundary": True,
    }
    assert report["nonclaim_boundaries"] == {
        "log_domain_zero_handling_reduction_consumed_as_local_convention_only": True,
        "remaining_supporting_assumptions_active": True,
        "remaining_assumption_class_count": 7,
        "target_stat_entropy_semantics_lean_backed": False,
        "target_stat_entropy_semantics_supplied_only": True,
        "entropy_semantics_theorem_discharged": False,
        "assumption_discharge_claim": False,
        "qm_stat_pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "master_action_promotion_authorized": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET

    for forbidden in {
        "LEAN_BACKED_ENTROPY_SEMANTICS_DISCHARGE",
        "ASSUMPTION_DISCHARGE",
        "THEOREM_GAP_CLOSURE",
        "QM_STAT_PILLAR_COMPLETION",
        "SEAM_CLOSURE",
        "PHASE_2_READINESS",
        "EMPIRICAL_ADEQUACY",
        "CANONICAL_TOE_STATUS",
        "MASTER_ACTION_PROMOTION",
        "QFT_GR_SOURCE_MAP_CLOSURE",
        "SELECTED_TARGET_EXECUTION",
        "GOVERNANCE_MANIFEST_ENROLLMENT",
    }:
        assert forbidden in report["forbidden_effects"]


def test_post_qm_stat_entropy_log_domain_reduction_selection_registry_rotates_to_candidate_selection() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()
    assert_forbidden_promotions_closed()

    payload = loop_registry()
    state = payload["current_target_state"]

    is_current = state["live_next_target"] == SELECTED_TARGET
    if is_current:
        assert state["previous_live_next_target"] == SELECTION_TARGET
        assert state["live_next_target_evidence"] == SELECTION_EVIDENCE
        assert state["active_lane"] == ACTIVE_LANE
    else:
        assert state["live_next_target"] in {
            SELECTED_TARGET,
            "select_next_post_v01_alpha_manifest_enrollment_bounded_attack",
            "review_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result",
            "review_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result",
            "prepare_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate",
            "review_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_result",
            "execute_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate",
            "review_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate_result",
            "prepare_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet",
            "review_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet_result",
            "prepare_v01_alpha_retained_tranche_004_source_map_closure_adjudication_packet",
            "review_v01_alpha_retained_tranche_004_source_map_closure_adjudication_packet_result",
            "review_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_result",
        }
    assert PREVIOUS_LANE in state["paused_lanes"]
    assert REDUCTION_LANE in state["paused_lanes"]

    previous = workstream(PREVIOUS_LANE, payload)
    assert previous["status"] == "paused"
    assert previous["authorized_next_strict_target"] == SELECTION_TARGET
    assert previous["consumed_target"] == CONSUMED_REVIEW_TARGET
    assert previous["authorization_evidence"] == REVIEW_EVIDENCE
    assert previous["review_report"] == REVIEW_REPORT_EVIDENCE
    assert previous["review_token"] == CONSUMED_REVIEW_TOKEN
    assert previous["selected_next_target"] == SELECTION_TARGET
    assert previous["reduced_assumption_class_id"] == REDUCED_ASSUMPTION
    assert previous["remaining_assumption_class_count"] == 7
    assert previous["remaining_supporting_assumptions_active"] == "yes"
    assert previous["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert previous["entropy_semantics_theorem_discharged"] == "no"

    current = active_workstream(payload) if is_current else workstream(ACTIVE_LANE, payload)
    assert current["workstream_id"] == ACTIVE_LANE
    assert current["status"] == ("active" if is_current else "paused")
    assert current["authorization_evidence"] == SELECTION_EVIDENCE
    assert current["authorized_next_strict_target"] == SELECTED_TARGET
    assert current["consumed_target"] == SELECTION_TARGET
    assert current["latest_surface"] == SURFACE_ID
    assert current["selection_report"] == REPORT_EVIDENCE
    assert current["source_review_surface"] == REVIEW_EVIDENCE
    assert current["source_review_report"] == REVIEW_REPORT_EVIDENCE
    assert current["source_reduction_surface"] == REDUCTION_EVIDENCE
    assert current["source_reduction_report"] == REDUCTION_REPORT_EVIDENCE
    assert current["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert current["output_token"] == OUTPUT_TOKEN
    assert current["selected_next_target"] == SELECTED_TARGET
    assert current["selected_decision"] == SELECTED_TARGET
    assert current["recommended_next_candidate"] == RECOMMENDED_CANDIDATE
    assert current["selection_count"] == 1
    assert current["candidate_target_count"] == 2
    assert current["selection_executes_target"] == "no"
    assert current["local_convention_reduction_only"] == "yes"
    assert current["remaining_assumption_class_count"] == 7
    assert current["remaining_supporting_assumptions_active"] == "yes"
    assert current["target_stat_entropy_semantics_lean_backed"] == "no"
    assert current["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert current["entropy_semantics_theorem_discharged"] == "no"
    assert current["assumption_discharge_claim"] == "no"
    assert current["qm_stat_pillar_completion_inferred"] == "no"
    assert current["qft_gr_source_map_closure_authorized"] == "no"
    assert current["seam_closure_claim"] == "no"
    assert current["phase2_readiness_claim"] == "no"
    assert current["empirical_adequacy_claim"] == "no"
    assert current["canonical_toe_claim"] == "no"
    assert current["governance_manifest_enrollment_authorized"] == "no"
    assert current["master_action_promotion_authorized"] == "no"

    assert SELECTED_TARGET in payload["next_strict_target_coverage"]
    assert (
        "post_qm_stat_entropy_log_domain_reduction_bounded_attack_selection_nonclaim_boundary"
        in payload["retained_blocker_coverage"]
    )


def test_post_qm_stat_entropy_log_domain_reduction_selection_public_surfaces_are_synchronized() -> None:
    for path in {
        README_PATH,
        STATE_PATH,
        STRICT_MAP_PATH,
        CURRENT_AUTHORITATIVE_SURFACES_PATH,
    }:
        text = _read(path)
        for token in {
            f"CURRENT_LIVE_NEXT_TARGET_v0: {SELECTED_TARGET}",
            OUTPUT_TOKEN,
            CONSUMED_REVIEW_TOKEN,
            RECOMMENDED_CANDIDATE,
            "seven remaining",
            "supplied-only",
        }:
            assert token in text

    assert_public_surfaces_match_registry()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()


def test_post_qm_stat_entropy_log_domain_reduction_selection_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_post_qm_stat_entropy_log_domain_reduction_bounded_attack_selection_gate.py"
    )
