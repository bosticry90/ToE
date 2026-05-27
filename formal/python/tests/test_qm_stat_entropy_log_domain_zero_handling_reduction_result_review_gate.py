from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.tests.strict_physics_state_helpers import (
    README_PATH,
    REPO_ROOT,
    STATE_PATH,
    STRICT_MAP_PATH,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_forbidden_promotions_closed,
    assert_frontier_matches_registry,
    assert_historical_target_recorded,
    assert_public_surfaces_match_registry,
    loop_registry,
    read_text,
    workstream,
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
    "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_20260510_v0"
)
SURFACE_ID = "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_v0"
ACTIVE_LANE = "qm_stat_entropy_log_domain_zero_handling_reduction_result_review"
PREVIOUS_LANE = "qm_stat_entropy_log_domain_zero_handling_reduction"
CONSUMED_TARGET = "review_qm_stat_entropy_log_domain_zero_handling_reduction_result"
CONSUMED_TOKEN = (
    "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_ASSUMPTION_REDUCED_LEAN_BACKED"
)
REVIEW_TOKEN = (
    "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_CONSUMED_LEAN_BACKED"
)
SELECTED_TARGET = "select_next_post_qm_stat_entropy_log_domain_reduction_bounded_attack"
REDUCED_ASSUMPTION = "log_domain_zero_handling_convention_required"
RECOMMENDED_CANDIDATE = "normalization_or_probability_mass_condition_required"
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REDUCTION_EVIDENCE = str(REDUCTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REDUCTION_REPORT_EVIDENCE = str(REDUCTION_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
REMAINING_ASSUMPTIONS = {
    "target_entropy_functional_definition_required",
    "statistical_state_domain_semantics_required",
    "normalization_or_probability_mass_condition_required",
    "finite_support_or_summability_condition_required",
    "transport_alignment_relation_required",
    "residual_zero_bridge_condition_required",
    "comparison_target_semantics_required",
}


def _read(path: Path) -> str:
    return read_text(path)


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_qm_stat_entropy_log_domain_zero_handling_reduction_result_review_surface_records_consumption() -> None:
    text = _read(REVIEW_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        REVIEW_TOKEN,
        SELECTED_TARGET,
        REDUCED_ASSUMPTION,
        "QMStatEntropyLogDomainZeroHandlingReductionResultReviewStatus",
        "remainingQMStatEntropySupportingAssumptionClassIdsAfterLogDomainReductionV0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_consumes_live_target_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_consumes_reduction_token_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_token_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_next_target_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_remaining_count_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_frontier_target_v0",
    } | REMAINING_ASSUMPTIONS:
        assert token in text

    assert (
        "import ToeFormal.Derivation.QMStatEntropyLogDomainZeroHandlingReductionResultReview"
        in aggregate_text
    )


def test_qm_stat_entropy_log_domain_zero_handling_reduction_result_review_surface_preserves_nonclaims() -> None:
    text = _read(REVIEW_PATH)

    for theorem in {
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_target_entropy_lean_backed_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_supplied_only_preserved_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_entropy_theorem_discharge_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_qm_stat_completion_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_seam_closure_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_phase2_readiness_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_empirical_adequacy_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_canonical_toe_claim_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_master_action_not_promoted_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_qft_gr_not_authorized_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_qm_stat_entropy_log_domain_zero_handling_reduction_result_review_report_records_review() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["review_status"] == "consumed_lean_backed_local_convention_reduction_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_reduction_token"] == CONSUMED_TOKEN
    assert report["review_token"] == REVIEW_TOKEN
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["source_reduction_surface"] == REDUCTION_EVIDENCE
    assert report["source_reduction_report"] == REDUCTION_REPORT_EVIDENCE
    assert report["review_surface"] == REVIEW_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_qm_stat_entropy_log_domain_zero_handling_reduction_result_review_gate.py"
    )

    interpretation = report["review_interpretation"]
    assert interpretation["reduced_assumption_class_id"] == REDUCED_ASSUMPTION
    assert interpretation["reduced_assumption_authority"] == (
        "Lean-backed local convention"
    )
    assert interpretation["local_convention_reduction_only"] is True
    assert interpretation["target_stat_entropy_semantics_theorem_gap_authority"] == (
        "supplied-only"
    )
    assert interpretation["entropy_semantics_theorem_discharged"] is False

    remaining = report["remaining_supporting_assumptions"]
    assert remaining["remaining_assumption_class_count"] == 7
    assert remaining["remaining_assumption_classes_active"] is True
    assert set(remaining["class_ids"]) == REMAINING_ASSUMPTIONS


def test_qm_stat_entropy_log_domain_zero_handling_reduction_result_review_report_preserves_boundary() -> None:
    report = _json(REPORT_PATH)

    assert report["nonclaim_boundaries"] == {
        "log_domain_zero_handling_reduction_consumed_as_local_convention_only": True,
        "remaining_supporting_assumptions_active": True,
        "target_stat_entropy_semantics_lean_backed": False,
        "target_stat_entropy_semantics_supplied_only": True,
        "entropy_semantics_theorem_discharged": False,
        "qm_stat_pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "master_action_promotion_authorized": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }
    assert report["next_target_expectations"] == {
        "target_id": SELECTED_TARGET,
        "should_select_one_next_bounded_target": True,
        "recommended_candidate": RECOMMENDED_CANDIDATE,
        "alternate_candidate": "return_to_full_pillar_target_map_next_lane_selection",
        "must_not_claim_entropy_semantics_theorem_discharge": True,
        "must_preserve_supplied_only_qm_stat_entropy_semantics_boundary": True,
    }
    assert report["next_action_after_review_packet"] == SELECTED_TARGET
    assert "remaining supporting assumptions remain active" in report[
        "acceptance_condition"
    ]


def test_qm_stat_entropy_log_domain_zero_handling_reduction_result_review_registry_rotates_to_selector() -> None:
    assert_current_target_consistent()
    assert_forbidden_promotions_closed()

    payload = loop_registry()
    state = payload["current_target_state"]
    is_current = assert_historical_target_recorded(
        payload=payload,
        previous_target=CONSUMED_TARGET,
        live_target=SELECTED_TARGET,
        evidence=REVIEW_EVIDENCE,
        lane=ACTIVE_LANE,
    )

    if is_current:
        assert_frontier_matches_registry()
        assert_public_surfaces_match_registry()
        assert state["previous_live_next_target"] == CONSUMED_TARGET
        assert state["live_next_target"] == SELECTED_TARGET
        assert state["live_next_target_evidence"] == REVIEW_EVIDENCE
        assert state["active_lane"] == ACTIVE_LANE
    else:
        assert state["live_next_target"] in {
            "prepare_qm_stat_entropy_assumption_reduction_candidate_selection",
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
            "prepare_qft_gr_operator_domain_assumption_reduction_packet",
            "review_qft_gr_operator_domain_assumption_reduction_packet_result",
        }
        assert state["active_lane"] in {
            "post_qm_stat_entropy_log_domain_reduction_bounded_attack_selection",
            "v01_alpha_governance_manifest_enrollment_result_review",
            "v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet",
            "v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt",
            "v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result_review",
            "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate",
            "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_result_review",
            "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate",
            "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_result_review",
            "v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet",
            "v01_alpha_retained_tranche_004_source_map_authorization_adjudication_result_review",
            "v01_alpha_retained_tranche_004_source_map_closure_adjudication_packet",
            "v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_preparation",
            "qft_gr_covariant_conservation_assumption_reduction_packet_result_review",
            "qft_gr_operator_domain_assumption_reduction_packet_preparation",
        }
    assert PREVIOUS_LANE in state["paused_lanes"]
    assert ACTIVE_LANE in state["paused_lanes"]

    previous = workstream(PREVIOUS_LANE, payload)
    assert previous["status"] == "paused"
    assert previous["authorized_next_strict_target"] == CONSUMED_TARGET
    assert previous["result_token"] == CONSUMED_TOKEN
    assert previous["selected_next_target"] == CONSUMED_TARGET
    assert previous["addressed_assumption_class_id"] == REDUCED_ASSUMPTION
    assert previous["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert previous["entropy_semantics_theorem_discharged"] == "no"

    current = workstream(ACTIVE_LANE, payload)
    assert current["status"] == "paused"
    assert current["workstream_id"] == ACTIVE_LANE
    assert current["authorization_evidence"] == REVIEW_EVIDENCE
    assert current["authorized_next_strict_target"] == SELECTED_TARGET
    assert current["consumed_target"] == CONSUMED_TARGET
    assert current["latest_surface"] == SURFACE_ID
    assert current["source_reduction_surface"] == REDUCTION_EVIDENCE
    assert current["source_reduction_report"] == REDUCTION_REPORT_EVIDENCE
    assert current["review_report"] == REPORT_EVIDENCE
    assert current["consumed_reduction_token"] == CONSUMED_TOKEN
    assert current["review_token"] == REVIEW_TOKEN
    assert current["reduced_assumption_class_id"] == REDUCED_ASSUMPTION
    assert current["reduced_assumption_authority"] == "Lean-backed local convention"
    assert current["local_convention_reduction_only"] == "yes"
    assert current["remaining_assumption_class_count"] == 7
    assert current["remaining_supporting_assumptions_active"] == "yes"
    assert current["selected_next_target"] == SELECTED_TARGET
    assert current["recommended_next_candidate"] == RECOMMENDED_CANDIDATE
    assert current["target_stat_entropy_semantics_lean_backed"] == "no"
    assert current["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert current["entropy_semantics_theorem_discharged"] == "no"
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
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_nonclaim_boundary"
        in payload["retained_blocker_coverage"]
    )


def test_qm_stat_entropy_log_domain_zero_handling_reduction_result_review_public_surfaces_are_synchronized() -> None:
    for path in {
        README_PATH,
        STATE_PATH,
        STRICT_MAP_PATH,
        CURRENT_AUTHORITATIVE_SURFACES_PATH,
    }:
        text = _read(path)
        for token in {
            REVIEW_TOKEN,
            REDUCED_ASSUMPTION,
            "seven remaining",
            "supplied-only",
        }:
            assert token in text

    assert_public_surfaces_match_registry()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()


def test_qm_stat_entropy_log_domain_zero_handling_reduction_result_review_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_qm_stat_entropy_log_domain_zero_handling_reduction_result_review_gate.py"
    )
