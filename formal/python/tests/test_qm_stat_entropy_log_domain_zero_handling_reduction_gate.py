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


REDUCTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropyLogDomainZeroHandlingReduction.lean"
)
CANDIDATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropyAssumptionReductionCandidateSelection.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_20260510_v0.json"
)
CANDIDATE_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_20260510_v0.json"
)
CURRENT_AUTHORITATIVE_SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)

REPORT_ID = "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_20260510_v0"
SURFACE_ID = "qm_stat_entropy_log_domain_zero_handling_reduction_v0"
ACTIVE_LANE = "qm_stat_entropy_log_domain_zero_handling_reduction"
PREVIOUS_LANE = "qm_stat_entropy_assumption_reduction_candidate_selection"
CONSUMED_TARGET = "prepare_selected_qm_stat_entropy_assumption_reduction_bounded_attack"
CONSUMED_TOKEN = "QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTED"
RESULT_TOKEN = (
    "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_ASSUMPTION_REDUCED_LEAN_BACKED"
)
FALLBACK_RETAINED_TOKEN = (
    "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_ASSUMPTION_RETAINED_SUPPLIED_ONLY"
)
FALLBACK_REFINED_TOKEN = (
    "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_ASSUMPTION_REFINED_NOT_DISCHARGED"
)
SELECTED_TARGET = "review_qm_stat_entropy_log_domain_zero_handling_reduction_result"
SELECTED_ASSUMPTION = "log_domain_zero_handling_convention_required"
REDUCTION_EVIDENCE = str(REDUCTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
CANDIDATE_EVIDENCE = str(CANDIDATE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
CANDIDATE_REPORT_EVIDENCE = str(CANDIDATE_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)


def _read(path: Path) -> str:
    return read_text(path)


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_qm_stat_entropy_log_domain_zero_handling_reduction_surface_records_convention() -> None:
    text = _read(REDUCTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        FALLBACK_RETAINED_TOKEN,
        FALLBACK_REFINED_TOKEN,
        SELECTED_TARGET,
        SELECTED_ASSUMPTION,
        "QMStatEntropyLogDomainZeroHandlingConvention",
        "QMStatEntropyLogDomainMassCase",
        "qm_stat_entropy_log_domain_positive_case_admitted_v0",
        "qm_stat_entropy_log_domain_zero_case_not_admitted_v0",
        "qm_stat_entropy_log_domain_zero_case_uses_zero_contribution_v0",
        "qm_stat_entropy_log_domain_outside_case_not_admitted_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_consumes_live_target_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_consumes_candidate_token_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_selected_assumption_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_result_token_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_frontier_target_v0",
    }:
        assert token in text

    assert (
        "import ToeFormal.Derivation.QMStatEntropyLogDomainZeroHandlingReduction"
        in aggregate_text
    )


def test_qm_stat_entropy_log_domain_zero_handling_reduction_surface_preserves_nonclaims() -> None:
    text = _read(REDUCTION_PATH)

    for theorem in {
        "qm_stat_entropy_log_domain_zero_handling_reduction_no_target_entropy_lean_backed_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_supplied_only_preserved_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_no_entropy_theorem_discharge_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_no_qm_stat_completion_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_no_seam_closure_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_no_phase2_readiness_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_no_empirical_adequacy_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_no_canonical_toe_claim_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_master_action_not_promoted_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_qft_gr_not_authorized_v0",
        "qm_stat_entropy_log_domain_zero_handling_reduction_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_qm_stat_entropy_log_domain_zero_handling_reduction_report_records_result() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["reduction_status"] == "lean_backed_local_convention_reduction_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_candidate_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["fallback_tokens_not_used"] == [
        FALLBACK_RETAINED_TOKEN,
        FALLBACK_REFINED_TOKEN,
    ]
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["source_candidate_surface"] == CANDIDATE_EVIDENCE
    assert report["source_candidate_report"] == CANDIDATE_REPORT_EVIDENCE
    assert report["reduction_surface"] == REDUCTION_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_qm_stat_entropy_log_domain_zero_handling_reduction_gate.py"
    )

    selected = report["selected_assumption"]
    assert selected["assumption_class_id"] == SELECTED_ASSUMPTION
    assert selected["authority_before_reduction"] == "not yet represented"
    assert selected["authority_after_reduction"] == "Lean-backed local convention"
    assert selected["addressed_assumption_count"] == 1
    assert selected["source_assumption_class_count"] == 8

    convention = report["local_convention"]
    assert convention["positive_probability_case"]["admitted_to_log_domain"] is True
    assert convention["zero_probability_case"]["admitted_to_log_domain"] is False
    assert convention["zero_probability_case"]["uses_zero_contribution"] is True
    assert convention["outside_domain_case"]["admitted_to_log_domain"] is False


def test_qm_stat_entropy_log_domain_zero_handling_reduction_report_preserves_boundary() -> None:
    report = _json(REPORT_PATH)

    assert report["nonclaim_boundaries"] == {
        "only_selected_assumption_addressed": True,
        "log_domain_zero_handling_assumption_reduced_to_lean_backed_local_convention": True,
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
        "should_review_local_convention_reduction_only": True,
        "must_not_claim_entropy_semantics_theorem_discharge": True,
        "must_preserve_supplied_only_qm_stat_entropy_semantics_boundary": True,
        "must_not_reopen_other_assumption_classes": True,
    }
    assert report["next_action_after_reduction_packet"] == SELECTED_TARGET
    assert "addresses only `log_domain_zero_handling_convention_required`" in report[
        "acceptance_condition"
    ]


def test_qm_stat_entropy_log_domain_zero_handling_reduction_registry_rotates_to_review() -> None:
    assert_current_target_consistent()
    assert_forbidden_promotions_closed()

    payload = loop_registry()
    state = payload["current_target_state"]
    is_current = assert_historical_target_recorded(
        payload=payload,
        previous_target=CONSUMED_TARGET,
        live_target=SELECTED_TARGET,
        evidence=REDUCTION_EVIDENCE,
        lane=ACTIVE_LANE,
    )

    if is_current:
        assert_frontier_matches_registry()
        assert_public_surfaces_match_registry()
        assert state["previous_live_next_target"] == CONSUMED_TARGET
        assert state["live_next_target"] == SELECTED_TARGET
        assert state["live_next_target_evidence"] == REDUCTION_EVIDENCE
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
        }
    assert PREVIOUS_LANE in state["paused_lanes"]
    assert ACTIVE_LANE in state["paused_lanes"]

    previous = workstream(PREVIOUS_LANE, payload)
    assert previous["status"] == "paused"
    assert previous["authorized_next_strict_target"] == CONSUMED_TARGET
    assert previous["result_token"] == CONSUMED_TOKEN
    assert previous["selected_next_target"] == CONSUMED_TARGET
    assert previous["selected_assumption_class_id"] == SELECTED_ASSUMPTION
    assert previous["reduction_executed"] == "no"
    assert previous["theorem_gap_discharged"] == "no"

    current = workstream(ACTIVE_LANE, payload)
    assert current["workstream_id"] == ACTIVE_LANE
    assert current["status"] == "paused"
    assert current["authorization_evidence"] == REDUCTION_EVIDENCE
    assert current["authorized_next_strict_target"] == SELECTED_TARGET
    assert current["consumed_target"] == CONSUMED_TARGET
    assert current["latest_surface"] == SURFACE_ID
    assert current["source_candidate_surface"] == CANDIDATE_EVIDENCE
    assert current["source_candidate_report"] == CANDIDATE_REPORT_EVIDENCE
    assert current["reduction_report"] == REPORT_EVIDENCE
    assert current["consumed_candidate_token"] == CONSUMED_TOKEN
    assert current["result_token"] == RESULT_TOKEN
    assert current["addressed_assumption_class_id"] == SELECTED_ASSUMPTION
    assert current["addressed_assumption_count"] == 1
    assert current["source_assumption_class_count"] == 8
    assert current["assumption_authority_after"] == "Lean-backed local convention"
    assert current["positive_probability_case_admitted_to_log_domain"] == "yes"
    assert current["zero_probability_case_admitted_to_log_domain"] == "no"
    assert current["zero_probability_uses_zero_contribution"] == "yes"
    assert current["outside_domain_case_admitted_to_log_domain"] == "no"
    assert current["only_selected_assumption_addressed"] == "yes"
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
        "qm_stat_entropy_log_domain_zero_handling_reduction_nonclaim_boundary"
        in payload["retained_blocker_coverage"]
    )


def test_qm_stat_entropy_log_domain_zero_handling_reduction_public_surfaces_are_synchronized() -> None:
    for path in {
        README_PATH,
        STATE_PATH,
        STRICT_MAP_PATH,
        CURRENT_AUTHORITATIVE_SURFACES_PATH,
    }:
        text = _read(path)
        for token in {
            RESULT_TOKEN,
            SELECTED_ASSUMPTION,
            "Lean-backed local convention",
            "supplied-only",
        }:
            assert token in text

    assert_public_surfaces_match_registry()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()


def test_qm_stat_entropy_log_domain_zero_handling_reduction_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_qm_stat_entropy_log_domain_zero_handling_reduction_gate.py"
    )
