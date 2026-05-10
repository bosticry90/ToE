from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)


REPO_ROOT = find_repo_root(Path(__file__))
REENTRY_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTheoremGapReentry.lean"
)
SOURCE_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterSampleRep32AxiomAudit.lean"
)
SOURCE_PROBABILITY_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATSourceProbabilityExtractionResultReview.lean"
)
RESIDUAL_PACKAGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QM_STAT_TransportResidualPackage.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_THEOREM_GAP_REENTRY_20260510_v0.json"
)

REPORT_ID = "QM_STAT_THEOREM_GAP_REENTRY_20260510_v0"
SURFACE_ID = "qm_stat_theorem_gap_reentry_v0"
CONSUMED_TARGET = "prepare_qm_stat_theorem_gap_reentry"
CONSUMED_TOKEN = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_SAMPLEREP32_AXIOM_AUDIT"
RESULT_TOKEN = "QM_STAT_THEOREM_GAP_REENTRY_PREPARED"
NEXT_TARGET = "review_qm_stat_theorem_gap_reentry_result"
SELECTED_GAP = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0"
SELECTED_CATEGORY = "entropy_mean_variance_residual_bridge_gap"
SELECTED_OBLIGATION = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_OBLIGATION_v0"
CURRENT_AUTHORITY = (
    "RETAINED_SUPPLIED_TARGET_STAT_ENTROPY_STRUCTURE_REQUIRED_BY_RESIDUAL_PACKAGE"
)
INTENDED_AUTHORITY = (
    "THEOREM_LINKED_TARGET_STAT_ENTROPY_SEMANTICS_DISCHARGE_OR_EXPLICIT_OBSTRUCTION"
)
CANDIDATE_CATEGORIES = {
    "finite_transport_residual_theorem_gap",
    SELECTED_CATEGORY,
    "finite_alignment_assumption_discharge_candidate",
    "qm_stat_source_target_map_admissibility_gap",
    "statistical_closure_obstruction_followup",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_qm_stat_theorem_gap_reentry_consumes_selector_and_selects_one_gap() -> None:
    text = _read(REENTRY_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        NEXT_TARGET,
        SELECTED_GAP,
        SELECTED_CATEGORY,
        SELECTED_OBLIGATION,
        CURRENT_AUTHORITY,
        INTENDED_AUTHORITY,
        "QMStatTheoremGapReentryStatus",
        "QMStatTheoremGapReentryDecision",
        "selectTargetSTATEntropySemanticsGap",
        "qm_stat_theorem_gap_reentry_consumes_live_target_v0",
        "qm_stat_theorem_gap_reentry_consumes_selector_token_v0",
        "qm_stat_theorem_gap_reentry_exactly_one_gap_v0",
        "qm_stat_theorem_gap_reentry_selected_gap_id_v0",
        "qm_stat_theorem_gap_reentry_selected_category_v0",
        "qm_stat_theorem_gap_reentry_selected_obligation_v0",
        "qm_stat_theorem_gap_reentry_current_authority_v0",
        "qm_stat_theorem_gap_reentry_intended_authority_v0",
        "qm_stat_theorem_gap_reentry_candidate_count_v0",
        "qm_stat_theorem_gap_reentry_selected_gap_count_v0",
        "qm_stat_theorem_gap_reentry_result_token_v0",
        "qm_stat_theorem_gap_reentry_selected_next_target_v0",
    } | CANDIDATE_CATEGORIES:
        assert token in text

    assert "import ToeFormal.Derivation.QMStatTheoremGapReentry" in aggregate_text


def test_qm_stat_theorem_gap_reentry_records_source_authority_basis() -> None:
    text = _read(REENTRY_PATH)

    for token in {
        "fullPillarTargetMapNextLaneSelectionAfterSampleRep32AxiomAuditStatusReadoutV0",
        "qmStatSourceProbabilityExtractionResultReviewStatusReadoutV0",
        "qm_stat_theorem_gap_reentry_selector_qm_stat_lane_selected_v0",
        "qm_stat_theorem_gap_reentry_source_selector_bounded_item_ready_v0",
        "qm_stat_theorem_gap_reentry_source_probability_review_completed_v0",
        "qm_stat_theorem_gap_reentry_source_probability_retained_v0",
        "qm_stat_theorem_gap_reentry_prior_target_entropy_not_authorized_v0",
        "qm_stat_theorem_gap_reentry_selected_obligation_matches_protocol_row_v0",
        "phase1BlockerQMSTATTransportResidualPackageRetainedId",
    }:
        assert token in text


def test_qm_stat_theorem_gap_reentry_preserves_nonclaims() -> None:
    text = _read(REENTRY_PATH)

    for token in {
        "qm_stat_theorem_gap_reentry_does_not_execute_discharge_v0",
        "qm_stat_theorem_gap_reentry_target_entropy_selected_v0",
        "qm_stat_theorem_gap_reentry_finite_transport_not_selected_v0",
        "qm_stat_theorem_gap_reentry_finite_alignment_not_selected_v0",
        "qm_stat_theorem_gap_reentry_source_target_map_not_selected_v0",
        "qm_stat_theorem_gap_reentry_statistical_closure_not_selected_v0",
        "qm_stat_theorem_gap_reentry_no_broader_theorem_work_v0",
        "qm_stat_theorem_gap_reentry_no_theorem_gap_discharge_v0",
        "qm_stat_theorem_gap_reentry_no_qm_stat_completion_v0",
        "qm_stat_theorem_gap_reentry_no_seam_closure_v0",
        "qm_stat_theorem_gap_reentry_no_phase2_readiness_v0",
        "qm_stat_theorem_gap_reentry_no_empirical_adequacy_v0",
        "qm_stat_theorem_gap_reentry_no_canonical_toe_claim_v0",
        "qm_stat_theorem_gap_reentry_master_action_not_promoted_v0",
        "qm_stat_theorem_gap_reentry_qft_gr_not_authorized_v0",
        "qm_stat_theorem_gap_reentry_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_qm_stat_theorem_gap_reentry_report_records_selected_gap() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["selected_next_target_kind"] == "qm_stat_theorem_gap_reentry_result_review_only"
    assert report["selection_surface"] == _rel(REENTRY_PATH)
    assert report["source_selector_surface"] == _rel(SOURCE_SELECTOR_PATH)
    assert report["source_probability_result_review_surface"] == _rel(
        SOURCE_PROBABILITY_RESULT_REVIEW_PATH
    )
    assert report["residual_package_surface"] == _rel(RESIDUAL_PACKAGE_PATH)
    assert report["authorized_effect"] == (
        "IDENTIFY_EXACTLY_ONE_BOUNDED_QM_STAT_THEOREM_GAP_ITEM"
    )
    assert report["selection_executes_gap_discharge"] is False
    assert report["selection_count"] == 1
    assert report["candidate_category_count"] == 5

    selected = [row for row in report["candidate_categories"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["category_id"] == SELECTED_CATEGORY
    assert selected[0]["candidate_target"] == SELECTED_GAP
    assert {row["category_id"] for row in report["candidate_categories"]} == CANDIDATE_CATEGORIES

    gap = report["selected_gap"]
    assert gap["gap_id"] == SELECTED_GAP
    assert gap["category_id"] == SELECTED_CATEGORY
    assert gap["selected_obligation_id"] == SELECTED_OBLIGATION
    assert gap["current_authority_level"] == CURRENT_AUTHORITY
    assert gap["intended_stronger_authority"] == INTENDED_AUTHORITY
    assert report["next_action_after_reentry_packet"] == NEXT_TARGET


def test_qm_stat_theorem_gap_reentry_report_preserves_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["reentry_basis"] == {
        "source_selector_selected_lane": "QM_STAT_THEOREM_GAP_RE_ENTRY_LANE",
        "source_selector_selected_target": CONSUMED_TARGET,
        "target_map_row": "FULL_SEAM_QM_STAT_TARGET_MAP_v0",
        "target_map_next_admissible_action": (
            "map_qm_stat_full_probability_entropy_transport_obligations"
        ),
        "source_probability_result_review_completed": True,
        "source_probability_retained_as_supplied": True,
        "target_entropy_semantics_authorized_before_this_packet": False,
        "bounded_item_ready": True,
    }
    assert report["nonclaim_boundaries"] == {
        "selection_executes_gap_discharge": False,
        "target_entropy_gap_selected": True,
        "finite_transport_residual_gap_selected": False,
        "finite_alignment_gap_selected": False,
        "source_target_map_admissibility_gap_selected": False,
        "statistical_closure_followup_selected": False,
        "broader_qm_stat_theorem_work_authorized": False,
        "theorem_gap_discharged": False,
        "qm_stat_pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "master_action_promotion_authorized": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }


def test_qm_stat_theorem_gap_reentry_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_qm_stat_theorem_gap_reentry_gate.py"
    )
