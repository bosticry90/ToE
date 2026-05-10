from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)


REPO_ROOT = find_repo_root(Path(__file__))
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTheoremGapReentryResultReview.lean"
)
REENTRY_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTheoremGapReentry.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_THEOREM_GAP_REENTRY_RESULT_REVIEW_20260510_v0.json"
)

REPORT_ID = "QM_STAT_THEOREM_GAP_REENTRY_RESULT_REVIEW_20260510_v0"
SURFACE_ID = "qm_stat_theorem_gap_reentry_result_review_v0"
CONSUMED_TARGET = "review_qm_stat_theorem_gap_reentry_result"
CONSUMED_TOKEN = "QM_STAT_THEOREM_GAP_REENTRY_PREPARED"
REVIEW_TOKEN = "QM_STAT_THEOREM_GAP_REENTRY_RESULT_REVIEW_CONSUMED"
NEXT_TARGET = "prepare_qm_stat_target_stat_entropy_semantics_theorem_gap_bounded_attack"
SELECTED_GAP = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0"
SELECTED_OBLIGATION = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_OBLIGATION_v0"
CURRENT_AUTHORITY = (
    "RETAINED_SUPPLIED_TARGET_STAT_ENTROPY_STRUCTURE_REQUIRED_BY_RESIDUAL_PACKAGE"
)
INTENDED_AUTHORITY = (
    "THEOREM_LINKED_TARGET_STAT_ENTROPY_SEMANTICS_DISCHARGE_OR_EXPLICIT_OBSTRUCTION"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_qm_stat_theorem_gap_reentry_result_review_consumes_prepared_packet() -> None:
    text = _read(REVIEW_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        REVIEW_TOKEN,
        NEXT_TARGET,
        SELECTED_GAP,
        SELECTED_OBLIGATION,
        CURRENT_AUTHORITY,
        INTENDED_AUTHORITY,
        "QMStatTheoremGapReentryResultReviewStatus",
        "QMStatTheoremGapReentryResultReviewDecision",
        "authorizeTargetSTATEntropySemanticsBoundedAttackPreparation",
        "qm_stat_theorem_gap_reentry_result_review_consumes_live_target_v0",
        "qm_stat_theorem_gap_reentry_result_review_consumes_prepared_token_v0",
        "qm_stat_theorem_gap_reentry_result_review_token_v0",
        "qm_stat_theorem_gap_reentry_result_review_prepared_gap_available_v0",
        "qm_stat_theorem_gap_reentry_result_review_exactly_one_gap_v0",
        "qm_stat_theorem_gap_reentry_result_review_selected_decision_v0",
        "qm_stat_theorem_gap_reentry_result_review_selected_gap_id_v0",
        "qm_stat_theorem_gap_reentry_result_review_selected_obligation_v0",
        "qm_stat_theorem_gap_reentry_result_review_current_authority_v0",
        "qm_stat_theorem_gap_reentry_result_review_intended_authority_v0",
        "qm_stat_theorem_gap_reentry_result_review_selected_gap_count_v0",
        "qm_stat_theorem_gap_reentry_result_review_selected_next_target_v0",
    }:
        assert token in text

    assert "import ToeFormal.Derivation.QMStatTheoremGapReentryResultReview" in aggregate_text


def test_qm_stat_theorem_gap_reentry_result_review_authorizes_only_preparation() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        "qm_stat_theorem_gap_reentry_result_review_authorizes_bounded_attack_preparation_v0",
        "qm_stat_theorem_gap_reentry_result_review_frontier_target_v0",
        "qm_stat_theorem_gap_reentry_result_review_does_not_execute_attack_v0",
        "qm_stat_theorem_gap_reentry_result_review_no_entropy_theorem_claim_v0",
        "qm_stat_theorem_gap_reentry_result_review_no_gap_discharge_v0",
        "qm_stat_theorem_gap_reentry_result_review_no_qm_stat_completion_v0",
        "qm_stat_theorem_gap_reentry_result_review_no_seam_closure_v0",
        "qm_stat_theorem_gap_reentry_result_review_no_phase2_readiness_v0",
        "qm_stat_theorem_gap_reentry_result_review_no_empirical_adequacy_v0",
        "qm_stat_theorem_gap_reentry_result_review_no_canonical_toe_claim_v0",
        "qm_stat_theorem_gap_reentry_result_review_master_action_not_promoted_v0",
        "qm_stat_theorem_gap_reentry_result_review_qft_gr_not_authorized_v0",
        "qm_stat_theorem_gap_reentry_result_review_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_qm_stat_theorem_gap_reentry_result_review_report_records_handoff() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_result_token"] == CONSUMED_TOKEN
    assert report["review_token"] == REVIEW_TOKEN
    assert report["selected_next_target"] == NEXT_TARGET
    assert (
        report["selected_next_target_kind"]
        == "qm_stat_target_stat_entropy_semantics_bounded_attack_preparation_only"
    )
    assert report["review_surface"] == _rel(REVIEW_PATH)
    assert report["source_reentry_surface"] == _rel(REENTRY_PATH)
    assert report["authorized_effect"] == (
        "AUTHORIZE_PREPARATION_ONLY_FOR_SELECTED_QM_STAT_THEOREM_GAP_BOUNDED_ATTACK"
    )
    assert report["review_executes_bounded_attack"] is False
    assert report["selected_gap_count"] == 1

    gap = report["selected_gap"]
    assert gap["gap_id"] == SELECTED_GAP
    assert gap["selected_obligation_id"] == SELECTED_OBLIGATION
    assert gap["current_authority_level"] == CURRENT_AUTHORITY
    assert gap["intended_stronger_authority"] == INTENDED_AUTHORITY
    assert report["next_action_after_result_review"] == NEXT_TARGET


def test_qm_stat_theorem_gap_reentry_result_review_report_preserves_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["review_basis"] == {
        "prepared_packet_result_token": CONSUMED_TOKEN,
        "prepared_packet_selected_gap": SELECTED_GAP,
        "prepared_packet_selected_obligation": SELECTED_OBLIGATION,
        "exactly_one_theorem_gap_remains_selected": True,
        "entropy_semantics_theorem_claimed": False,
        "theorem_gap_discharged": False,
    }
    assert report["nonclaim_boundaries"] == {
        "review_executes_bounded_attack": False,
        "entropy_semantics_theorem_claimed": False,
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


def test_qm_stat_theorem_gap_reentry_result_review_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_qm_stat_theorem_gap_reentry_result_review_gate.py"
    )
