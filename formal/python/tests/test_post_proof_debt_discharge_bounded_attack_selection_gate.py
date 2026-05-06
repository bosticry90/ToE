from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)


REPO_ROOT = find_repo_root(Path(__file__))
SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostProofDebtDischargeBoundedAttackSelection.lean"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01DischargeResultReview.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_PROOF_DEBT_DISCHARGE_BOUNDED_ATTACK_SELECTION_20260503_v0.json"
)
REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROOF_DEBT_DISCHARGE_FNREP_NONALIAS_RESULT_REVIEW_20260503_v0.json"
)

SURFACE_ID = "post_proof_debt_discharge_bounded_attack_selection_v0"
SELECTION_TARGET = "select_next_post_proof_debt_discharge_bounded_attack"
CONSUMED_REVIEW_TARGET = "review_fnrep_nonalias_default_nonalias_discharge_result"
CONSUMED_REVIEW_TOKEN = (
    "FNREP_NONALIAS_DEFAULT_NONALIAS_DISCHARGE_RESULT_REVIEW_CONSUMED_LEAN_BACKED"
)
OUTPUT_TOKEN = "POST_PROOF_DEBT_DISCHARGE_NEXT_ATTACK_SELECTED"
SELECTED_TARGET = "prepare_axiom_ledger_audit_refresh"
NEXT_DEBT_TARGET = "prepare_next_proof_debt_ledger_discharge_item"
FULL_PILLAR_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
AUDIT_REFRESH_TOKEN = "AXIOM_LEDGER_AUDIT_REFRESH_PREPARED"
REPORT_ID = "POST_PROOF_DEBT_DISCHARGE_BOUNDED_ATTACK_SELECTION_20260503_v0"
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_REPORT_EVIDENCE = str(REVIEW_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_post_discharge_selection_surface_records_exactly_one_target() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        SURFACE_ID,
        SELECTION_TARGET,
        CONSUMED_REVIEW_TOKEN,
        OUTPUT_TOKEN,
        SELECTED_TARGET,
        NEXT_DEBT_TARGET,
        FULL_PILLAR_TARGET,
        "PostProofDebtDischargeBoundedAttackSelectionStatus",
        "PostProofDebtDischargeBoundedAttackSelectionDecision",
        "prepareAxiomLedgerAuditRefresh",
        "post_proof_debt_discharge_bounded_attack_selection_consumes_live_target_v0",
        "post_proof_debt_discharge_bounded_attack_selection_consumes_review_token_v0",
        "post_proof_debt_discharge_bounded_attack_selection_review_consumed_v0",
        "post_proof_debt_discharge_bounded_attack_selection_exactly_one_target_v0",
        "post_proof_debt_discharge_bounded_attack_selection_output_token_v0",
        "post_proof_debt_discharge_bounded_attack_selection_decision_v0",
        "post_proof_debt_discharge_bounded_attack_selection_selected_target_v0",
        "post_proof_debt_discharge_bounded_attack_selection_matches_review_recommendation_v0",
        "post_proof_debt_discharge_bounded_attack_selection_candidate_count_v0",
    }:
        assert token in text


def test_post_discharge_selection_surface_carries_reviewed_ledger_posture() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_proof_debt_discharge_bounded_attack_selection_default_nonalias_lean_backed_v0",
        "post_proof_debt_discharge_bounded_attack_selection_default_nonalias_axiom_removed_v0",
        "post_proof_debt_discharge_bounded_attack_selection_axiom_count_v0",
        "post_proof_debt_discharge_bounded_attack_selection_sample_rep32_retained_v0",
        "real_axiom_count_after_discharge := 60",
        "sample_rep32_retained",
    }:
        assert token in text


def test_post_discharge_selection_surface_preserves_nonclaim_boundaries() -> None:
    text = _read(SELECTION_PATH)

    for theorem in {
        "post_proof_debt_discharge_bounded_attack_selection_does_not_execute_target_v0",
        "post_proof_debt_discharge_bounded_attack_selection_no_pillar_completion_v0",
        "post_proof_debt_discharge_bounded_attack_selection_no_seam_closure_v0",
        "post_proof_debt_discharge_bounded_attack_selection_no_phase2_readiness_v0",
        "post_proof_debt_discharge_bounded_attack_selection_no_empirical_adequacy_v0",
        "post_proof_debt_discharge_bounded_attack_selection_master_action_not_promoted_v0",
        "post_proof_debt_discharge_bounded_attack_selection_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_post_discharge_selection_report_selects_audit_refresh() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_selection_only"
    assert report["current_target"] == SELECTION_TARGET
    assert report["consumed_review_target"] == CONSUMED_REVIEW_TARGET
    assert report["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert report["output_token"] == OUTPUT_TOKEN
    assert report["review_surface"] == REVIEW_EVIDENCE
    assert report["review_report"] == REVIEW_REPORT_EVIDENCE
    assert report["selection_surface"] == SELECTION_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/"
        "test_post_proof_debt_discharge_bounded_attack_selection_gate.py"
    )
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_TARGET"
    assert report["selection_executes_target"] is False
    assert report["selection_count"] == 1
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selected_decision"] == SELECTED_TARGET

    selected = [
        row for row in report["candidate_next_targets"] if row["selection"] == "selected"
    ]
    assert len(selected) == 1
    assert selected[0]["target_id"] == SELECTED_TARGET
    assert {row["target_id"] for row in report["candidate_next_targets"]} == {
        NEXT_DEBT_TARGET,
        FULL_PILLAR_TARGET,
        SELECTED_TARGET,
    }

    authority = report["authority_posture"]
    assert authority == {
        "defaultNonAlias": "LEAN_BACKED_DEFINITION_AND_THEOREM",
        "sampleRep32": "RETAINED_SPEC_BACKED_AXIOM",
        "real_axiom_count": 60,
    }


def test_post_discharge_selection_report_defers_audit_refresh_result() -> None:
    report = _json(REPORT_PATH)
    expectations = report["audit_refresh_target_expectations"]

    assert expectations == {
        "result_token": AUDIT_REFRESH_TOKEN,
        "real_axiom_count": 60,
        "defaultNonAlias_absent_from_axiom_ledger": True,
        "sampleRep32_retained_with_correct_authority_status": True,
        "recent_discharge_result_referenced": True,
        "no_stale_61_count_references_in_active_docs_or_gates": True,
    }
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_post_discharge_selection_report_preserves_nonclaim_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["forbidden_effects"] == [
        "PILLAR_COMPLETION",
        "SEAM_CLOSURE",
        "PHASE_2_READINESS",
        "EMPIRICAL_ADEQUACY",
        "MASTER_ACTION_PROMOTION",
        "SELECTED_TARGET_EXECUTION",
    ]
    assert report["nonclaim_boundaries"] == {
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "master_action_promotion_authorized": False,
        "governance_manifest_enrollment_authorized": False,
        "selection_executes_target": False,
    }
    assert (
        report["acceptance_condition"]
        == "The selector consumes the FNRep discharge result review, selects exactly "
        "one next bounded target, and does not infer pillar completion, seam closure, "
        "Phase 2 readiness, empirical adequacy, or master-action promotion."
    )


def test_post_discharge_selection_gate_is_not_governance_manifest_enrolled() -> None:
    assert REPORT_EVIDENCE.endswith(
        "POST_PROOF_DEBT_DISCHARGE_BOUNDED_ATTACK_SELECTION_20260503_v0.json"
    )
    assert_focused_gate_not_manifest_enrolled(
        "test_post_proof_debt_discharge_bounded_attack_selection_gate.py"
    )
