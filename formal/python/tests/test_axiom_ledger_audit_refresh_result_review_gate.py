from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.test_lean_axiom_spec_backed_ledger_gate import (
    _lean_surface_debt,
    _ledger_rows,
)
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
    / "AxiomLedgerAuditRefreshResultReview.lean"
)
AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "AxiomLedgerAuditRefresh.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
SOURCE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "AXIOM_LEDGER_AUDIT_REFRESH_RESULT_REVIEW_20260503_v0.json"
)
AUDIT_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "AXIOM_LEDGER_AUDIT_REFRESH_20260503_v0.json"
)
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MATH_PHYSICS_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
)

REPORT_ID = "AXIOM_LEDGER_AUDIT_REFRESH_RESULT_REVIEW_20260503_v0"
SURFACE_ID = "axiom_ledger_audit_refresh_result_review_v0"
CURRENT_TARGET = "review_axiom_ledger_audit_refresh_result"
CONSUMED_RESULT_TOKEN = "AXIOM_LEDGER_AUDIT_REFRESH_CONFIRMED_60_REAL_AXIOMS"
REVIEW_TOKEN = (
    "AXIOM_LEDGER_AUDIT_REFRESH_RESULT_REVIEW_CONSUMED_60_REAL_AXIOMS_CONFIRMED"
)
NEXT_TARGET = "select_next_post_axiom_ledger_audit_bounded_attack"
RECOMMENDED_SELECTOR_CHOICE = "return_to_full_pillar_target_map_next_lane_selection"
CANDIDATE_SELECTOR_TARGETS = [
    "prepare_next_proof_debt_ledger_discharge_item",
    "return_to_full_pillar_target_map_next_lane_selection",
    "prepare_master_action_dependency_audit",
]
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
AUDIT_EVIDENCE = str(AUDIT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
AUDIT_REPORT_EVIDENCE = str(AUDIT_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
LEDGER_EVIDENCE = str(LEDGER_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_EVIDENCE = str(SOURCE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_result_review_lean_surface_consumes_audit_refresh_result() -> None:
    text = _read(REVIEW_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CURRENT_TARGET,
        CONSUMED_RESULT_TOKEN,
        REVIEW_TOKEN,
        NEXT_TARGET,
        RECOMMENDED_SELECTOR_CHOICE,
        "AxiomLedgerAuditRefreshResultReviewStatus",
        "AxiomLedgerAuditRefreshResultReviewDecision",
        "axiom_ledger_audit_refresh_result_review_consumes_live_target_v0",
        "axiom_ledger_audit_refresh_result_review_consumes_audit_result_v0",
        "axiom_ledger_audit_refresh_result_review_real_axiom_count_v0",
        "axiom_ledger_audit_refresh_result_review_default_nonalias_absent_v0",
        "axiom_ledger_audit_refresh_result_review_sample_rep32_retained_v0",
        "axiom_ledger_audit_refresh_result_review_no_stale_61_count_v0",
        "axiom_ledger_audit_refresh_result_review_token_v0",
        "axiom_ledger_audit_refresh_result_review_selected_next_target_v0",
        "axiom_ledger_audit_refresh_result_review_recommends_full_pillar_map_v0",
        "axiom_ledger_audit_refresh_result_review_selector_choice_not_executed_v0",
    }:
        assert token in text

    assert (
        "import ToeFormal.Derivation.AxiomLedgerAuditRefreshResultReview"
        in aggregate_text
    )


def test_result_review_lean_surface_preserves_nonclaim_boundaries() -> None:
    text = _read(REVIEW_PATH)

    for theorem in {
        "axiom_ledger_audit_refresh_result_review_no_pillar_completion_v0",
        "axiom_ledger_audit_refresh_result_review_no_seam_closure_v0",
        "axiom_ledger_audit_refresh_result_review_no_phase2_readiness_v0",
        "axiom_ledger_audit_refresh_result_review_no_empirical_claim_v0",
        "axiom_ledger_audit_refresh_result_review_master_action_not_promoted_v0",
        "axiom_ledger_audit_refresh_result_review_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_result_review_report_consumes_completed_audit_and_selects_selector() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["review_status"] == "completed_result_consumed"
    assert report["current_target"] == CURRENT_TARGET
    assert report["consumed_result_token"] == CONSUMED_RESULT_TOKEN
    assert report["review_result_token"] == REVIEW_TOKEN
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["review_surface"] == REVIEW_EVIDENCE
    assert report["audit_surface"] == AUDIT_EVIDENCE
    assert report["audit_report"] == AUDIT_REPORT_EVIDENCE
    assert report["proof_debt_ledger"] == LEDGER_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_axiom_ledger_audit_refresh_result_review_gate.py"
    )

    assert report["ledger_posture"] == {
        "real_axiom_count": 60,
        "real_sorry_or_admit_count": 0,
        "real_axiom_file_count": 15,
        "defaultNonAlias": "absent_from_unresolved_axiom_debt_and_lean_backed",
        "sampleRep32": "retained_spec_backed_axiom",
        "active_ledger_state_confirmed": True,
    }
    assert report["review_effect"] == {
        "audit_refresh_result_consumed": True,
        "real_axiom_count_confirmed": True,
        "defaultNonAlias_absent_from_unresolved_axiom_debt": True,
        "defaultNonAlias_lean_backed": True,
        "sampleRep32_honestly_retained": True,
        "stale_active_61_count_references_remain_cleared": True,
        "post_audit_selector_target_selected": True,
    }
    assert report["candidate_selector_targets"] == CANDIDATE_SELECTOR_TARGETS
    assert report["recommended_selector_choice"] == RECOMMENDED_SELECTOR_CHOICE
    assert report["review_executes_selector_choice"] is False
    assert report["next_action_after_result_review"] == NEXT_TARGET


def test_result_review_live_ledger_still_matches_confirmed_60_axiom_posture() -> None:
    ledger_text = _read(LEDGER_PATH)
    source_text = _read(SOURCE_PATH)
    axioms, sorry_or_admit = _lean_surface_debt()
    rows = _ledger_rows()

    assert len(axioms) == 60
    assert len(sorry_or_admit) == 0
    assert len({file for _, file in axioms}) == 15
    assert len(rows) == 60
    assert "real_axiom_count_v0: 60" in ledger_text
    assert "real_sorry_or_admit_count_v0: 0" in ledger_text
    assert "real_axiom_file_count_v0: 15" in ledger_text

    assert "axiom defaultNonAlias" not in source_text
    assert "def defaultNonAlias" in source_text
    assert f"| `defaultNonAlias` | `{SOURCE_EVIDENCE}` |" not in ledger_text
    assert f"| `sampleRep32` | `{SOURCE_EVIDENCE}` | `spec_backed` |" in ledger_text


def test_result_review_report_preserves_nonclaim_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["forbidden_effects"] == [
        "PILLAR_COMPLETION",
        "SEAM_CLOSURE",
        "PHASE_2_READINESS",
        "EMPIRICAL_CLAIM",
        "MASTER_ACTION_PROMOTION",
        "GOVERNANCE_MANIFEST_ENROLLMENT",
    ]
    assert report["nonclaim_boundaries"] == {
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_claim": False,
        "master_action_promotion_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }
    assert "60-real-axiom posture" in report["acceptance_condition"]


def test_result_review_public_surfaces_and_manifest_posture() -> None:
    for path in [README_PATH, STATE_PATH, STRICT_MAP_PATH, ROADMAP_PATH]:
        text = _read(path)
        assert REVIEW_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert REVIEW_TOKEN in text
        assert NEXT_TARGET in text
        assert RECOMMENDED_SELECTOR_CHOICE in text

    inventory = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-AXIOM-LEDGER-AUDIT-REFRESH-RESULT-REVIEW-v0" in inventory
    assert REVIEW_EVIDENCE in inventory
    assert REPORT_EVIDENCE in inventory
    assert REVIEW_TOKEN in inventory
    assert NEXT_TARGET in inventory
    assert RECOMMENDED_SELECTOR_CHOICE in inventory

    assert_focused_gate_not_manifest_enrolled(
        "test_axiom_ledger_audit_refresh_result_review_gate.py"
    )
