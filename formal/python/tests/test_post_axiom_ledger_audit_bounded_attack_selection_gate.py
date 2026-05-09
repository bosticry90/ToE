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
SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostAxiomLedgerAuditBoundedAttackSelection.lean"
)
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
    / "POST_AXIOM_LEDGER_AUDIT_BOUNDED_ATTACK_SELECTION_20260503_v0.json"
)
REVIEW_REPORT_PATH = (
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

REPORT_ID = "POST_AXIOM_LEDGER_AUDIT_BOUNDED_ATTACK_SELECTION_20260503_v0"
SURFACE_ID = "post_axiom_ledger_audit_bounded_attack_selection_v0"
SELECTION_TARGET = "select_next_post_axiom_ledger_audit_bounded_attack"
CONSUMED_REVIEW_TARGET = "review_axiom_ledger_audit_refresh_result"
CONSUMED_REVIEW_TOKEN = (
    "AXIOM_LEDGER_AUDIT_REFRESH_RESULT_REVIEW_CONSUMED_60_REAL_AXIOMS_CONFIRMED"
)
OUTPUT_TOKEN = "POST_AXIOM_LEDGER_AUDIT_NEXT_ATTACK_SELECTED"
SELECTED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
NEXT_DEBT_TARGET = "prepare_next_proof_debt_ledger_discharge_item"
MASTER_ACTION_TARGET = "prepare_master_action_dependency_audit"
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_REPORT_EVIDENCE = str(REVIEW_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
AUDIT_EVIDENCE = str(AUDIT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
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


def test_post_audit_selection_surface_records_exactly_one_target() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        SELECTION_TARGET,
        CONSUMED_REVIEW_TOKEN,
        OUTPUT_TOKEN,
        SELECTED_TARGET,
        NEXT_DEBT_TARGET,
        MASTER_ACTION_TARGET,
        "PostAxiomLedgerAuditBoundedAttackSelectionStatus",
        "PostAxiomLedgerAuditBoundedAttackSelectionDecision",
        "returnToFullPillarTargetMapNextLaneSelection",
        "post_axiom_ledger_audit_bounded_attack_selection_consumes_live_target_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_consumes_review_token_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_review_consumed_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_exactly_one_target_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_output_token_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_decision_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_selected_target_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_matches_review_recommendation_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_candidate_count_v0",
    }:
        assert token in text

    assert (
        "import ToeFormal.Derivation.PostAxiomLedgerAuditBoundedAttackSelection"
        in aggregate_text
    )


def test_post_audit_selection_surface_carries_reviewed_ledger_posture() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_axiom_ledger_audit_bounded_attack_selection_axiom_count_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_no_sorry_or_admit_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_file_count_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_default_nonalias_absent_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_default_nonalias_lean_backed_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_sample_rep32_retained_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_no_stale_61_count_v0",
    }:
        assert token in text


def test_post_audit_selection_surface_preserves_nonclaim_boundaries() -> None:
    text = _read(SELECTION_PATH)

    for theorem in {
        "post_axiom_ledger_audit_bounded_attack_selection_does_not_execute_target_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_no_pillar_completion_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_no_seam_closure_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_no_phase2_readiness_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_no_empirical_adequacy_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_master_action_not_promoted_v0",
        "post_axiom_ledger_audit_bounded_attack_selection_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_post_audit_selection_report_selects_full_pillar_return() -> None:
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
    assert report["audit_surface"] == AUDIT_EVIDENCE
    assert report["audit_report"] == AUDIT_REPORT_EVIDENCE
    assert report["proof_debt_ledger"] == LEDGER_EVIDENCE
    assert report["selection_surface"] == SELECTION_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/"
        "test_post_axiom_ledger_audit_bounded_attack_selection_gate.py"
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
        SELECTED_TARGET,
        MASTER_ACTION_TARGET,
    }

    assert report["ledger_posture"] == {
        "real_axiom_count": 60,
        "real_sorry_or_admit_count": 0,
        "real_axiom_file_count": 15,
        "defaultNonAlias": "absent_from_unresolved_axiom_debt_and_lean_backed",
        "sampleRep32": "retained_spec_backed_axiom",
        "stale_active_61_count_references_remain_cleared": True,
    }
    assert report["next_target_expectations"] == {
        "target_id": SELECTED_TARGET,
        "result_token": "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED",
        "selector_should_choose_from_global_map": True,
        "selector_executes_selected_lane": False,
    }


def test_post_audit_selection_live_ledger_still_matches_60_axiom_posture() -> None:
    ledger_text = _read(LEDGER_PATH)
    source_text = _read(SOURCE_PATH)
    axioms, sorry_or_admit = _lean_surface_debt()
    rows = _ledger_rows()

    assert len(axioms) == 59
    assert len(sorry_or_admit) == 0
    assert len({file for _, file in axioms}) == 14
    assert len(rows) == 59
    assert "real_axiom_count_v0: 59" in ledger_text
    assert "real_sorry_or_admit_count_v0: 0" in ledger_text
    assert "real_axiom_file_count_v0: 14" in ledger_text

    assert "axiom defaultNonAlias" not in source_text
    assert "def defaultNonAlias" in source_text
    assert f"| `defaultNonAlias` | `{SOURCE_EVIDENCE}` |" not in ledger_text
    assert f"| `sampleRep32` | `{SOURCE_EVIDENCE}` |" not in ledger_text


def test_post_audit_selection_report_preserves_nonclaim_boundaries() -> None:
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
        == "The post-audit selector consumes the 60-real-axiom audit review, "
        "selects exactly one next bounded target, preserves the updated ledger "
        "posture, and does not infer pillar completion, seam closure, Phase 2 "
        "readiness, empirical adequacy, or master-action promotion."
    )
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_post_audit_selection_public_surfaces_and_manifest_posture() -> None:
    for path in [README_PATH, STATE_PATH, STRICT_MAP_PATH, ROADMAP_PATH]:
        text = _read(path)
        assert SELECTION_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert OUTPUT_TOKEN in text
        assert SELECTED_TARGET in text

    inventory = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-POST-AXIOM-LEDGER-AUDIT-BOUNDED-ATTACK-SELECTION-v0" in inventory
    assert SELECTION_EVIDENCE in inventory
    assert REPORT_EVIDENCE in inventory
    assert OUTPUT_TOKEN in inventory
    assert SELECTED_TARGET in inventory

    assert_focused_gate_not_manifest_enrolled(
        "test_post_axiom_ledger_audit_bounded_attack_selection_gate.py"
    )
