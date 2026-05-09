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
    / "PostMasterActionDependencyAuditBoundedAttackSelection.lean"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionDependencyAuditResultReview.lean"
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
    / "POST_MASTER_ACTION_DEPENDENCY_AUDIT_BOUNDED_ATTACK_SELECTION_20260503_v0.json"
)
REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MASTER_ACTION_DEPENDENCY_AUDIT_RESULT_REVIEW_20260503_v0.json"
)
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
SEAM_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
SEAM_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
)
MATH_PHYSICS_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
)

REPORT_ID = "POST_MASTER_ACTION_DEPENDENCY_AUDIT_BOUNDED_ATTACK_SELECTION_20260503_v0"
SURFACE_ID = "post_master_action_dependency_audit_bounded_attack_selection_v0"
CONSUMED_TARGET = "select_next_post_master_action_dependency_audit_bounded_attack"
CONSUMED_REVIEW_TOKEN = "MASTER_ACTION_DEPENDENCY_AUDIT_RESULT_REVIEW_CONSUMED_NONPROMOTED"
RESULT_TOKEN = "POST_MASTER_ACTION_DEPENDENCY_AUDIT_NEXT_ATTACK_SELECTED"
SELECTED_TARGET = "prepare_master_action_dependency_gap_packet"
FUTURE_GAP_TOKEN = "MASTER_ACTION_DEPENDENCY_GAP_PACKET_PREPARED"
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_REPORT_EVIDENCE = str(REVIEW_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
SOURCE_EVIDENCE = str(SOURCE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
PUBLIC_SURFACE_PATHS = [
    README_PATH,
    STATE_PATH,
    STRICT_MAP_PATH,
    ROADMAP_PATH,
    SEAM_REGISTRY_PATH,
    SEAM_INVENTORY_PATH,
]
CANDIDATE_TARGETS = {
    "return_to_full_pillar_target_map_next_lane_selection",
    "prepare_master_action_dependency_gap_packet",
    "prepare_next_proof_debt_ledger_discharge_item",
    "prepare_qft_gr_witness_search_plan",
    "prepare_sr_cosmo_global_obstruction_followup",
    "prepare_qm_stat_theorem_gap_reentry",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_post_master_action_audit_selector_surface_selects_gap_packet() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_REVIEW_TOKEN,
        RESULT_TOKEN,
        SELECTED_TARGET,
        "PostMasterActionDependencyAuditBoundedAttackSelectionStatus",
        "PostMasterActionDependencyAuditBoundedAttackSelectionDecision",
        "prepareMasterActionDependencyGapPacket",
        "post_master_action_dependency_audit_bounded_attack_selection_consumes_live_target_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_consumes_review_token_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_review_consumed_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_nonpromotional_audit_consumed_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_exactly_one_target_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_output_token_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_decision_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_selected_target_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_matches_review_recommendation_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_candidate_count_v0",
    } | CANDIDATE_TARGETS:
        assert token in text

    assert (
        "import ToeFormal.Derivation.PostMasterActionDependencyAuditBoundedAttackSelection"
        in aggregate_text
    )


def test_selector_surface_preserves_reviewed_posture() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_master_action_dependency_audit_bounded_attack_selection_qft_gr_source_map_not_authorized_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_axiom_count_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_default_nonalias_absent_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_sample_rep32_retained_v0",
        "nonpromotional_dependency_map_audit_consumed",
        "qft_gr_source_map_closure_authorized",
        "real_axiom_count_confirmed",
        "default_nonalias_absent_from_unresolved_axiom_debt",
        "sample_rep32_retained",
    }:
        assert token in text


def test_selector_surface_preserves_selection_only_and_nonclaim_boundaries() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_master_action_dependency_audit_bounded_attack_selection_does_not_execute_target_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_gap_packet_not_prepared_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_qft_gr_witness_not_selected_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_proof_debt_not_selected_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_full_pillar_return_not_selected_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_master_action_not_promoted_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_no_pillar_completion_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_no_seam_closure_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_no_phase2_readiness_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_no_empirical_adequacy_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_no_canonical_toe_claim_v0",
        "post_master_action_dependency_audit_bounded_attack_selection_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_post_master_action_audit_selection_report_records_gap_packet_choice() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_selection_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == SELECTED_TARGET
    assert (
        report["selected_next_target_kind"]
        == "master_action_dependency_gap_packet_preparation_only"
    )
    assert report["selector_surface"] == SELECTION_EVIDENCE
    assert report["source_review_surface"] == REVIEW_EVIDENCE
    assert report["source_review_report"] == REVIEW_REPORT_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/"
        "test_post_master_action_dependency_audit_bounded_attack_selection_gate.py"
    )
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_TARGET"
    assert report["selection_executes_target"] is False
    assert report["gap_packet_prepared"] is False
    assert report["selection_count"] == 1
    assert report["candidate_target_count"] == 6
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET

    selected = [row for row in report["candidate_targets"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["target"] == SELECTED_TARGET
    assert {row["target"] for row in report["candidate_targets"]} == CANDIDATE_TARGETS


def test_selection_report_preserves_posture_and_future_gap_purpose() -> None:
    report = _json(REPORT_PATH)

    assert report["preserved_posture"] == {
        "qft_gr_source_map_closure_authorized": False,
        "real_axiom_count": 60,
        "defaultNonAlias": "absent_from_unresolved_axiom_debt_and_lean_backed",
        "sampleRep32": "retained_spec_backed_axiom",
        "master_action": "candidate_dependency_surface_only",
        "dependency_audit": "nonpromotional_consumed",
    }
    assert report["future_gap_packet_purpose"]["future_result_token"] == FUTURE_GAP_TOKEN
    assert report["future_gap_packet_purpose"]["solves_dependencies"] is False
    assert report["future_gap_packet_purpose"]["promotes_master_action"] is False
    assert set(report["future_gap_packet_purpose"]["expected_gap_classes"]) == {
        "QFT-GR source-map witness chain absent",
        "full pillar closure absent",
        "seam closure absent",
        "empirical adequacy absent",
        "proof debt still present: 60 real axioms",
        "canonical master-action derivation absent",
        "Phase 2 authorization absent",
    }
    assert report["nonclaim_boundaries"] == {
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "governance_manifest_enrollment_authorized": False,
    }


def test_post_master_action_audit_selector_live_ledger_still_matches_60_axioms() -> None:
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


def test_post_master_action_audit_public_surfaces_are_synced() -> None:
    for path in PUBLIC_SURFACE_PATHS:
        text = _read(path)
        assert SELECTION_EVIDENCE in text, f"{path} missing selector surface"
        assert REPORT_EVIDENCE in text, f"{path} missing selector report"
        assert RESULT_TOKEN in text, f"{path} missing result token"
        assert SELECTED_TARGET in text, f"{path} missing selected target"
        assert FUTURE_GAP_TOKEN in text, f"{path} missing future gap token"
        assert "selects exactly one next bounded target" in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert (
        "INV-MATH-POST-MASTER-ACTION-DEPENDENCY-AUDIT-BOUNDED-ATTACK-SELECTION-v0"
        in inventory_text
    )
    assert SELECTION_EVIDENCE in inventory_text
    assert_focused_gate_not_manifest_enrolled(
        "test_post_master_action_dependency_audit_bounded_attack_selection_gate.py"
    )
