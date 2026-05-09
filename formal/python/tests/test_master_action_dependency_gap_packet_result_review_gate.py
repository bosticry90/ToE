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
    / "MasterActionDependencyGapPacketResultReview.lean"
)
GAP_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionDependencyGapPacket.lean"
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
    / "MASTER_ACTION_DEPENDENCY_GAP_PACKET_RESULT_REVIEW_20260503_v0.json"
)
GAP_PACKET_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MASTER_ACTION_DEPENDENCY_GAP_PACKET_20260503_v0.json"
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

REPORT_ID = "MASTER_ACTION_DEPENDENCY_GAP_PACKET_RESULT_REVIEW_20260503_v0"
SURFACE_ID = "master_action_dependency_gap_packet_result_review_v0"
CONSUMED_TARGET = "review_master_action_dependency_gap_packet_result"
CONSUMED_RESULT_TOKEN = "MASTER_ACTION_DEPENDENCY_GAP_PACKET_PREPARED"
REVIEW_TOKEN = "MASTER_ACTION_DEPENDENCY_GAP_PACKET_RESULT_REVIEW_CONSUMED_NONPROMOTED"
SELECTED_TARGET = "select_next_post_master_action_gap_packet_bounded_attack"
RECOMMENDED_SELECTOR_CHOICE = "return_to_full_pillar_target_map_next_lane_selection"
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
GAP_PACKET_EVIDENCE = str(GAP_PACKET_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
GAP_PACKET_REPORT_EVIDENCE = str(GAP_PACKET_REPORT_PATH.relative_to(REPO_ROOT)).replace(
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
    "prepare_next_proof_debt_ledger_discharge_item",
    "prepare_qm_stat_theorem_gap_reentry",
    "prepare_sr_cosmo_global_obstruction_followup",
    "prepare_qft_gr_witness_search_plan",
    "prepare_master_action_dependency_gap_reduction_plan",
}
REQUIRED_GAP_LABELS = {
    "QFT-GR source-map witness chain absent",
    "QFT-GR source-map closure unauthorized",
    "full pillar completion absent",
    "global seam closure absent",
    "Phase 2 authorization absent",
    "canonical master-action derivation absent",
    "empirical adequacy absent",
    "remaining proof debt: 60 real axioms",
    "sampleRep32 retained",
    "defaultNonAlias discharged and no longer unresolved debt",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_gap_packet_result_review_surface_records_consumption() -> None:
    text = _read(REVIEW_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_RESULT_TOKEN,
        REVIEW_TOKEN,
        SELECTED_TARGET,
        RECOMMENDED_SELECTOR_CHOICE,
        "MasterActionDependencyGapPacketResultReviewStatus",
        "MasterActionDependencyGapPacketResultReviewDecision",
        "consumeGapPacketAndSelectPostGapSelector",
        "master_action_dependency_gap_packet_result_review_consumes_live_target_v0",
        "master_action_dependency_gap_packet_result_review_consumes_result_token_v0",
        "master_action_dependency_gap_packet_result_review_completed_v0",
        "master_action_dependency_gap_packet_result_review_consumes_gap_packet_v0",
        "master_action_dependency_gap_packet_result_review_consumes_nonpromotional_gap_map_v0",
        "master_action_dependency_gap_packet_result_review_blockers_remain_active_v0",
    } | CANDIDATE_TARGETS | REQUIRED_GAP_LABELS:
        assert token in text

    assert (
        "import ToeFormal.Derivation.MasterActionDependencyGapPacketResultReview"
        in aggregate_text
    )


def test_gap_packet_result_review_preserves_blockers_and_60_axiom_posture() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        "master_action_dependency_gap_packet_result_review_gap_class_count_v0",
        "master_action_dependency_gap_packet_result_review_qft_gr_witness_chain_absent_v0",
        "master_action_dependency_gap_packet_result_review_qft_gr_source_map_not_authorized_v0",
        "master_action_dependency_gap_packet_result_review_full_pillar_completion_absent_v0",
        "master_action_dependency_gap_packet_result_review_global_seam_closure_absent_v0",
        "master_action_dependency_gap_packet_result_review_phase2_authorization_absent_v0",
        "master_action_dependency_gap_packet_result_review_canonical_derivation_absent_v0",
        "master_action_dependency_gap_packet_result_review_empirical_adequacy_absent_v0",
        "master_action_dependency_gap_packet_result_review_axiom_count_v0",
        "master_action_dependency_gap_packet_result_review_default_nonalias_absent_v0",
        "master_action_dependency_gap_packet_result_review_sample_rep32_retained_v0",
        "listed_missing_dependencies_remain_active_blockers",
        "real_axiom_count_confirmed",
        "default_nonalias_absent_from_unresolved_axiom_debt",
        "sample_rep32_retained",
    }:
        assert token in text


def test_gap_packet_result_review_records_selector_rotation_without_execution() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        "master_action_dependency_gap_packet_result_review_token_v0",
        "master_action_dependency_gap_packet_result_review_selected_next_target_v0",
        "master_action_dependency_gap_packet_result_review_decision_v0",
        "master_action_dependency_gap_packet_result_review_candidate_targets_v0",
        "master_action_dependency_gap_packet_result_review_candidate_count_v0",
        "master_action_dependency_gap_packet_result_review_recommends_full_pillar_map_v0",
        "master_action_dependency_gap_packet_result_review_selector_choice_not_executed_v0",
        "master_action_dependency_gap_packet_result_review_gap_reduction_plan_not_prepared_v0",
    }:
        assert token in text


def test_gap_packet_result_review_surface_preserves_nonclaim_boundaries() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        "master_action_dependency_gap_packet_result_review_master_action_not_promoted_v0",
        "master_action_dependency_gap_packet_result_review_no_pillar_completion_v0",
        "master_action_dependency_gap_packet_result_review_no_seam_closure_v0",
        "master_action_dependency_gap_packet_result_review_no_phase2_readiness_v0",
        "master_action_dependency_gap_packet_result_review_no_empirical_adequacy_v0",
        "master_action_dependency_gap_packet_result_review_no_canonical_toe_claim_v0",
        "master_action_dependency_gap_packet_result_review_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_gap_packet_result_review_report_records_review_and_selector_rotation() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["review_status"] == "completed_nonpromotional_gap_map_consumption"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_result_token"] == CONSUMED_RESULT_TOKEN
    assert report["review_token"] == REVIEW_TOKEN
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["recommended_selector_choice"] == RECOMMENDED_SELECTOR_CHOICE
    assert report["review_surface"] == REVIEW_EVIDENCE
    assert report["gap_packet_surface"] == GAP_PACKET_EVIDENCE
    assert report["gap_packet_report"] == GAP_PACKET_REPORT_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_master_action_dependency_gap_packet_result_review_gate.py"
    )
    assert report["authorized_effect"] == "RESULT_REVIEW_AND_SELECTOR_ROTATION_ONLY"
    assert report["next_action_after_review"] == SELECTED_TARGET

    findings = report["review_findings"]
    assert findings["gap_packet_result_consumed"] is True
    assert findings["nonpromotional_dependency_gap_map_consumed"] is True
    assert findings["listed_missing_dependencies_remain_active_blockers"] is True
    assert findings["qft_gr_source_map_witness_chain_absent"] is True
    assert findings["qft_gr_source_map_closure_authorized"] is False
    assert findings["real_axiom_count_confirmed"] == 60
    assert findings["defaultNonAlias_removed_from_unresolved_axiom_debt"] is True
    assert findings["sampleRep32_retained"] is True
    assert findings["selector_choice_executed"] is False
    assert findings["gap_reduction_plan_prepared"] is False

    selected = [
        row for row in report["candidate_selector_targets"] if row["recommendation"] == "recommended"
    ]
    assert len(selected) == 1
    assert selected[0]["target"] == RECOMMENDED_SELECTOR_CHOICE
    assert {row["target"] for row in report["candidate_selector_targets"]} == CANDIDATE_TARGETS


def test_gap_packet_result_review_report_preserves_blockers_posture_and_nonclaims() -> None:
    report = _json(REPORT_PATH)

    assert {row["label"] for row in report["gap_blockers"]} == REQUIRED_GAP_LABELS
    assert len(report["gap_blockers"]) == 10
    assert all(
        row["status"] in {"active_blocker", "retained_active_blocker", "retained", "discharged_not_unresolved"}
        for row in report["gap_blockers"]
    )
    assert report["preserved_posture"] == {
        "qft_gr": "ladder_only_closure_not_authorized",
        "qft_gr_source_map_witness_chain_absent": True,
        "qft_gr_source_map_closure_authorized": False,
        "real_axiom_count": 60,
        "defaultNonAlias": "absent_from_unresolved_axiom_debt_and_lean_backed",
        "sampleRep32": "retained_spec_backed_axiom",
        "master_action": "candidate_dependency_surface_only",
        "gap_map_interpretation": "nonpromotional_dependency_gap_map",
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


def test_gap_packet_result_review_live_ledger_still_matches_60_axioms() -> None:
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


def test_gap_packet_result_review_public_surfaces_are_synced() -> None:
    for path in PUBLIC_SURFACE_PATHS:
        text = _read(path)
        assert REVIEW_EVIDENCE in text, f"{path} missing review surface"
        assert REPORT_EVIDENCE in text, f"{path} missing review report"
        assert REVIEW_TOKEN in text, f"{path} missing review token"
        assert SELECTED_TARGET in text, f"{path} missing next target"
        assert RECOMMENDED_SELECTOR_CHOICE in text, f"{path} missing recommendation"
        assert "non-promotional dependency-gap map" in text
        assert "remain active blockers" in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-MASTER-ACTION-DEPENDENCY-GAP-PACKET-RESULT-REVIEW-v0" in inventory_text
    assert REVIEW_EVIDENCE in inventory_text
    assert_focused_gate_not_manifest_enrolled(
        "test_master_action_dependency_gap_packet_result_review_gate.py"
    )
