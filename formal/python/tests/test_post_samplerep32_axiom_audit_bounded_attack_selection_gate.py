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
from formal.python.tests.test_lean_axiom_spec_backed_ledger_gate import (
    _lean_surface_debt,
    _ledger_rows,
)


SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostSampleRep32AxiomAuditBoundedAttackSelection.lean"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "AxiomLedgerAuditRefreshAfterSampleRep32ResultReview.lean"
)
AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "AxiomLedgerAuditRefreshAfterSampleRep32.lean"
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
    / "POST_SAMPLEREP32_AXIOM_AUDIT_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
)
REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_20260505_v0.json"
)
AUDIT_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_20260505_v0.json"
)
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
CURRENT_AUTHORITATIVE_SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)

REPORT_ID = "POST_SAMPLEREP32_AXIOM_AUDIT_BOUNDED_ATTACK_SELECTION_20260505_v0"
SURFACE_ID = "post_samplerep32_axiom_audit_bounded_attack_selection_v0"
ACTIVE_LANE = "post_samplerep32_axiom_audit_bounded_attack_selection"
PREVIOUS_WORKSTREAM = "axiom_ledger_audit_refresh_after_samplerep32_result_review"
SELECTION_TARGET = "select_next_post_samplerep32_axiom_audit_bounded_attack"
CONSUMED_REVIEW_TARGET = "review_axiom_ledger_audit_refresh_after_samplerep32_result"
CONSUMED_REVIEW_TOKEN = (
    "AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_CONSUMED_59_REAL_AXIOMS_CONFIRMED"
)
OUTPUT_TOKEN = "POST_SAMPLEREP32_AXIOM_AUDIT_NEXT_ATTACK_SELECTED"
SELECTED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
NEXT_DEBT_TARGET = "prepare_next_proof_debt_ledger_discharge_item"
MASTER_ACTION_TARGET = "prepare_master_action_dependency_audit"
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
AUDIT_EVIDENCE = str(AUDIT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_REPORT_EVIDENCE = str(REVIEW_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
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


def test_post_samplerep32_axiom_audit_selection_surface_records_exactly_one_target() -> None:
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
        "PostSampleRep32AxiomAuditBoundedAttackSelectionStatus",
        "PostSampleRep32AxiomAuditBoundedAttackSelectionDecision",
        "returnToFullPillarTargetMapNextLaneSelection",
        "post_samplerep32_axiom_audit_bounded_attack_selection_consumes_live_target_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_consumes_review_token_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_review_consumed_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_exactly_one_target_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_output_token_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_decision_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_selected_target_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_matches_review_recommendation_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_candidate_count_v0",
    }:
        assert token in text

    assert (
        "import ToeFormal.Derivation.PostSampleRep32AxiomAuditBoundedAttackSelection"
        in aggregate_text
    )


def test_post_samplerep32_axiom_audit_selection_surface_carries_59_axiom_posture() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_samplerep32_axiom_audit_bounded_attack_selection_axiom_count_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_no_sorry_or_admit_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_file_count_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_default_nonalias_absent_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_default_nonalias_lean_backed_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_sample_rep32_absent_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_sample_rep32_lean_backed_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_prior_60_historical_only_v0",
    }:
        assert token in text


def test_post_samplerep32_axiom_audit_selection_surface_preserves_nonclaims() -> None:
    text = _read(SELECTION_PATH)

    for theorem in {
        "post_samplerep32_axiom_audit_bounded_attack_selection_does_not_execute_target_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_no_pillar_completion_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_no_seam_closure_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_no_phase2_readiness_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_no_empirical_adequacy_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_no_canonical_toe_claim_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_qft_gr_not_authorized_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_master_action_not_promoted_v0",
        "post_samplerep32_axiom_audit_bounded_attack_selection_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_post_samplerep32_axiom_audit_selection_report_selects_full_pillar_return() -> None:
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
        "formal/python/tests/test_post_samplerep32_axiom_audit_bounded_attack_selection_gate.py"
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
        SELECTED_TARGET,
        NEXT_DEBT_TARGET,
        MASTER_ACTION_TARGET,
    }


def test_post_samplerep32_axiom_audit_selection_report_preserves_ledger_posture() -> None:
    report = _json(REPORT_PATH)

    assert report["ledger_posture"] == {
        "real_axiom_count": 59,
        "real_sorry_or_admit_count": 0,
        "real_axiom_file_count": 14,
        "defaultNonAlias": "absent_from_unresolved_axiom_debt_and_lean_backed",
        "sampleRep32": "absent_from_unresolved_axiom_debt_and_lean_backed_constructor",
        "prior_60_axiom_audit_status": "historical_only",
    }
    assert report["review_interpretation"] == {
        "audit_refresh_result_review_consumed": True,
        "defaultNonAlias_authority": "LEAN_BACKED_DISCHARGED",
        "sampleRep32_authority": "LEAN_BACKED_EXPLICIT_SAMPLE_REPRESENTATION_CONSTRUCTOR",
        "ledger_posture_consumed": "59_real_axioms_across_14_files",
    }
    assert report["next_target_expectations"] == {
        "target_id": SELECTED_TARGET,
        "selector_should_choose_from_global_map": True,
        "selector_executes_selected_lane": False,
        "must_preserve_59_axiom_posture": True,
    }
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_post_samplerep32_axiom_audit_selection_live_ledger_still_matches_59() -> None:
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
    assert "axiom sampleRep32" not in source_text
    assert "def sampleRep32" in source_text
    assert f"| `defaultNonAlias` | `{SOURCE_EVIDENCE}` |" not in ledger_text
    assert f"| `sampleRep32` | `{SOURCE_EVIDENCE}` |" not in ledger_text


def test_post_samplerep32_axiom_audit_selection_report_preserves_nonclaim_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["forbidden_effects"] == [
        "MASTER_ACTION_PROMOTION",
        "PILLAR_COMPLETION",
        "SEAM_CLOSURE",
        "PHASE_2_READINESS",
        "EMPIRICAL_ADEQUACY",
        "CANONICAL_TOE_STATUS",
        "QFT_GR_SOURCE_MAP_CLOSURE",
        "SELECTED_TARGET_EXECUTION",
        "GOVERNANCE_MANIFEST_ENROLLMENT",
    ]
    assert report["nonclaim_boundaries"] == {
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "qft_gr_source_map_closure_authorized": False,
        "selection_executes_target": False,
        "governance_manifest_enrollment_authorized": False,
    }
    assert "59-real-axiom posture" in report["acceptance_condition"]


def test_post_samplerep32_axiom_audit_selection_registry_rotates_to_full_pillar() -> None:
    payload = loop_registry()
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()

    state = payload["current_target_state"]
    assert state["previous_live_next_target"] == SELECTION_TARGET
    assert state["live_next_target"] == SELECTED_TARGET
    assert state["live_next_target_evidence"] == SELECTION_EVIDENCE
    assert state["active_lane"] == ACTIVE_LANE

    previous = workstream(PREVIOUS_WORKSTREAM, payload)
    assert previous["status"] == "paused"
    assert previous["authorized_next_strict_target"] == SELECTION_TARGET
    assert previous["selected_next_target"] == SELECTION_TARGET
    assert previous["review_token"] == CONSUMED_REVIEW_TOKEN
    assert previous["real_axiom_count"] == 59
    assert previous["real_axiom_file_count"] == 14

    current = active_workstream(payload)
    assert current["workstream_id"] == ACTIVE_LANE
    assert current["authorized_next_strict_target"] == SELECTED_TARGET
    assert current["consumed_target"] == SELECTION_TARGET
    assert current["latest_surface"] == SURFACE_ID
    assert current["source_review_surface"] == REVIEW_EVIDENCE
    assert current["source_review_report"] == REVIEW_REPORT_EVIDENCE
    assert current["selection_report"] == REPORT_EVIDENCE
    assert current["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert current["output_token"] == OUTPUT_TOKEN
    assert current["selected_next_target"] == SELECTED_TARGET
    assert current["selected_target_count"] == 1
    assert current["selection_executes_target"] == "no"
    assert current["real_axiom_count"] == 59
    assert current["real_axiom_file_count"] == 14
    assert current["default_nonalias_remains_discharged"] == "yes"
    assert current["sample_rep32_discharged"] == "yes"
    assert current["qft_gr_source_map_closure_authorized"] == "no"
    assert current["seam_closure_claim"] == "no"
    assert current["phase2_readiness_claim"] == "no"
    assert current["empirical_adequacy_claim"] == "no"
    assert current["canonical_toe_claim"] == "no"
    assert current["governance_manifest_enrollment_authorized"] == "no"
    assert current["master_action_promotion_authorized"] == "no"

    assert (
        "post_samplerep32_axiom_audit_bounded_attack_selection_nonclaim_boundary"
        in payload["retained_blocker_coverage"]
    )
    assert {
        "from": ACTIVE_LANE,
        "to": "full_pillar_target_map_next_lane_selection",
        "status": "active",
        "evidence": SELECTION_EVIDENCE,
    } in payload["dependency_edges"]
    assert (
        workstream("qft_gr_source_map", payload)["authorized_next_strict_target"]
        == SELECTED_TARGET
    )
    assert (
        workstream("master_action_dependency_frontier", payload)[
            "authorized_next_strict_target"
        ]
        == SELECTED_TARGET
    )


def test_post_samplerep32_axiom_audit_selection_public_surfaces_are_current() -> None:
    for path in [README_PATH, STATE_PATH, STRICT_MAP_PATH, ROADMAP_PATH]:
        text = read_text(path)
        assert SELECTED_TARGET in text
        assert SELECTION_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert OUTPUT_TOKEN in text
        assert "59 real axioms across 14 files" in text

    authoritative = read_text(CURRENT_AUTHORITATIVE_SURFACES_PATH)
    assert SELECTION_EVIDENCE in authoritative
    assert REPORT_EVIDENCE in authoritative
    assert OUTPUT_TOKEN in authoritative
    assert SELECTED_TARGET in authoritative

    inventory = read_text(INVENTORY_PATH)
    assert "INV-MATH-POST-SAMPLEREP32-AXIOM-AUDIT-BOUNDED-ATTACK-SELECTION-v0" in inventory
    assert SELECTION_EVIDENCE in inventory
    assert REPORT_EVIDENCE in inventory
    assert OUTPUT_TOKEN in inventory
    assert SELECTED_TARGET in inventory

    assert_focused_gate_not_manifest_enrolled(
        "test_post_samplerep32_axiom_audit_bounded_attack_selection_gate.py"
    )
