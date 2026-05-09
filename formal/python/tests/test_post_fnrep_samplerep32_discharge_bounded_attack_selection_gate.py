from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.tests.strict_physics_state_helpers import (
    README_PATH,
    REPO_ROOT,
    active_workstream,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_forbidden_promotions_closed,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
    skip_if_not_current_target,
    loop_registry,
    read_text,
    workstream,
)


SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostFNRepSampleRep32DischargeBoundedAttackSelection.lean"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01SampleRep32DischargeResultReview.lean"
)
DISCHARGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01SampleRep32Discharge.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_FNREP_SAMPLEREP32_DISCHARGE_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
)
REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROOF_DEBT_DISCHARGE_FNREP_SAMPLEREP32_RESULT_REVIEW_20260505_v0.json"
)
DISCHARGE_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROOF_DEBT_DISCHARGE_FNREP_SAMPLEREP32_20260505_v0.json"
)
INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
)

SURFACE_ID = "post_fnrep_samplerep32_discharge_bounded_attack_selection_v0"
ACTIVE_LANE = "post_fnrep_samplerep32_discharge_bounded_attack_selection"
PREVIOUS_WORKSTREAM = "fnrep_nonalias_samplerep32_discharge"
SELECTION_TARGET = "select_next_post_fnrep_samplerep32_discharge_bounded_attack"
REVIEW_TARGET = "review_fnrep_nonalias_samplerep32_discharge_result"
CONSUMED_REVIEW_TOKEN = (
    "FNREP_NONALIAS_SAMPLEREP32_DISCHARGE_RESULT_REVIEW_CONSUMED_LEAN_BACKED_CONSTRUCTOR"
)
OUTPUT_TOKEN = "POST_FNREP_SAMPLEREP32_DISCHARGE_NEXT_ATTACK_SELECTED"
SELECTED_TARGET = "prepare_axiom_ledger_audit_refresh"
NEXT_DEBT_TARGET = "prepare_next_proof_debt_ledger_discharge_item"
FULL_PILLAR_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
REPORT_ID = "POST_FNREP_SAMPLEREP32_DISCHARGE_BOUNDED_ATTACK_SELECTION_v0"
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
DISCHARGE_EVIDENCE = str(DISCHARGE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_REPORT_EVIDENCE = str(REVIEW_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
DISCHARGE_REPORT_EVIDENCE = str(DISCHARGE_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_post_fnrep_samplerep32_selection_surface_records_exactly_one_target() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        SURFACE_ID,
        SELECTION_TARGET,
        CONSUMED_REVIEW_TOKEN,
        OUTPUT_TOKEN,
        SELECTED_TARGET,
        NEXT_DEBT_TARGET,
        FULL_PILLAR_TARGET,
        "PostFNRepSampleRep32DischargeBoundedAttackSelectionStatus",
        "PostFNRepSampleRep32DischargeDecision",
        "prepareAxiomLedgerAuditRefresh",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_consumes_live_target_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_consumes_review_token_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_review_consumed_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_exactly_one_target_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_output_token_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_decision_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_selected_target_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_matches_review_recommendation_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_candidate_count_v0",
    }:
        assert token in text


def test_post_fnrep_samplerep32_selection_surface_carries_reviewed_ledger_posture() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_samplerep32_lean_backed_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_samplerep32_axiom_removed_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_default_nonalias_remains_discharged_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_axiom_count_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_axiom_file_count_v0",
        "real_axiom_count_after_discharge :=\n      fnrepSampleRep32DischargeResultReviewStatusReadoutV0.ledger_count_after_discharge",
        "real_axiom_file_count_after_discharge :=\n      fnrepSampleRep32DischargeResultReviewStatusReadoutV0.ledger_file_count_after_discharge",
    }:
        assert token in text


def test_post_fnrep_samplerep32_selection_surface_preserves_nonclaim_boundaries() -> None:
    text = _read(SELECTION_PATH)

    for theorem in {
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_does_not_execute_target_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_no_pillar_completion_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_no_seam_closure_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_no_phase2_readiness_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_no_empirical_adequacy_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_no_canonical_toe_claim_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_qft_gr_not_authorized_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_master_action_not_promoted_v0",
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_post_fnrep_samplerep32_selection_report_selects_audit_refresh() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_selection_only"
    assert report["current_target"] == SELECTION_TARGET
    assert report["consumed_review_target"] == REVIEW_TARGET
    assert report["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert report["output_token"] == OUTPUT_TOKEN
    assert report["review_surface"] == REVIEW_EVIDENCE
    assert report["review_report"] == REVIEW_REPORT_EVIDENCE
    assert report["discharge_surface"] == DISCHARGE_EVIDENCE
    assert report["discharge_report"] == DISCHARGE_REPORT_EVIDENCE
    assert report["selection_surface"] == SELECTION_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/"
        "test_post_fnrep_samplerep32_discharge_bounded_attack_selection_gate.py"
    )
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_TARGET"
    assert report["selection_executes_target"] is False
    assert report["selection_count"] == 1
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selected_decision"] == SELECTED_TARGET

    selected = [row for row in report["candidate_next_targets"] if row["selected"]]
    assert len(selected) == 1
    assert selected[0]["target"] == SELECTED_TARGET
    assert {row["target"] for row in report["candidate_next_targets"]} == {
        NEXT_DEBT_TARGET,
        FULL_PILLAR_TARGET,
        SELECTED_TARGET,
    }


def test_post_fnrep_samplerep32_selection_report_preserves_ledger_posture() -> None:
    report = _json(REPORT_PATH)

    assert report["review_interpretation"] == {
        "sampleRep32_result_review_consumed": True,
        "sampleRep32_authority": "LEAN_BACKED_EXPLICIT_SAMPLE_REPRESENTATION_CONSTRUCTOR",
        "defaultNonAlias_authority": "LEAN_BACKED_DISCHARGED",
        "ledger_delta_consumed": "60_to_59_real_axioms_and_15_to_14_axiom_bearing_files",
    }
    assert report["authority_posture"] == {
        "real_axiom_count": 59,
        "real_axiom_file_count": 14,
        "defaultNonAlias": "discharged_lean_backed_absent_from_unresolved_axiom_debt",
        "sampleRep32": "discharged_lean_backed_explicit_constructor_absent_from_unresolved_axiom_debt",
    }
    assert report["audit_refresh_target_expectations"] == {
        "expected_result_token": "AXIOM_LEDGER_AUDIT_REFRESH_CONFIRMED_59_REAL_AXIOMS",
        "real_axiom_count": 59,
        "real_axiom_file_count": 14,
        "defaultNonAlias_absent_from_unresolved_axiom_debt": True,
        "sampleRep32_absent_from_unresolved_axiom_debt": True,
        "recent_discharge_result_review_referenced": True,
    }
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_post_fnrep_samplerep32_selection_report_preserves_nonclaim_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["forbidden_effects"] == [
        "PILLAR_COMPLETION",
        "SEAM_CLOSURE",
        "PHASE_2_READINESS",
        "EMPIRICAL_ADEQUACY",
        "CANONICAL_TOE_STATUS",
        "QFT_GR_SOURCE_MAP_CLOSURE",
        "MASTER_ACTION_PROMOTION",
        "SELECTED_TARGET_EXECUTION",
    ]
    assert report["nonclaim_boundaries"] == {
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "qft_gr_source_map_closure_authorized": False,
        "master_action_promotion_authorized": False,
        "governance_manifest_enrollment_authorized": False,
        "selection_executes_target": False,
    }
    assert (
        report["acceptance_condition"]
        == "The selector consumes the sampleRep32 discharge review, selects exactly "
        "one next bounded target, preserves the 59-real-axiom posture, and does "
        "not infer master-action promotion, pillar completion, seam closure, "
        "Phase 2 readiness, empirical adequacy, canonical ToE status, or QFT-GR "
        "source-map closure."
    )


def test_post_fnrep_samplerep32_selection_registry_rotates_to_audit_refresh() -> None:
    payload = loop_registry()
    skip_if_not_current_target(payload, SELECTED_TARGET)
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
    assert previous["selected_next_target"] == SELECTION_TARGET
    assert previous["review_result_token"] == CONSUMED_REVIEW_TOKEN
    assert previous["real_axiom_count_after"] == 59
    assert previous["real_axiom_file_count_after"] == 14

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
        "post_fnrep_samplerep32_discharge_bounded_attack_selection_nonclaim_boundary"
        in payload["retained_blocker_coverage"]
    )
    assert {
        "from": ACTIVE_LANE,
        "to": "axiom_ledger_audit_refresh",
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


def test_post_fnrep_samplerep32_selection_public_surfaces_are_current() -> None:
    for path in {README_PATH, INVENTORY_PATH}:
        text = read_text(path)
        assert SELECTED_TARGET in text
        assert SELECTION_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert OUTPUT_TOKEN in text
        assert "59 real axioms" in text
        assert "14 files" in text


def test_post_fnrep_samplerep32_selection_gate_is_not_governance_manifest_enrolled() -> None:
    assert REPORT_EVIDENCE.endswith(
        "POST_FNREP_SAMPLEREP32_DISCHARGE_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
    )
    assert_focused_gate_not_manifest_enrolled(
        "test_post_fnrep_samplerep32_discharge_bounded_attack_selection_gate.py"
    )
