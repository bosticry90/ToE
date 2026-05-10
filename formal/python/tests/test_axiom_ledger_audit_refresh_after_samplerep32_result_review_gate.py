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
    assert_public_surfaces_match_registry,
    loop_registry,
    read_text,
    skip_if_not_current_target,
    workstream,
)
from formal.python.tests.test_lean_axiom_spec_backed_ledger_gate import (
    _lean_surface_debt,
    _ledger_rows,
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
MATH_PHYSICS_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
)
CURRENT_AUTHORITATIVE_SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)

REPORT_ID = "AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_20260505_v0"
SURFACE_ID = "axiom_ledger_audit_refresh_after_samplerep32_result_review_v0"
ACTIVE_LANE = "axiom_ledger_audit_refresh_after_samplerep32_result_review"
PREVIOUS_WORKSTREAM = "axiom_ledger_audit_refresh_after_samplerep32"
CURRENT_TARGET = "review_axiom_ledger_audit_refresh_after_samplerep32_result"
CONSUMED_RESULT_TOKEN = "AXIOM_LEDGER_AUDIT_REFRESH_CONFIRMED_59_REAL_AXIOMS"
REVIEW_TOKEN = (
    "AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_CONSUMED_59_REAL_AXIOMS_CONFIRMED"
)
NEXT_TARGET = "select_next_post_samplerep32_axiom_audit_bounded_attack"
RECOMMENDED_SELECTOR_CHOICE = "return_to_full_pillar_target_map_next_lane_selection"
CANDIDATE_SELECTOR_TARGETS = [
    "return_to_full_pillar_target_map_next_lane_selection",
    "prepare_next_proof_debt_ledger_discharge_item",
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


def test_result_review_after_samplerep32_lean_surface_consumes_audit_refresh() -> None:
    text = _read(REVIEW_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CURRENT_TARGET,
        CONSUMED_RESULT_TOKEN,
        REVIEW_TOKEN,
        NEXT_TARGET,
        RECOMMENDED_SELECTOR_CHOICE,
        "AxiomLedgerAuditRefreshAfterSampleRep32ResultReviewStatus",
        "AxiomLedgerAuditRefreshAfterSampleRep32ResultReviewDecision",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_consumes_live_target_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_consumes_audit_result_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_real_axiom_count_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_no_sorry_or_admit_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_file_count_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_default_nonalias_absent_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_default_nonalias_lean_backed_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_sample_rep32_absent_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_sample_rep32_lean_backed_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_no_stale_active_60_count_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_prior_60_historical_only_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_token_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_selected_next_target_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_recommends_full_pillar_map_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_selector_choice_not_executed_v0",
    }:
        assert token in text

    assert (
        "import ToeFormal.Derivation.AxiomLedgerAuditRefreshAfterSampleRep32ResultReview"
        in aggregate_text
    )


def test_result_review_after_samplerep32_lean_surface_preserves_nonclaim_boundaries() -> None:
    text = _read(REVIEW_PATH)

    for theorem in {
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_no_pillar_completion_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_no_seam_closure_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_no_phase2_readiness_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_no_empirical_adequacy_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_no_canonical_toe_claim_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_qft_gr_not_authorized_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_master_action_not_promoted_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_result_review_after_samplerep32_report_consumes_audit_and_selects_selector() -> None:
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
        "formal/python/tests/test_axiom_ledger_audit_refresh_after_samplerep32_result_review_gate.py"
    )

    assert report["ledger_posture"] == {
        "real_axiom_count": 59,
        "real_sorry_or_admit_count": 0,
        "real_axiom_file_count": 14,
        "defaultNonAlias": "absent_from_unresolved_axiom_debt_and_lean_backed",
        "sampleRep32": "absent_from_unresolved_axiom_debt_and_lean_backed_constructor",
        "active_ledger_state_confirmed": True,
        "prior_60_axiom_audit_status": "historical_only",
    }
    assert report["review_effect"] == {
        "audit_refresh_result_consumed": True,
        "real_axiom_count_confirmed": True,
        "real_axiom_file_count_confirmed": True,
        "defaultNonAlias_absent_from_unresolved_axiom_debt": True,
        "defaultNonAlias_lean_backed": True,
        "sampleRep32_absent_from_unresolved_axiom_debt": True,
        "sampleRep32_lean_backed_constructor": True,
        "stale_active_60_count_references_remain_cleared": True,
        "prior_60_axiom_audit_historical_only": True,
        "post_audit_selector_target_selected": True,
    }
    assert report["candidate_selector_targets"] == CANDIDATE_SELECTOR_TARGETS
    assert report["recommended_selector_choice"] == RECOMMENDED_SELECTOR_CHOICE
    assert report["review_executes_selector_choice"] is False
    assert report["next_action_after_result_review"] == NEXT_TARGET


def test_result_review_after_samplerep32_live_ledger_matches_59_axiom_posture() -> None:
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


def test_result_review_after_samplerep32_report_preserves_nonclaim_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["forbidden_effects"] == [
        "MASTER_ACTION_PROMOTION",
        "PILLAR_COMPLETION",
        "SEAM_CLOSURE",
        "PHASE_2_READINESS",
        "EMPIRICAL_ADEQUACY",
        "CANONICAL_TOE_STATUS",
        "QFT_GR_SOURCE_MAP_CLOSURE",
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
        "governance_manifest_enrollment_authorized": False,
    }
    assert "59-real-axiom posture across 14 files" in report["acceptance_condition"]


def test_result_review_after_samplerep32_registry_rotates_to_post_audit_selector() -> None:
    payload = loop_registry()
    skip_if_not_current_target(payload, NEXT_TARGET)
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()

    state = payload["current_target_state"]
    assert state["previous_live_next_target"] == CURRENT_TARGET
    assert state["live_next_target"] == NEXT_TARGET
    assert state["live_next_target_evidence"] == REVIEW_EVIDENCE
    assert state["active_lane"] == ACTIVE_LANE

    previous = workstream(PREVIOUS_WORKSTREAM, payload)
    assert previous["status"] == "paused"
    assert previous["authorized_next_strict_target"] == CURRENT_TARGET
    assert previous["consumed_target"] == "prepare_axiom_ledger_audit_refresh"
    assert previous["latest_surface"] == "axiom_ledger_audit_refresh_after_samplerep32_v0"
    assert previous["result_token"] == CONSUMED_RESULT_TOKEN
    assert previous["real_axiom_count"] == 59
    assert previous["real_axiom_file_count"] == 14
    assert previous["selected_next_target"] == CURRENT_TARGET

    current = workstream(ACTIVE_LANE, payload)
    assert current["status"] == "active"
    assert current["authorized_next_strict_target"] == NEXT_TARGET
    assert current["consumed_target"] == CURRENT_TARGET
    assert current["latest_surface"] == SURFACE_ID
    assert current["audit_surface"] == AUDIT_EVIDENCE
    assert current["audit_report"] == AUDIT_REPORT_EVIDENCE
    assert current["review_report"] == REPORT_EVIDENCE
    assert current["consumed_result_token"] == CONSUMED_RESULT_TOKEN
    assert current["review_token"] == REVIEW_TOKEN
    assert current["real_axiom_count"] == 59
    assert current["real_axiom_file_count"] == 14
    assert current["default_nonalias_absent_from_unresolved_axiom_debt"] == "yes"
    assert current["sample_rep32_absent_from_unresolved_axiom_debt"] == "yes"
    assert current["prior_60_axiom_audit_status"] == "historical_only"
    assert current["selected_next_target"] == NEXT_TARGET
    assert current["recommended_selector_choice"] == RECOMMENDED_SELECTOR_CHOICE
    assert current["selector_choice_executed"] == "no"
    assert current["qft_gr_source_map_closure_authorized"] == "no"
    assert current["seam_closure_claim"] == "no"
    assert current["phase2_readiness_claim"] == "no"
    assert current["empirical_adequacy_claim"] == "no"
    assert current["canonical_toe_claim"] == "no"
    assert current["governance_manifest_enrollment_authorized"] == "no"
    assert current["master_action_promotion_authorized"] == "no"

    assert (
        "axiom_ledger_audit_refresh_after_samplerep32_result_review_nonclaim_boundary"
        in payload["retained_blocker_coverage"]
    )
    assert NEXT_TARGET in payload["next_strict_target_coverage"]
    assert {
        "from": ACTIVE_LANE,
        "to": "post_samplerep32_axiom_audit_bounded_attack_selection",
        "status": "active",
        "evidence": REVIEW_EVIDENCE,
    } in payload["dependency_edges"]
    assert (
        workstream("qft_gr_source_map", payload)["authorized_next_strict_target"]
        == NEXT_TARGET
    )
    assert (
        workstream("master_action_dependency_frontier", payload)[
            "authorized_next_strict_target"
        ]
        == NEXT_TARGET
    )


def test_result_review_after_samplerep32_public_surfaces_and_manifest_posture() -> None:
    for path in [README_PATH, STATE_PATH, STRICT_MAP_PATH, ROADMAP_PATH]:
        text = read_text(path)
        assert REVIEW_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert REVIEW_TOKEN in text
        assert NEXT_TARGET in text
        assert RECOMMENDED_SELECTOR_CHOICE in text
        assert "59 real axioms across 14 files" in text

    authoritative = read_text(CURRENT_AUTHORITATIVE_SURFACES_PATH)
    assert REVIEW_EVIDENCE in authoritative
    assert REPORT_EVIDENCE in authoritative
    assert REVIEW_TOKEN in authoritative
    assert NEXT_TARGET in authoritative

    inventory = read_text(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-AXIOM-LEDGER-AUDIT-REFRESH-AFTER-SAMPLEREP32-RESULT-REVIEW-v0" in inventory
    assert REVIEW_EVIDENCE in inventory
    assert REPORT_EVIDENCE in inventory
    assert REVIEW_TOKEN in inventory
    assert NEXT_TARGET in inventory
    assert RECOMMENDED_SELECTOR_CHOICE in inventory

    assert_focused_gate_not_manifest_enrolled(
        "test_axiom_ledger_audit_refresh_after_samplerep32_result_review_gate.py"
    )
