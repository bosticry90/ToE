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


AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "AxiomLedgerAuditRefreshAfterSampleRep32.lean"
)
SELECTOR_PATH = (
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
    / "AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_20260505_v0.json"
)
SELECTOR_REPORT_PATH = (
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
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MATH_PHYSICS_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
)
CURRENT_AUTHORITATIVE_SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
LEDGER_GATE_PATH = (
    REPO_ROOT / "formal" / "python" / "tests" / "test_lean_axiom_spec_backed_ledger_gate.py"
)

REPORT_ID = "AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_20260505_v0"
SURFACE_ID = "axiom_ledger_audit_refresh_after_samplerep32_v0"
ACTIVE_LANE = "axiom_ledger_audit_refresh_after_samplerep32"
PREVIOUS_WORKSTREAM = "post_fnrep_samplerep32_discharge_bounded_attack_selection"
CURRENT_TARGET = "prepare_axiom_ledger_audit_refresh"
CONSUMED_SELECTOR_TARGET = "select_next_post_fnrep_samplerep32_discharge_bounded_attack"
CONSUMED_SELECTOR_TOKEN = "POST_FNREP_SAMPLEREP32_DISCHARGE_NEXT_ATTACK_SELECTED"
CONSUMED_REVIEW_TARGET = "review_fnrep_nonalias_samplerep32_discharge_result"
CONSUMED_REVIEW_TOKEN = (
    "FNREP_NONALIAS_SAMPLEREP32_DISCHARGE_RESULT_REVIEW_CONSUMED_LEAN_BACKED_CONSTRUCTOR"
)
RESULT_TOKEN = "AXIOM_LEDGER_AUDIT_REFRESH_CONFIRMED_59_REAL_AXIOMS"
NEXT_TARGET = "review_axiom_ledger_audit_refresh_after_samplerep32_result"
AUDIT_EVIDENCE = str(AUDIT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SELECTOR_EVIDENCE = str(SELECTOR_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
DISCHARGE_EVIDENCE = str(DISCHARGE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SELECTOR_REPORT_EVIDENCE = str(SELECTOR_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
REVIEW_REPORT_EVIDENCE = str(REVIEW_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
DISCHARGE_REPORT_EVIDENCE = str(DISCHARGE_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
LEDGER_EVIDENCE = str(LEDGER_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_EVIDENCE = str(SOURCE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")

ACTIVE_AUTHORITY_SURFACES = [
    README_PATH,
    STATE_PATH,
    STRICT_MAP_PATH,
    ROADMAP_PATH,
    MATH_PHYSICS_INVENTORY_PATH,
    CURRENT_AUTHORITATIVE_SURFACES_PATH,
    LEDGER_GATE_PATH,
]
STALE_ACTIVE_60_PATTERNS = {
    "REAL_AXIOM_COUNT_v0: 60",
    "real_axiom_count_v0: 60",
    "CURRENT_REAL_AXIOM_COUNT_v0: 60",
    "active ledger posture: 60 real axioms",
    "current active ledger posture at 60 real axioms",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_audit_refresh_after_samplerep32_lean_surface_records_59_axiom_posture() -> None:
    text = _read(AUDIT_PATH)

    for token in {
        SURFACE_ID,
        CURRENT_TARGET,
        CONSUMED_SELECTOR_TOKEN,
        CONSUMED_REVIEW_TOKEN,
        RESULT_TOKEN,
        NEXT_TARGET,
        "AxiomLedgerAuditRefreshAfterSampleRep32Status",
        "axiom_ledger_audit_refresh_after_samplerep32_consumes_live_target_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_consumes_selector_token_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_consumes_review_token_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_consumes_review_token_literal_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_selector_consumed_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_selector_token_consumed_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_real_axiom_count_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_no_sorry_or_admit_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_file_count_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_default_nonalias_absent_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_sample_rep32_absent_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_sample_rep32_lean_backed_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_no_stale_active_60_count_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_recent_review_referenced_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_result_token_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_selected_next_target_v0",
    }:
        assert token in text


def test_audit_refresh_after_samplerep32_lean_surface_preserves_nonclaim_boundaries() -> None:
    text = _read(AUDIT_PATH)

    for theorem in {
        "axiom_ledger_audit_refresh_after_samplerep32_no_pillar_completion_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_no_seam_closure_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_no_phase2_readiness_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_no_empirical_adequacy_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_no_canonical_toe_claim_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_qft_gr_not_authorized_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_master_action_not_promoted_v0",
        "axiom_ledger_audit_refresh_after_samplerep32_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_audit_refresh_after_samplerep32_report_confirms_selector_and_ledger_posture() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["audit_status"] == "completed_audit_refresh"
    assert report["current_target"] == CURRENT_TARGET
    assert report["consumed_selector_target"] == CONSUMED_SELECTOR_TARGET
    assert report["consumed_selector_token"] == CONSUMED_SELECTOR_TOKEN
    assert report["consumed_review_target"] == CONSUMED_REVIEW_TARGET
    assert report["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["audit_surface"] == AUDIT_EVIDENCE
    assert report["selector_surface"] == SELECTOR_EVIDENCE
    assert report["selector_report"] == SELECTOR_REPORT_EVIDENCE
    assert report["review_surface"] == REVIEW_EVIDENCE
    assert report["review_report"] == REVIEW_REPORT_EVIDENCE
    assert report["discharge_surface"] == DISCHARGE_EVIDENCE
    assert report["discharge_report"] == DISCHARGE_REPORT_EVIDENCE
    assert report["proof_debt_ledger"] == LEDGER_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_axiom_ledger_audit_refresh_after_samplerep32_gate.py"
    )

    assert report["ledger_posture"] == {
        "real_axiom_count": 59,
        "real_sorry_or_admit_count": 0,
        "real_axiom_file_count": 14,
        "defaultNonAlias": "absent_from_unresolved_axiom_debt_and_lean_backed",
        "sampleRep32": "absent_from_unresolved_axiom_debt_and_lean_backed_constructor",
        "recent_sampleRep32_discharge_result_review_referenced": True,
    }
    assert report["audit_findings"] == {
        "post_fnrep_samplerep32_selector_result_consumed": True,
        "sampleRep32_discharge_review_token_consumed": True,
        "real_axiom_count_confirmed": True,
        "real_axiom_file_count_confirmed": True,
        "defaultNonAlias_absent_from_axiom_ledger": True,
        "sampleRep32_absent_from_axiom_ledger": True,
        "active_authority_surfaces_have_no_stale_active_60_axiom_posture": True,
        "review_result_target_selected": True,
    }


def test_live_ledger_matches_post_samplerep32_axiom_posture() -> None:
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


def test_active_authority_surfaces_do_not_assert_stale_active_60_posture() -> None:
    for path in ACTIVE_AUTHORITY_SURFACES:
        text = _read(path)
        for pattern in STALE_ACTIVE_60_PATTERNS:
            assert pattern not in text, f"{path} still contains stale active count: {pattern}"


def test_audit_refresh_after_samplerep32_report_preserves_nonclaim_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["forbidden_effects"] == [
        "PILLAR_COMPLETION",
        "SEAM_CLOSURE",
        "PHASE_2_READINESS",
        "EMPIRICAL_ADEQUACY",
        "CANONICAL_TOE_STATUS",
        "QFT_GR_SOURCE_MAP_CLOSURE",
        "MASTER_ACTION_PROMOTION",
        "GOVERNANCE_MANIFEST_ENROLLMENT",
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
    }
    assert report["next_action_after_audit_refresh"] == NEXT_TARGET
    assert "59 real axioms across 14 files" in report["acceptance_condition"]


def test_audit_refresh_after_samplerep32_registry_rotates_to_result_review() -> None:
    payload = loop_registry()
    skip_if_not_current_target(payload, NEXT_TARGET)
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()

    state = payload["current_target_state"]
    assert state["previous_live_next_target"] == CURRENT_TARGET
    assert state["live_next_target"] == NEXT_TARGET
    assert state["live_next_target_evidence"] == AUDIT_EVIDENCE
    assert state["active_lane"] == ACTIVE_LANE

    previous = workstream(PREVIOUS_WORKSTREAM, payload)
    assert previous["status"] == "paused"
    assert previous["selected_next_target"] == CURRENT_TARGET
    assert previous["output_token"] == CONSUMED_SELECTOR_TOKEN
    assert previous["real_axiom_count"] == 59
    assert previous["real_axiom_file_count"] == 14

    current = workstream(ACTIVE_LANE, payload)
    assert current["status"] == "active"
    assert current["authorized_next_strict_target"] == NEXT_TARGET
    assert current["consumed_target"] == CURRENT_TARGET
    assert current["latest_surface"] == SURFACE_ID
    assert current["source_selector_surface"] == SELECTOR_EVIDENCE
    assert current["source_selector_report"] == SELECTOR_REPORT_EVIDENCE
    assert current["source_review_surface"] == REVIEW_EVIDENCE
    assert current["source_review_report"] == REVIEW_REPORT_EVIDENCE
    assert current["audit_report"] == REPORT_EVIDENCE
    assert current["consumed_selector_token"] == CONSUMED_SELECTOR_TOKEN
    assert current["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert current["result_token"] == RESULT_TOKEN
    assert current["real_axiom_count"] == 59
    assert current["real_axiom_file_count"] == 14
    assert current["default_nonalias_absent_from_unresolved_axiom_debt"] == "yes"
    assert current["sample_rep32_absent_from_unresolved_axiom_debt"] == "yes"
    assert current["stale_active_60_axiom_posture"] == "absent"
    assert current["selected_next_target"] == NEXT_TARGET
    assert current["selection_executes_target"] == "no"
    assert current["qft_gr_source_map_closure_authorized"] == "no"
    assert current["seam_closure_claim"] == "no"
    assert current["phase2_readiness_claim"] == "no"
    assert current["empirical_adequacy_claim"] == "no"
    assert current["canonical_toe_claim"] == "no"
    assert current["governance_manifest_enrollment_authorized"] == "no"
    assert current["master_action_promotion_authorized"] == "no"

    assert (
        "axiom_ledger_audit_refresh_after_samplerep32_nonclaim_boundary"
        in payload["retained_blocker_coverage"]
    )
    assert NEXT_TARGET in payload["next_strict_target_coverage"]
    assert {
        "from": ACTIVE_LANE,
        "to": "axiom_ledger_audit_refresh_after_samplerep32_result_review",
        "status": "active",
        "evidence": AUDIT_EVIDENCE,
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


def test_audit_refresh_after_samplerep32_public_surfaces_and_manifest_posture() -> None:
    for path in [README_PATH, STATE_PATH, STRICT_MAP_PATH, ROADMAP_PATH]:
        text = read_text(path)
        assert AUDIT_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert RESULT_TOKEN in text
        assert NEXT_TARGET in text
        assert "59 real axioms across 14 files" in text

    inventory = read_text(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-AXIOM-LEDGER-AUDIT-REFRESH-AFTER-SAMPLEREP32-v0" in inventory
    assert AUDIT_EVIDENCE in inventory
    assert REPORT_EVIDENCE in inventory
    assert RESULT_TOKEN in inventory
    assert NEXT_TARGET in inventory

    assert_focused_gate_not_manifest_enrolled(
        "test_axiom_ledger_audit_refresh_after_samplerep32_gate.py"
    )
