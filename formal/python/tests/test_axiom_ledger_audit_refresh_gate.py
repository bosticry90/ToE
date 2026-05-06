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
AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "AxiomLedgerAuditRefresh.lean"
)
SELECTOR_PATH = (
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
    / "AXIOM_LEDGER_AUDIT_REFRESH_20260503_v0.json"
)
SELECTOR_REPORT_PATH = (
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
LEDGER_GATE_PATH = (
    REPO_ROOT / "formal" / "python" / "tests" / "test_lean_axiom_spec_backed_ledger_gate.py"
)

REPORT_ID = "AXIOM_LEDGER_AUDIT_REFRESH_20260503_v0"
SURFACE_ID = "axiom_ledger_audit_refresh_v0"
CURRENT_TARGET = "prepare_axiom_ledger_audit_refresh"
CONSUMED_SELECTOR_TARGET = "select_next_post_proof_debt_discharge_bounded_attack"
CONSUMED_SELECTOR_TOKEN = "POST_PROOF_DEBT_DISCHARGE_NEXT_ATTACK_SELECTED"
CONSUMED_REVIEW_TOKEN = (
    "FNREP_NONALIAS_DEFAULT_NONALIAS_DISCHARGE_RESULT_REVIEW_CONSUMED_LEAN_BACKED"
)
RESULT_TOKEN = "AXIOM_LEDGER_AUDIT_REFRESH_CONFIRMED_60_REAL_AXIOMS"
NEXT_TARGET = "review_axiom_ledger_audit_refresh_result"
AUDIT_EVIDENCE = str(AUDIT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SELECTOR_EVIDENCE = str(SELECTOR_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SELECTOR_REPORT_EVIDENCE = str(SELECTOR_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
REVIEW_REPORT_EVIDENCE = str(REVIEW_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
LEDGER_EVIDENCE = str(LEDGER_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_EVIDENCE = str(SOURCE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")

ACTIVE_STALE_COUNT_SURFACES = [
    README_PATH,
    STATE_PATH,
    STRICT_MAP_PATH,
    ROADMAP_PATH,
    MATH_PHYSICS_INVENTORY_PATH,
    LEDGER_GATE_PATH,
]
STALE_61_POSTURE_PATTERNS = {
    "61 real uncommented axioms",
    "61 real axioms, 0 `sorry`/`admit`",
    "61_REAL_AXIOMS_0_SORRY_OR_ADMIT_15_FILES",
    "Baseline is 61 real axioms",
    "real_axiom_count_v0: 61",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_audit_refresh_lean_surface_records_confirmed_60_axiom_posture() -> None:
    text = _read(AUDIT_PATH)

    for token in {
        SURFACE_ID,
        CURRENT_TARGET,
        CONSUMED_SELECTOR_TOKEN,
        CONSUMED_REVIEW_TOKEN,
        RESULT_TOKEN,
        NEXT_TARGET,
        "AxiomLedgerAuditRefreshStatus",
        "axiom_ledger_audit_refresh_consumes_live_target_v0",
        "axiom_ledger_audit_refresh_consumes_selector_token_v0",
        "axiom_ledger_audit_refresh_consumes_fnrep_review_token_v0",
        "axiom_ledger_audit_refresh_post_discharge_selector_consumed_v0",
        "axiom_ledger_audit_refresh_selector_result_token_consumed_v0",
        "axiom_ledger_audit_refresh_real_axiom_count_v0",
        "axiom_ledger_audit_refresh_no_sorry_or_admit_v0",
        "axiom_ledger_audit_refresh_file_count_v0",
        "axiom_ledger_audit_refresh_default_nonalias_absent_v0",
        "axiom_ledger_audit_refresh_default_nonalias_lean_backed_v0",
        "axiom_ledger_audit_refresh_sample_rep32_retained_v0",
        "axiom_ledger_audit_refresh_no_stale_61_count_v0",
        "axiom_ledger_audit_refresh_recent_discharge_referenced_v0",
        "axiom_ledger_audit_refresh_result_token_v0",
        "axiom_ledger_audit_refresh_selected_next_target_v0",
    }:
        assert token in text


def test_audit_refresh_lean_surface_preserves_nonclaim_boundaries() -> None:
    text = _read(AUDIT_PATH)

    for theorem in {
        "axiom_ledger_audit_refresh_no_pillar_completion_v0",
        "axiom_ledger_audit_refresh_no_seam_closure_v0",
        "axiom_ledger_audit_refresh_no_phase2_readiness_v0",
        "axiom_ledger_audit_refresh_no_empirical_adequacy_v0",
        "axiom_ledger_audit_refresh_master_action_not_promoted_v0",
        "axiom_ledger_audit_refresh_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_audit_refresh_report_confirms_selector_and_ledger_posture() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["audit_status"] == "completed_audit_refresh"
    assert report["current_target"] == CURRENT_TARGET
    assert report["consumed_selector_target"] == CONSUMED_SELECTOR_TARGET
    assert report["consumed_selector_token"] == CONSUMED_SELECTOR_TOKEN
    assert report["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["audit_surface"] == AUDIT_EVIDENCE
    assert report["selector_surface"] == SELECTOR_EVIDENCE
    assert report["selector_report"] == SELECTOR_REPORT_EVIDENCE
    assert report["review_surface"] == REVIEW_EVIDENCE
    assert report["review_report"] == REVIEW_REPORT_EVIDENCE
    assert report["proof_debt_ledger"] == LEDGER_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_axiom_ledger_audit_refresh_gate.py"
    )

    assert report["ledger_posture"] == {
        "real_axiom_count": 60,
        "real_sorry_or_admit_count": 0,
        "real_axiom_file_count": 15,
        "defaultNonAlias": "absent_from_unresolved_axiom_debt_and_lean_backed",
        "sampleRep32": "retained_spec_backed_axiom",
        "recent_discharge_result_referenced": True,
    }
    assert report["audit_findings"] == {
        "post_proof_debt_selector_result_consumed": True,
        "fnrep_discharge_review_token_consumed": True,
        "real_axiom_count_confirmed": True,
        "defaultNonAlias_absent_from_axiom_ledger": True,
        "sampleRep32_retained_with_correct_authority_status": True,
        "active_docs_and_gates_have_no_stale_61_count_posture": True,
        "review_result_target_selected": True,
    }


def test_live_ledger_matches_60_axiom_refresh_posture() -> None:
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


def test_active_docs_and_gates_do_not_assert_stale_61_posture() -> None:
    for path in ACTIVE_STALE_COUNT_SURFACES:
        text = _read(path)
        for pattern in STALE_61_POSTURE_PATTERNS:
            assert pattern not in text, f"{path} still contains stale count: {pattern}"


def test_audit_refresh_report_preserves_nonclaim_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["forbidden_effects"] == [
        "PILLAR_COMPLETION",
        "SEAM_CLOSURE",
        "PHASE_2_READINESS",
        "EMPIRICAL_ADEQUACY",
        "MASTER_ACTION_PROMOTION",
        "GOVERNANCE_MANIFEST_ENROLLMENT",
    ]
    assert report["nonclaim_boundaries"] == {
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "master_action_promotion_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }
    assert report["next_action_after_audit_refresh"] == NEXT_TARGET
    assert "60 real axioms" in report["acceptance_condition"]


def test_audit_refresh_public_surfaces_and_manifest_posture() -> None:
    for path in [README_PATH, STATE_PATH, STRICT_MAP_PATH, ROADMAP_PATH]:
        text = _read(path)
        assert AUDIT_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert RESULT_TOKEN in text
        assert NEXT_TARGET in text

    inventory = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-AXIOM-LEDGER-AUDIT-REFRESH-v0" in inventory
    assert AUDIT_EVIDENCE in inventory
    assert REPORT_EVIDENCE in inventory
    assert RESULT_TOKEN in inventory
    assert NEXT_TARGET in inventory

    assert_focused_gate_not_manifest_enrolled("test_axiom_ledger_audit_refresh_gate.py")
