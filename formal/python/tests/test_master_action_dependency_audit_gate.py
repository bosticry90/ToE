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
    / "MasterActionDependencyAudit.lean"
)
SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterAudit.lean"
)
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionDependencyFrontier.lean"
)
QFT_GR_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_SourceMapEligibilityLadderSummaryResultReview.lean"
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
    / "MASTER_ACTION_DEPENDENCY_AUDIT_20260503_v0.json"
)
SELECTION_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_AUDIT_20260503_v0.json"
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

REPORT_ID = "MASTER_ACTION_DEPENDENCY_AUDIT_20260503_v0"
SURFACE_ID = "master_action_dependency_audit_v0"
CONSUMED_TARGET = "prepare_master_action_dependency_audit"
CONSUMED_TOKEN = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_AUDIT"
RESULT_TOKEN = "MASTER_ACTION_DEPENDENCY_AUDIT_COMPLETED_NONPROMOTED"
SELECTED_TARGET = "review_master_action_dependency_audit_result"
AUDIT_EVIDENCE = str(AUDIT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SELECTION_REPORT_EVIDENCE = str(SELECTION_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
FRONTIER_EVIDENCE = str(FRONTIER_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
QFT_GR_REVIEW_EVIDENCE = str(QFT_GR_REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
LEDGER_EVIDENCE = str(LEDGER_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_EVIDENCE = str(SOURCE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
PUBLIC_SURFACE_PATHS = [
    README_PATH,
    STATE_PATH,
    STRICT_MAP_PATH,
    ROADMAP_PATH,
    SEAM_REGISTRY_PATH,
    SEAM_INVENTORY_PATH,
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_master_action_dependency_audit_surface_records_completed_audit() -> None:
    text = _read(AUDIT_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        SELECTED_TARGET,
        "MasterActionDependencyAuditStatus",
        "master_action_dependency_audit_consumes_live_target_v0",
        "master_action_dependency_audit_consumes_selector_token_v0",
        "master_action_dependency_audit_selector_result_consumed_v0",
        "master_action_dependency_audit_map_checked_v0",
        "master_action_dependency_audit_result_token_v0",
        "master_action_dependency_audit_selected_next_target_v0",
    }:
        assert token in text

    assert "import ToeFormal.Derivation.MasterActionDependencyAudit" in aggregate_text


def test_audit_surface_carries_qft_gr_and_60_axiom_posture() -> None:
    text = _read(AUDIT_PATH)

    for token in {
        "master_action_dependency_audit_qft_gr_ladder_constructed_v0",
        "master_action_dependency_audit_qft_gr_witness_chain_absent_v0",
        "master_action_dependency_audit_qft_gr_source_map_not_authorized_v0",
        "master_action_dependency_audit_axiom_count_v0",
        "master_action_dependency_audit_default_nonalias_absent_v0",
        "master_action_dependency_audit_sample_rep32_retained_v0",
        "qft_gr_ladder_constructed",
        "qft_gr_witness_chain_absent",
        "qft_gr_source_map_closure_authorized",
        "real_axiom_count_confirmed",
        "default_nonalias_absent_from_unresolved_axiom_debt",
        "sample_rep32_retained",
    }:
        assert token in text


def test_audit_surface_preserves_dependency_frontier_and_nonclaim_boundaries() -> None:
    text = _read(AUDIT_PATH)

    for token in {
        "master_action_dependency_audit_candidate_dependency_only_v0",
        "master_action_dependency_audit_public_docs_checked_v0",
        "master_action_dependency_audit_roadmap_strict_refs_current_v0",
        "master_action_dependency_audit_no_stale_dependency_refs_v0",
        "master_action_dependency_audit_no_missing_dependency_refs_v0",
        "master_action_dependency_audit_reference_count_v0",
        "master_action_dependency_audit_boundary_count_v0",
        "master_action_dependency_audit_preserves_dependency_kind_ids_v0",
        "master_action_dependency_audit_preserves_retained_ids_v0",
        "master_action_dependency_audit_master_action_not_promoted_v0",
        "master_action_dependency_audit_no_pillar_completion_v0",
        "master_action_dependency_audit_no_seam_closure_v0",
        "master_action_dependency_audit_no_phase2_readiness_v0",
        "master_action_dependency_audit_no_empirical_adequacy_v0",
        "master_action_dependency_audit_no_canonical_toe_claim_v0",
        "master_action_dependency_audit_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_master_action_dependency_audit_report_records_completed_nonpromotion() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["audit_status"] == "completed_nonpromoted"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["audit_surface"] == AUDIT_EVIDENCE
    assert report["source_selection_surface"] == SELECTION_EVIDENCE
    assert report["source_selection_report"] == SELECTION_REPORT_EVIDENCE
    assert report["dependency_frontier_surface"] == FRONTIER_EVIDENCE
    assert report["qft_gr_ladder_review_surface"] == QFT_GR_REVIEW_EVIDENCE
    assert report["proof_debt_ledger"] == LEDGER_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_master_action_dependency_audit_gate.py"
    )
    assert report["authorized_effect"] == "AUDIT_DEPENDENCY_MAP_ONLY"
    assert report["next_action_after_audit"] == SELECTED_TARGET

    findings = report["audit_findings"]
    assert findings["after_audit_selector_result_consumed"] is True
    assert findings["master_action_dependency_map_checked"] is True
    assert findings["qft_gr_eligibility_ladder_constructed"] is True
    assert findings["qft_gr_witness_chain_absent"] is True
    assert findings["qft_gr_source_map_closure_authorized"] is False
    assert findings["real_axiom_count_confirmed"] == 60
    assert findings["defaultNonAlias_removed_from_unresolved_axiom_debt"] is True
    assert findings["sampleRep32_retained"] is True
    assert findings["stale_dependency_references_found"] == 0
    assert findings["missing_dependency_references_found"] == 0


def test_audit_report_preserves_expected_dependency_posture() -> None:
    report = _json(REPORT_PATH)

    assert report["ledger_posture"] == {
        "real_axiom_count": 60,
        "real_sorry_or_admit_count": 0,
        "real_axiom_file_count": 15,
        "defaultNonAlias": "absent_from_unresolved_axiom_debt_and_lean_backed",
        "sampleRep32": "retained_spec_backed_axiom",
    }
    assert report["qft_gr_dependency_status"] == {
        "eligibility_ladder_constructed": True,
        "witness_chain_absent": True,
        "missing_witness_count": 10,
        "source_map_closure_authorized": False,
        "witness_search_authorized": False,
        "status": "ladder_only_closure_not_authorized",
    }
    assert report["master_action_posture"]["candidate_dependency_surface_only"] is True
    assert report["master_action_posture"]["dependency_kind_count"] == 4
    assert report["master_action_posture"]["retained_boundary_count"] == 10
    assert report["master_action_posture"]["promotion_authorized"] is False
    assert report["dependency_map_posture"]["axiom_ledger_status"] == "60_real_axioms"
    assert (
        report["dependency_map_posture"]["defaultNonAlias_status"]
        == "discharged_no_longer_unresolved_debt"
    )
    assert report["dependency_map_posture"]["phase2_status"] == "unauthorized"
    assert report["dependency_map_posture"]["source_map_closure_status"] == "unauthorized"


def test_master_action_dependency_audit_live_ledger_still_matches_60_axioms() -> None:
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


def test_report_nonclaim_boundaries_and_public_surfaces_are_synced() -> None:
    report = _json(REPORT_PATH)
    assert report["nonclaim_boundaries"] == {
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "governance_manifest_enrollment_authorized": False,
    }

    for path in PUBLIC_SURFACE_PATHS:
        text = _read(path)
        assert AUDIT_EVIDENCE in text, f"{path} missing audit surface"
        assert RESULT_TOKEN in text, f"{path} missing audit result token"
        assert SELECTED_TARGET in text, f"{path} missing audit next target"
        assert "QFT-GR remains ladder-only and closure-not-authorized" in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-MASTER-ACTION-DEPENDENCY-AUDIT-v0" in inventory_text
    assert REPORT_ID in _read(REPORT_PATH)
    assert_focused_gate_not_manifest_enrolled("test_master_action_dependency_audit_gate.py")
