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
GAP_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionDependencyGapPacket.lean"
)
SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostMasterActionDependencyAuditBoundedAttackSelection.lean"
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
    / "MASTER_ACTION_DEPENDENCY_GAP_PACKET_20260503_v0.json"
)
SELECTION_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_MASTER_ACTION_DEPENDENCY_AUDIT_BOUNDED_ATTACK_SELECTION_20260503_v0.json"
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

REPORT_ID = "MASTER_ACTION_DEPENDENCY_GAP_PACKET_20260503_v0"
SURFACE_ID = "master_action_dependency_gap_packet_v0"
CONSUMED_TARGET = "prepare_master_action_dependency_gap_packet"
CONSUMED_SELECTOR_TOKEN = "POST_MASTER_ACTION_DEPENDENCY_AUDIT_NEXT_ATTACK_SELECTED"
RESULT_TOKEN = "MASTER_ACTION_DEPENDENCY_GAP_PACKET_PREPARED"
NEXT_TARGET = "review_master_action_dependency_gap_packet_result"
GAP_PACKET_EVIDENCE = str(GAP_PACKET_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SELECTION_REPORT_EVIDENCE = str(SELECTION_REPORT_PATH.relative_to(REPO_ROOT)).replace(
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


def test_master_action_dependency_gap_packet_surface_records_packet() -> None:
    text = _read(GAP_PACKET_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_SELECTOR_TOKEN,
        RESULT_TOKEN,
        NEXT_TARGET,
        "MasterActionDependencyGapPacketStatus",
        "master_action_dependency_gap_packet_consumes_live_target_v0",
        "master_action_dependency_gap_packet_consumes_selector_token_v0",
        "master_action_dependency_gap_packet_selector_result_consumed_v0",
        "master_action_dependency_gap_packet_gap_classes_listed_v0",
        "master_action_dependency_gap_packet_gap_class_count_v0",
        "master_action_dependency_gap_packet_result_token_v0",
        "master_action_dependency_gap_packet_selected_next_target_v0",
        "master_action_dependency_gap_packet_solves_no_dependencies_v0",
    } | REQUIRED_GAP_LABELS:
        assert token in text

    assert "import ToeFormal.Derivation.MasterActionDependencyGapPacket" in aggregate_text


def test_gap_packet_surface_records_required_gap_classes_and_posture() -> None:
    text = _read(GAP_PACKET_PATH)

    for token in {
        "master_action_dependency_gap_packet_qft_gr_ladder_constructed_v0",
        "master_action_dependency_gap_packet_qft_gr_witness_chain_absent_v0",
        "master_action_dependency_gap_packet_qft_gr_source_map_not_authorized_v0",
        "master_action_dependency_gap_packet_full_pillar_completion_absent_v0",
        "master_action_dependency_gap_packet_global_seam_closure_absent_v0",
        "master_action_dependency_gap_packet_phase2_authorization_absent_v0",
        "master_action_dependency_gap_packet_canonical_derivation_absent_v0",
        "master_action_dependency_gap_packet_empirical_adequacy_absent_v0",
        "master_action_dependency_gap_packet_axiom_count_v0",
        "master_action_dependency_gap_packet_default_nonalias_absent_v0",
        "master_action_dependency_gap_packet_sample_rep32_retained_v0",
        "gap_class_count",
        "real_axiom_count_confirmed",
        "default_nonalias_absent_from_unresolved_axiom_debt",
        "sample_rep32_retained",
    }:
        assert token in text


def test_gap_packet_surface_preserves_nonclaim_boundaries() -> None:
    text = _read(GAP_PACKET_PATH)

    for token in {
        "master_action_dependency_gap_packet_master_action_not_promoted_v0",
        "master_action_dependency_gap_packet_no_pillar_completion_v0",
        "master_action_dependency_gap_packet_no_seam_closure_v0",
        "master_action_dependency_gap_packet_no_phase2_readiness_v0",
        "master_action_dependency_gap_packet_no_empirical_adequacy_v0",
        "master_action_dependency_gap_packet_no_canonical_toe_claim_v0",
        "master_action_dependency_gap_packet_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_gap_packet_report_records_classification_only_packet() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["packet_status"] == "prepared_classification_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_SELECTOR_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["gap_packet_surface"] == GAP_PACKET_EVIDENCE
    assert report["source_selector_surface"] == SELECTION_EVIDENCE
    assert report["source_selector_report"] == SELECTION_REPORT_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_master_action_dependency_gap_packet_gate.py"
    )
    assert report["authorized_effect"] == "CLASSIFY_MISSING_DEPENDENCIES_ONLY"
    assert report["solves_dependencies"] is False
    assert report["gap_class_count"] == 10
    assert report["next_action_after_gap_packet"] == NEXT_TARGET

    assert {row["label"] for row in report["gap_classes"]} == REQUIRED_GAP_LABELS
    assert len(report["gap_classes"]) == 10


def test_gap_packet_report_preserves_posture_and_nonclaim_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["preserved_posture"] == {
        "qft_gr": "ladder_only_closure_not_authorized",
        "qft_gr_source_map_witness_chain_absent": True,
        "qft_gr_source_map_closure_authorized": False,
        "real_axiom_count": 60,
        "defaultNonAlias": "absent_from_unresolved_axiom_debt_and_lean_backed",
        "sampleRep32": "retained_spec_backed_axiom",
        "master_action": "candidate_dependency_surface_only",
        "dependency_audit": "nonpromotional_consumed",
    }
    assert report["classification_boundaries"] == {
        "solves_qft_gr_witness_chain": False,
        "authorizes_qft_gr_source_map_closure": False,
        "discharges_remaining_proof_debt": False,
        "derives_canonical_master_action": False,
        "authorizes_phase2": False,
        "claims_empirical_adequacy": False,
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


def test_master_action_dependency_gap_packet_live_ledger_still_matches_60_axioms() -> None:
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


def test_gap_packet_public_surfaces_are_synced() -> None:
    for path in PUBLIC_SURFACE_PATHS:
        text = _read(path)
        assert GAP_PACKET_EVIDENCE in text, f"{path} missing gap packet surface"
        assert REPORT_EVIDENCE in text, f"{path} missing gap packet report"
        assert RESULT_TOKEN in text, f"{path} missing result token"
        assert NEXT_TARGET in text, f"{path} missing next target"
        assert "lists the missing dependency classes" in text
        assert "does not solve any dependency" in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-MASTER-ACTION-DEPENDENCY-GAP-PACKET-v0" in inventory_text
    assert GAP_PACKET_EVIDENCE in inventory_text
    assert_focused_gate_not_manifest_enrolled(
        "test_master_action_dependency_gap_packet_gate.py"
    )
