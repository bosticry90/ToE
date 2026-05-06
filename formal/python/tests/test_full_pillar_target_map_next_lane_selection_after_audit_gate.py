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
    / "FullPillarTargetMapNextLaneSelectionAfterAudit.lean"
)
POST_AUDIT_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostAxiomLedgerAuditBoundedAttackSelection.lean"
)
TARGET_MAP_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapRebase.lean"
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
    / "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_AUDIT_20260503_v0.json"
)
POST_AUDIT_SELECTION_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_AXIOM_LEDGER_AUDIT_BOUNDED_ATTACK_SELECTION_20260503_v0.json"
)
TARGET_MAP_DOC_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "FULL_PILLAR_TARGET_MAP_REBASE_v0.md"
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

REPORT_ID = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_AUDIT_20260503_v0"
SURFACE_ID = "full_pillar_target_map_next_lane_selection_after_audit_v0"
CONSUMED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
CONSUMED_TOKEN = "POST_AXIOM_LEDGER_AUDIT_NEXT_ATTACK_SELECTED"
RESULT_TOKEN = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_AUDIT"
SELECTED_LANE = "MASTER_ACTION_DEPENDENCY_AUDIT"
SELECTED_TARGET = "prepare_master_action_dependency_audit"
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
POST_AUDIT_SELECTION_EVIDENCE = str(
    POST_AUDIT_SELECTION_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
POST_AUDIT_SELECTION_REPORT_EVIDENCE = str(
    POST_AUDIT_SELECTION_REPORT_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
TARGET_MAP_EVIDENCE = str(TARGET_MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
TARGET_MAP_DOC_EVIDENCE = str(TARGET_MAP_DOC_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
LEDGER_EVIDENCE = str(LEDGER_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_EVIDENCE = str(SOURCE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
CANDIDATE_CLASSES = {
    "QFT_GR_WITNESS_SEARCH_PLAN",
    "GR_WEAK_FIELD_SOURCE_SIDE_OBLIGATION_LANE",
    "QM_STAT_THEOREM_GAP_RE_ENTRY_LANE",
    "SR_COSMO_GLOBAL_OBSTRUCTION_FOLLOW_UP",
    "MASTER_ACTION_DEPENDENCY_AUDIT",
    "PROOF_DEBT_LEDGER_DISCHARGE_LANE",
    "PILLAR_MAP_STALE_TARGET_SYNCHRONIZATION_LANE",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_after_audit_full_pillar_selector_surface_selects_master_action_audit() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        SELECTED_LANE,
        SELECTED_TARGET,
        "FullPillarTargetMapNextLaneSelectionAfterAuditStatus",
        "FullPillarTargetMapNextLaneSelectionAfterAuditDecision",
        "selectMasterActionDependencyAudit",
        "full_pillar_target_map_next_lane_selection_after_audit_consumes_return_target_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_consumes_selector_token_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_rows_evaluated_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_ledger_attached_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_exactly_one_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_result_token_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_selected_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_selected_target_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_decision_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_candidate_count_v0",
    } | CANDIDATE_CLASSES:
        assert token in text

    assert (
        "import ToeFormal.Derivation.FullPillarTargetMapNextLaneSelectionAfterAudit"
        in aggregate_text
    )


def test_after_audit_full_pillar_selector_surface_carries_60_axiom_posture() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "full_pillar_target_map_next_lane_selection_after_audit_axiom_count_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_default_nonalias_absent_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_sample_rep32_retained_v0",
        "real_axiom_count_confirmed",
        "default_nonalias_absent_from_unresolved_axiom_debt",
        "sample_rep32_retained",
    }:
        assert token in text


def test_after_audit_full_pillar_selector_surface_preserves_nonclaim_boundaries() -> None:
    text = _read(SELECTION_PATH)

    for theorem in {
        "full_pillar_target_map_next_lane_selection_after_audit_does_not_execute_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_qft_gr_witness_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_proof_debt_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_master_action_not_promoted_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_no_pillar_completion_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_no_seam_closure_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_no_phase2_readiness_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_no_empirical_adequacy_v0",
        "full_pillar_target_map_next_lane_selection_after_audit_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_after_audit_full_pillar_selection_report_records_master_action_audit() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_selection_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["post_audit_selection_surface"] == POST_AUDIT_SELECTION_EVIDENCE
    assert report["post_audit_selection_report"] == POST_AUDIT_SELECTION_REPORT_EVIDENCE
    assert report["target_map_surface"] == TARGET_MAP_EVIDENCE
    assert report["target_map_document"] == TARGET_MAP_DOC_EVIDENCE
    assert report["proof_debt_ledger"] == LEDGER_EVIDENCE
    assert report["selection_surface"] == SELECTION_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/"
        "test_full_pillar_target_map_next_lane_selection_after_audit_gate.py"
    )
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_LANE"
    assert report["selection_executes_lane"] is False
    assert report["selection_count"] == 1
    assert report["candidate_lane_count"] == 7
    assert report["selected_lane"] == SELECTED_LANE
    assert report["selected_next_target"] == SELECTED_TARGET
    assert (
        report["selected_next_target_kind"]
        == "master_action_dependency_audit_preparation_only"
    )

    selected = [row for row in report["candidate_classes"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["class_id"] == SELECTED_LANE
    assert selected[0]["candidate_target"] == SELECTED_TARGET
    assert {row["class_id"] for row in report["candidate_classes"]} == CANDIDATE_CLASSES

    assert report["refreshed_ledger_posture"] == {
        "real_axiom_count": 60,
        "real_sorry_or_admit_count": 0,
        "real_axiom_file_count": 15,
        "defaultNonAlias": "absent_from_unresolved_axiom_debt_and_lean_backed",
        "sampleRep32": "retained_spec_backed_axiom",
    }
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_after_audit_full_pillar_selector_live_ledger_still_matches_60_axioms() -> None:
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


def test_after_audit_full_pillar_selection_report_preserves_nonclaim_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["nonclaim_boundaries"] == {
        "qft_gr_witness_search_selected": False,
        "proof_debt_discharge_item_selected": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "master_action_promotion_authorized": False,
        "selection_executes_lane": False,
        "governance_manifest_enrollment_authorized": False,
    }
    assert (
        report["acceptance_condition"]
        == "The selector consumes the post-audit return target, evaluates eligible "
        "lanes from the full pillar target map using the refreshed 60-real-axiom "
        "posture, selects exactly one next bounded lane, and does not infer "
        "pillar completion, seam closure, Phase 2 readiness, empirical adequacy, "
        "or master-action promotion."
    )


def test_after_audit_full_pillar_selection_public_surfaces_and_manifest_posture() -> None:
    for path in [
        README_PATH,
        STATE_PATH,
        ROADMAP_PATH,
        STRICT_MAP_PATH,
        SEAM_REGISTRY_PATH,
        SEAM_INVENTORY_PATH,
    ]:
        text = _read(path)
        assert SELECTION_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert RESULT_TOKEN in text
        assert SELECTED_TARGET in text
        assert SELECTED_LANE in text

    inventory = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-FULL-PILLAR-TARGET-MAP-NEXT-LANE-SELECTION-AFTER-AUDIT-v0" in inventory
    assert SELECTION_EVIDENCE in inventory
    assert REPORT_EVIDENCE in inventory
    assert SELECTED_TARGET in inventory
    assert RESULT_TOKEN in inventory

    assert_focused_gate_not_manifest_enrolled(
        "test_full_pillar_target_map_next_lane_selection_after_audit_gate.py"
    )
