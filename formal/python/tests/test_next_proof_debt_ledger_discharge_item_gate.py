from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_forbidden_promotions_closed,
    assert_frontier_matches_registry,
    assert_historical_target_recorded,
    assert_public_surfaces_match_registry,
    workstream,
)


REPO_ROOT = find_repo_root(Path(__file__))
SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "NextProofDebtLedgerDischargeItem.lean"
)
SOURCE_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterStatusSurfaceEnforcement.lean"
)
SOURCE_SELECTOR_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_STATUS_SURFACE_ENFORCEMENT_20260508_v0.json"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "NEXT_PROOF_DEBT_LEDGER_DISCHARGE_ITEM_20260505_v0.json"
)
LEDGER_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"
)
SOURCE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"

REPORT_ID = "NEXT_PROOF_DEBT_LEDGER_DISCHARGE_ITEM_20260505_v0"
SURFACE_ID = "next_proof_debt_ledger_discharge_item_v0"
CONSUMED_TARGET = "prepare_next_proof_debt_ledger_discharge_item"
NEXT_TARGET = "execute_selected_proof_debt_discharge_item"
CONSUMED_TOKEN = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_STATUS_SURFACE_ENFORCEMENT"
RESULT_TOKEN = "NEXT_PROOF_DEBT_LEDGER_DISCHARGE_ITEM_SELECTED"
SELECTED_LANE = "NEXT_PROOF_DEBT_LEDGER_DISCHARGE_ITEM"
ACTIVE_LANE = "next_proof_debt_ledger_discharge_item"
PREVIOUS_LANE = "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement"
SELECTED_DECLARATION = "sampleRep32"
SELECTED_FILE = "formal/toe_formal/ToeFormal/Variational/FNRepNonAliasEquivalence01.lean"
SELECTED_ITEM = f"{SELECTED_FILE}::{SELECTED_DECLARATION}"
CURRENT_AUTHORITY = "RETAINED_SPEC_BACKED_AXIOM"
INTENDED_AUTHORITY = "LEAN_BACKED_EXPLICIT_SAMPLE_REPRESENTATION_CONSTRUCTOR"
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_SELECTOR_EVIDENCE = str(SOURCE_SELECTOR_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
SOURCE_SELECTOR_REPORT_EVIDENCE = str(
    SOURCE_SELECTOR_REPORT_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
LEDGER_EVIDENCE = str(LEDGER_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_next_proof_debt_item_surface_selects_sample_rep32() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        SELECTED_LANE,
        NEXT_TARGET,
        SELECTED_ITEM,
        SELECTED_DECLARATION,
        SELECTED_FILE,
        CURRENT_AUTHORITY,
        INTENDED_AUTHORITY,
        "NextProofDebtLedgerDischargeItemStatus",
        "NextProofDebtLedgerDischargeItemDecision",
        "selectSampleRep32RetainedSpecBackedAxiom",
        "next_proof_debt_ledger_discharge_item_consumes_live_target_v0",
        "next_proof_debt_ledger_discharge_item_consumes_selector_token_v0",
        "next_proof_debt_ledger_discharge_item_exactly_one_item_v0",
        "next_proof_debt_ledger_discharge_item_selected_item_v0",
        "next_proof_debt_ledger_discharge_item_selected_declaration_v0",
        "next_proof_debt_ledger_discharge_item_selected_file_v0",
        "next_proof_debt_ledger_discharge_item_current_authority_v0",
        "next_proof_debt_ledger_discharge_item_intended_authority_v0",
        "next_proof_debt_ledger_discharge_item_result_token_v0",
        "next_proof_debt_ledger_discharge_item_next_target_v0",
    }:
        assert token in text

    assert "import ToeFormal.Derivation.NextProofDebtLedgerDischargeItem" in aggregate_text


def test_next_proof_debt_item_report_records_selected_authority() -> None:
    report = _json(REPORT_PATH)
    ledger = _read(LEDGER_PATH)
    source = _read(SOURCE_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_selection_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["selected_lane"] == SELECTED_LANE
    assert report["result_token"] == RESULT_TOKEN
    assert report["source_selector_surface"] == SOURCE_SELECTOR_EVIDENCE
    assert report["source_selector_report"] == SOURCE_SELECTOR_REPORT_EVIDENCE
    assert report["proof_debt_ledger"] == LEDGER_EVIDENCE
    assert report["selection_surface"] == SELECTION_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_next_proof_debt_ledger_discharge_item_gate.py"
    )
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_BOUNDED_PROOF_DEBT_ITEM"
    assert report["selection_executes_discharge"] is False
    assert report["selected_item_count"] == 1
    assert report["candidate_item_count"] == 3
    assert report["selected_debt_item"] == SELECTED_ITEM
    assert report["selected_declaration"] == SELECTED_DECLARATION
    assert report["selected_file"] == SELECTED_FILE
    assert report["ledger_status"] == "spec_backed"
    assert report["current_authority"] == CURRENT_AUTHORITY
    assert report["intended_authority"] == INTENDED_AUTHORITY
    assert report["associated_pillar_or_seam"] == "SCALAR_QFT"
    assert report["blocks_full_pillar_target"] == "no"
    assert report["next_target"] == NEXT_TARGET

    selected = [row for row in report["candidate_items"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["item"] == SELECTED_ITEM
    assert selected[0]["current_authority"] == CURRENT_AUTHORITY
    assert selected[0]["intended_authority"] == INTENDED_AUTHORITY

    assert f"| `{SELECTED_DECLARATION}` | `{SELECTED_FILE}` | `spec_backed` |" not in ledger
    assert "def sampleRep32 : Field2DRep32" in source
    assert "axiom sampleRep32" not in source
    assert "def defaultNonAlias" in source
    assert "axiom defaultNonAlias" not in source


def test_next_proof_debt_item_preserves_validation_and_nonclaims() -> None:
    text = _read(SELECTION_PATH)
    report = _json(REPORT_PATH)

    for token in {
        "next_proof_debt_ledger_discharge_item_read_only_preserved_v0",
        "next_proof_debt_ledger_discharge_item_freeze_preserved_v0",
        "next_proof_debt_ledger_discharge_item_mirror_parity_preserved_v0",
        "next_proof_debt_ledger_discharge_item_full_pytest_count_v0",
        "next_proof_debt_ledger_discharge_item_lean_jobs_v0",
        "next_proof_debt_ledger_discharge_item_axiom_count_v0",
        "next_proof_debt_ledger_discharge_item_default_nonalias_absent_v0",
        "next_proof_debt_ledger_discharge_item_sample_rep32_retained_v0",
        "next_proof_debt_ledger_discharge_item_qft_gr_not_authorized_v0",
        "next_proof_debt_ledger_discharge_item_does_not_discharge_item_v0",
        "next_proof_debt_ledger_discharge_item_master_action_not_promoted_v0",
        "next_proof_debt_ledger_discharge_item_no_pillar_completion_v0",
        "next_proof_debt_ledger_discharge_item_no_seam_closure_v0",
        "next_proof_debt_ledger_discharge_item_no_phase2_readiness_v0",
        "next_proof_debt_ledger_discharge_item_no_empirical_claim_v0",
        "next_proof_debt_ledger_discharge_item_no_canonical_toe_claim_v0",
        "next_proof_debt_ledger_discharge_item_manifest_not_enrolled_v0",
    }:
        assert token in text

    assert report["validation_checkpoint"] == {
        "full_pytest_passed": 6625,
        "full_pytest_skipped": 230,
        "lean_build_target": "ToeFormal",
        "lean_build_jobs": 7987,
        "governance_suite_passed": True,
        "git_diff_check_passed": True,
        "ordinary_validation_mode": "read_only_by_default",
    }
    assert report["preserved_enforcement"] == {
        "read_only_validation_preserved": True,
        "artifact_freeze_preserved": True,
        "active_live_target_mirror_parity_preserved": True,
        "loop_registry_canonical_source_preserved": True,
        "tracked_generated_output_mutation_forbidden_during_validation": True,
    }
    assert report["preserved_posture"]["real_axiom_count"] == 60
    assert report["preserved_posture"][
        "defaultNonAlias_absent_from_unresolved_axiom_debt"
    ] is True
    assert report["preserved_posture"][
        "sampleRep32_selected_from_retained_spec_backed_axiom"
    ] is True
    assert not any(report["nonclaim_boundaries"].values())


def test_registry_rotates_to_selected_proof_debt_execution() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()
    payload = _json(REGISTRY_PATH)
    assert_historical_target_recorded(
        payload=payload,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=SELECTION_EVIDENCE,
        lane=ACTIVE_LANE,
    )

    previous = workstream(PREVIOUS_LANE, payload)
    assert previous["status"] == "paused"
    assert previous["result_token"] == CONSUMED_TOKEN
    assert previous["selected_next_target"] == CONSUMED_TARGET

    active = workstream(ACTIVE_LANE, payload)
    assert active["status"] == "paused"
    assert active["authorization_evidence"] == SELECTION_EVIDENCE
    assert active["authorized_next_slice"] == "selected_proof_debt_discharge_item_execution_v0"
    assert active["authorized_next_strict_target"] == NEXT_TARGET
    assert active["consumed_target"] == CONSUMED_TARGET
    assert active["latest_surface"] == SURFACE_ID
    assert active["source_selector_surface"] == SOURCE_SELECTOR_EVIDENCE
    assert active["source_selector_report"] == SOURCE_SELECTOR_REPORT_EVIDENCE
    assert active["selection_report"] == REPORT_EVIDENCE
    assert active["consumed_selector_token"] == CONSUMED_TOKEN
    assert active["result_token"] == RESULT_TOKEN
    assert active["selected_lane"] == SELECTED_LANE
    assert active["selected_next_target"] == NEXT_TARGET
    assert active["selected_next_target_kind"] == "proof_debt_item_execution"
    assert active["selection_executes_discharge"] == "no"
    assert active["selected_debt_item"] == SELECTED_ITEM
    assert active["selected_declaration"] == SELECTED_DECLARATION
    assert active["selected_file"] == SELECTED_FILE
    assert active["current_authority"] == CURRENT_AUTHORITY
    assert active["intended_authority"] == INTENDED_AUTHORITY
    assert active["selected_item_count"] == 1
    assert active["qft_gr_source_map_closure_authorized"] == "no"
    assert active["master_action_promotion_authorized"] == "no"
    assert active["pillar_completion_inferred"] == "no"
    assert active["seam_closure_claim"] == "no"
    assert active["phase2_readiness_claim"] == "no"
    assert active["empirical_adequacy_claim"] == "no"
    assert active["canonical_toe_claim"] == "no"
    assert active["governance_manifest_enrollment_authorized"] == "no"


def test_next_proof_debt_item_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_next_proof_debt_ledger_discharge_item_gate.py"
    )
