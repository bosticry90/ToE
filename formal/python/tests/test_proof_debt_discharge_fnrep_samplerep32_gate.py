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
    assert_public_surfaces_match_registry,
    workstream,
)


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01.lean"
)
DISCHARGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01SampleRep32Discharge.lean"
)
SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "NextProofDebtLedgerDischargeItem.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROOF_DEBT_DISCHARGE_FNREP_SAMPLEREP32_20260505_v0.json"
)
SELECTOR_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "NEXT_PROOF_DEBT_LEDGER_DISCHARGE_ITEM_20260505_v0.json"
)
LEDGER_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"

SOURCE_EVIDENCE = str(SOURCE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
DISCHARGE_EVIDENCE = str(DISCHARGE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SELECTOR_EVIDENCE = str(SELECTOR_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SELECTOR_REPORT_EVIDENCE = str(
    SELECTOR_REPORT_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
LEDGER_EVIDENCE = str(LEDGER_PATH.relative_to(REPO_ROOT)).replace("\\", "/")

SURFACE_ID = "fnrep_nonalias_samplerep32_discharge_v0"
EXECUTION_TARGET = "execute_selected_proof_debt_discharge_item"
REVIEW_TARGET = "review_fnrep_nonalias_samplerep32_discharge_result"
SELECTOR_TOKEN = "NEXT_PROOF_DEBT_LEDGER_DISCHARGE_ITEM_SELECTED"
RESULT_TOKEN = "FNREP_NONALIAS_SAMPLEREP32_DISCHARGED_LEAN_BACKED_CONSTRUCTOR"
FALLBACK_TOKEN = "FNREP_NONALIAS_SAMPLEREP32_RETAINED_NOT_DISCHARGED"
SELECTED_ITEM = f"{SOURCE_EVIDENCE}::sampleRep32"
ACTIVE_LANE = "fnrep_nonalias_samplerep32_discharge"
PREVIOUS_LANE = "next_proof_debt_ledger_discharge_item"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_sample_rep32_axiom_is_replaced_by_explicit_constructor() -> None:
    source = _read(SOURCE_PATH)
    aggregate = _read(AGGREGATE_PATH)

    assert "axiom sampleRep32" not in source
    for token in {
        "def sampleRep32 : Field2DRep32",
        "Quot.mk RepSetoid32",
        "theorem sampleRep32_eq_defaultRep32",
        "theorem nonAliasSample_eq_sampleRep32_false",
        "theorem nonAliasSample_tag_false",
        "theorem diagnosticNonAlias_not_eligible",
    }:
        assert token in source

    assert (
        "import ToeFormal.Variational.FNRepNonAliasEquivalence01SampleRep32Discharge"
        in aggregate
    )


def test_sample_rep32_discharge_surface_records_successful_result() -> None:
    text = _read(DISCHARGE_PATH)

    for token in {
        SURFACE_ID,
        EXECUTION_TARGET,
        REVIEW_TARGET,
        SELECTOR_TOKEN,
        RESULT_TOKEN,
        FALLBACK_TOKEN,
        REPORT_EVIDENCE,
        "selectedNextProofDebtLedgerItemV0",
        "sampleRep32_explicit_quotient_constructor",
        "FNRepSampleRep32DischargeStatus",
        "sampleRep32_discharge_eq_defaultRep32",
        "nonAliasSample_discharge_tag_false",
        "nonAliasSample_discharge_roundtrip",
        "fnrep_samplerep32_discharge_consumes_live_target_v0",
        "fnrep_samplerep32_discharge_consumes_selector_token_v0",
        "fnrep_samplerep32_discharge_selected_item_v0",
        "fnrep_samplerep32_discharge_lean_backed_v0",
        "fnrep_samplerep32_discharge_result_token_v0",
        "fnrep_samplerep32_discharge_axiom_count_v0",
        "fnrep_samplerep32_discharge_axiom_removed_v0",
    }:
        assert token in text

    for theorem in {
        "fnrep_samplerep32_discharge_qft_gr_not_authorized_v0",
        "fnrep_samplerep32_discharge_master_action_not_promoted_v0",
        "fnrep_samplerep32_discharge_no_pillar_completion_v0",
        "fnrep_samplerep32_discharge_no_seam_closure_v0",
        "fnrep_samplerep32_discharge_no_phase2_readiness_v0",
        "fnrep_samplerep32_discharge_no_empirical_claim_v0",
        "fnrep_samplerep32_discharge_no_canonical_toe_claim_v0",
        "fnrep_samplerep32_discharge_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_sample_rep32_discharge_report_and_ledger_record_axiom_count_drop() -> None:
    report = _json(REPORT_PATH)
    ledger = _read(LEDGER_PATH)

    assert report["schema_id"] == "PROOF_DEBT_DISCHARGE_FNREP_SAMPLEREP32_20260505_v0"
    assert report["execution_status"] == "completed_successful_discharge"
    assert report["current_target"] == EXECUTION_TARGET
    assert report["consumed_selector_token"] == SELECTOR_TOKEN
    assert report["selected_debt_item"] == SELECTED_ITEM
    assert report["selector_surface"] == SELECTOR_EVIDENCE
    assert report["selector_report"] == SELECTOR_REPORT_EVIDENCE
    assert report["discharge_surface"] == DISCHARGE_EVIDENCE
    assert report["proof_debt_ledger"] == LEDGER_EVIDENCE
    assert report["result_token"] == RESULT_TOKEN
    assert report["fallback_token_not_used"] == FALLBACK_TOKEN
    assert report["prior_authority"] == "RETAINED_SPEC_BACKED_AXIOM"
    assert (
        report["resulting_authority"]
        == "LEAN_BACKED_EXPLICIT_SAMPLE_REPRESENTATION_CONSTRUCTOR"
    )
    assert report["axiom_removed"] is True
    assert report["ledger_row_removed"] is True
    assert report["real_axiom_count_before"] == 60
    assert report["real_axiom_count_after"] == 59
    assert report["next_target"] == REVIEW_TARGET
    assert not any(report["nonclaim_boundaries"].values())

    assert "real_axiom_count_v0: 59" in ledger
    assert f"| `sampleRep32` | `{SOURCE_EVIDENCE}` |" not in ledger


def test_registry_rotates_to_sample_rep32_discharge_result_review() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()
    payload = _json(REGISTRY_PATH)
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == EXECUTION_TARGET
    assert state["live_next_target"] == REVIEW_TARGET
    assert state["live_next_target_evidence"] == DISCHARGE_EVIDENCE
    assert state["active_lane"] == ACTIVE_LANE
    assert PREVIOUS_LANE in state["paused_lanes"]

    previous = workstream(PREVIOUS_LANE, payload)
    assert previous["status"] == "paused"
    assert previous["result_token"] == SELECTOR_TOKEN
    assert previous["selected_next_target"] == EXECUTION_TARGET

    active = workstream(ACTIVE_LANE, payload)
    assert active["status"] == "active"
    assert active["authorization_evidence"] == DISCHARGE_EVIDENCE
    assert active["authorized_next_slice"] == (
        "fnrep_nonalias_samplerep32_discharge_result_review_v0"
    )
    assert active["authorized_next_strict_target"] == REVIEW_TARGET
    assert active["consumed_target"] == EXECUTION_TARGET
    assert active["latest_surface"] == SURFACE_ID
    assert active["selector_surface"] == SELECTOR_EVIDENCE
    assert active["selector_report"] == SELECTOR_REPORT_EVIDENCE
    assert active["execution_report"] == REPORT_EVIDENCE
    assert active["proof_debt_ledger"] == LEDGER_EVIDENCE
    assert active["consumed_selector_token"] == SELECTOR_TOKEN
    assert active["result_token"] == RESULT_TOKEN
    assert active["fallback_token_not_used"] == FALLBACK_TOKEN
    assert active["selected_debt_item"] == SELECTED_ITEM
    assert active["prior_authority"] == "RETAINED_SPEC_BACKED_AXIOM"
    assert (
        active["resulting_authority"]
        == "LEAN_BACKED_EXPLICIT_SAMPLE_REPRESENTATION_CONSTRUCTOR"
    )
    assert active["real_axiom_count_before"] == 60
    assert active["real_axiom_count_after"] == 59
    assert active["axiom_removed"] == "yes"
    assert active["ledger_row_removed"] == "yes"
    assert active["debt_item_discharged"] == "yes"
    assert active["qft_gr_source_map_closure_authorized"] == "no"
    assert active["master_action_promotion_authorized"] == "no"
    assert active["pillar_completion_inferred"] == "no"
    assert active["seam_closure_claim"] == "no"
    assert active["phase2_readiness_claim"] == "no"
    assert active["empirical_adequacy_claim"] == "no"
    assert active["canonical_toe_claim"] == "no"
    assert active["governance_manifest_enrollment_authorized"] == "no"

    assert REVIEW_TARGET in payload["next_strict_target_coverage"]
    assert (
        "sampleRep32_discharged_pending_result_review_no_promotion"
        in payload["retained_blocker_coverage"]
    )


def test_sample_rep32_discharge_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_proof_debt_discharge_fnrep_samplerep32_gate.py"
    )
