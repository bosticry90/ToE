from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal/docs/release"
PROGRAM_ID = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"
EXIT_TARGET = "close_toe_targeted_ccft_closure_evidence_recovery_v0_after_bounded_result_v0"
OUTCOME = "TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERED"
RESULT = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_RESULT_v0.json"
REVIEW = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_REVIEW_v0.json"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"

def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def test_exit_preserves_positive_result_four_contracts_and_three_conflicts() -> None:
    result = read(RESULT)
    assert result["terminal_outcome"] == OUTCOME
    assert result["scientific_result"]["recovered_contract_count"] == 4
    assert result["scientific_result"]["cp_nlse_conflict_count"] == 3

def test_historical_recovery_is_complete_without_exhaustion_claim() -> None:
    science = read(RESULT)["scientific_result"]
    assert science["historical_recovery"] == "COMPLETE_FOR_CCFT_V0"
    assert science["repository_claim_exhaustion"] == "NOT_ESTABLISHED"
    assert science["further_archive_search"] == "NOT_AUTHORIZED"

def test_no_branch_model_postulate_theorem_or_construction_authority() -> None:
    result = read(RESULT)
    assert result["scientific_result"]["branch_selected"] == "NONE"
    assert result["scientific_result"]["closed_ccft_v0_model"] == "NONE"
    assert result["scientific_result"]["new_postulates"] == "NONE"
    assert all(value is False for value in result["nonpromotion_boundary"].values())
    assert result["future_decision_boundary"]["construction_preparation_authorized"] is False

def test_review_accepts_and_source_hashes_reproduce() -> None:
    review = read(REVIEW)
    assert review["accepted"] is True
    assert review["reviewed_result"]["sha256"] == sha(RESULT)
    assert all(review["checks"].values())

def test_registry_is_terminal_at_mandatory_exit() -> None:
    registry = read(REGISTRY)
    program = registry["bounded_programs_v1"][PROGRAM_ID]
    assert program["mandatory_exit_completed"] is True
    assert program["program_terminal_status"] == "CLOSED_AFTER_MANDATORY_EXIT"
    assert program["program_terminal_outcome"] == OUTCOME
    assert program["construction_preparation_authorized"] is False
    assert registry["current_projection_v0"]["current_target"] == EXIT_TARGET
