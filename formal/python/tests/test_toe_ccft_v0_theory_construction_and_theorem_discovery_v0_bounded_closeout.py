from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal/docs/release"
PROGRAM_ID = "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"
EXIT_TARGET = "close_toe_ccft_v0_theory_construction_and_theorem_discovery_v0_after_bounded_result_v0"
OUTCOME = "CCFT_V0_EQUIVALENT_TO_KNOWN_MODEL"
RESULT = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_RESULT_v0.json"
REVIEW = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_REVIEW_v0.json"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"

def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def test_exit_preserves_known_model_outcome_and_baseline_role() -> None:
    result = read(RESULT)
    assert result["terminal_outcome"] == OUTCOME
    assert result["scientific_result"]["earned_role"] == "KNOWN_MODEL_EQUIVALENT_CCFT_COMPUTATIONAL_BASELINE"
    assert result["scientific_result"]["frozen_model"] == "PRESERVED"

def test_mathematical_physical_and_empirical_boundaries_remain_exact() -> None:
    science = read(RESULT)["scientific_result"]
    assert science["mathematical_novelty"] == "NOT_ESTABLISHED"
    assert science["full_PDE_viability"] == "NOT_INDEPENDENTLY_ADJUDICATED"
    assert science["physical_interpretation"] == "NONE"
    assert science["empirical_promotion"] == "NONE"

def test_broader_ccft_and_lcrd_are_preserved_without_adjudication() -> None:
    science = read(RESULT)["scientific_result"]
    assert science["broader_CCFT"] == "UNREFUTED_BUT_UNESTABLISHED"
    assert science["LCRD_v3"] == "PRESERVED_INCOMPLETE_UNADJUDICATED"

def test_no_scientific_successor_is_selected_or_authorized() -> None:
    result = read(RESULT)
    assert result["future_decision_boundary"]["future_route_selected"] == "NONE"
    assert result["future_decision_boundary"]["scientific_successor_authorized"] is False
    assert all(value is False for value in result["nonpromotion_boundary"].values())

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
    assert program["proposed_successor_authorized"] is False
    assert registry["current_projection_v0"]["current_target"] == EXIT_TARGET
