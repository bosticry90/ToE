from __future__ import annotations

import hashlib
import json
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal/docs/release"
PROGRAM_ID = "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0"
EXIT_TARGET = "close_toe_native_gravitational_requirements_and_candidate_action_family_survey_v0_after_bounded_result_v0"
TERMINAL = "NO_PRESERVED_CANDIDATE_SATISFIES_NATIVE_REQUIREMENTS"
ROUTE = "DERIVE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE"
RESULT = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_RESULT_v0.json"
REVIEW = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_REVIEW_v0.json"
STAGE5 = RELEASE / "TOE_GRAVITATIONAL_ACTION_FAMILY_ELIGIBILITY_HANDOFF_RESULT_v0.json"
STAGE5_REVIEW = RELEASE / "TOE_GRAVITATIONAL_ACTION_FAMILY_ELIGIBILITY_HANDOFF_RESULT_REVIEW_v0.json"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"

def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def test_closeout_binds_stage_five_without_changing_its_result() -> None:
    result = read(RESULT)
    stage5 = read(STAGE5)
    assert result["source_bindings"]["stage_5_result_sha256"] == sha(STAGE5)
    assert result["source_bindings"]["stage_5_review_sha256"] == sha(STAGE5_REVIEW)
    assert stage5["terminal_outcome"] == TERMINAL
    assert stage5["selected_route"] == ROUTE
    assert result["source_bindings"]["event_chain_changed_by_mandatory_exit"] is False

def test_closeout_preserves_zero_eligible_actions_and_family_roles() -> None:
    survey = read(RESULT)["survey_result"]
    assert survey["eligible_native_action_family_count"] == 0
    assert survey["family_eligibility_summary"]["F_EH"] == "PROVISIONAL_BASELINE_ONLY"
    assert survey["family_eligibility_summary"]["F_QUADRATIC"] == "REFERENCE_CONTROL_ONLY"
    assert survey["family_eligibility_summary"]["F_EQUIVALENCE_PROBE"] == "NOT_APPLICABLE_NOT_AN_ACTION"
    assert sum(value == "BLOCKED_BY_MISSING_DEFINITION" for value in survey["family_eligibility_summary"].values()) == 4

def test_all_five_attempts_are_terminal_without_repair() -> None:
    result = read(RESULT)
    closeout = result["program_closeout"]
    stages = result["survey_result"]["stage_results"]
    assert [row["attempt"] for row in stages] == [1, 2, 3, 4, 5]
    assert all(row["terminal_result"] == "PASSED" for row in stages)
    assert closeout["event_chain_event_count"] == 10
    assert closeout["repair_attempt_count"] == 0
    assert closeout["mandatory_exit_completed"] is True
    assert closeout["program_terminal_status"] == "CLOSED_AFTER_MANDATORY_EXIT"

def test_independent_review_accepts_every_closeout_check() -> None:
    review = read(REVIEW)
    assert review["accepted"] is True
    assert review["program_terminal"] is True
    assert review["automatic_successor_selected"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
    assert review["reviewed_result"]["sha256"] == sha(RESULT)

def test_registry_is_terminal_without_successor_authority() -> None:
    registry = read(REGISTRY)
    program = registry["bounded_programs_v1"][PROGRAM_ID]
    projection = registry["current_projection_v0"]
    assert program["state"] == "CLOSED"
    assert program["mandatory_exit_completed"] is True
    assert program["program_terminal_status"] == "CLOSED_AFTER_MANDATORY_EXIT"
    assert program["eligible_native_action_family_count"] == 0
    assert program["selected_post_survey_route"] == ROUTE
    assert program["native_gravitational_principle_selected_or_derived"] is False
    assert program["native_gravitational_action_selected_or_adopted"] is False
    assert program["proposed_successor_authorized"] is False
    assert program["proposed_successor_installed"] is False
    assert program["proposed_successor_opened"] is False
    assert projection["current_target"] == EXIT_TARGET
    assert projection["current_target_kind"].endswith("survey_v0_terminal_closeout")
    assert projection["current_target_report"] == REVIEW.relative_to(REPO_ROOT).as_posix()
