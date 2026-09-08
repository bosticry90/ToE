from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal/docs/release"
PROGRAM_ID = "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_V0"
EXIT_TARGET = (
    "close_toe_positive_native_gravitational_principle_derivation_v0_"
    "after_bounded_result_v0"
)
TERMINAL = "EXISTING_NATIVE_ARCHITECTURE_DOES_NOT_SUPPLY_POSITIVE_GRAVITY_PRINCIPLE"
RESULT = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_RESULT_v0.json"
REVIEW = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_REVIEW_v0.json"
STAGE1 = RELEASE / "TOE_POSITIVE_GRAVITATIONAL_PRINCIPLE_SOURCE_INVENTORY_RESULT_v0.json"
STAGE1_REVIEW = RELEASE / (
    "TOE_POSITIVE_GRAVITATIONAL_PRINCIPLE_SOURCE_INVENTORY_RESULT_REVIEW_v0.json"
)
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_closeout_binds_stage_one_without_changing_its_blocked_result() -> None:
    result = read(RESULT)
    stage1 = read(STAGE1)
    assert result["source_bindings"]["stage_1_result_sha256"] == sha(STAGE1)
    assert result["source_bindings"]["stage_1_review_sha256"] == sha(STAGE1_REVIEW)
    assert stage1["terminal_outcome"] == "NO_SOURCE_BOUND_POSITIVE_PRINCIPLE_CANDIDATE_FOUND"
    assert stage1["lifecycle_result"] == "BLOCKED"
    assert result["source_bindings"]["event_chain_changed_by_mandatory_exit"] is False


def test_closeout_preserves_zero_candidates_and_scope_limitation() -> None:
    science = read(RESULT)["scientific_result"]
    assert science["positive_generative_principle_candidate_count"] == 0
    assert science["action_class_constraining_principle_candidate_count"] == 0
    assert science["positive_native_gravitational_principle"] == "NONE"
    assert science["permitted_native_gravitational_action_class"] == "NONE"
    assert science["native_gravitational_action"] == "NONE"
    assert science["repository_claim_exhaustion"] == "NOT_ESTABLISHED"
    assert science["unreviewed_custody_record_count"] == 12923


def test_only_stage_one_was_attempted_and_later_stages_are_prohibited() -> None:
    result = read(RESULT)
    closeout = result["program_closeout"]
    stages = result["scientific_result"]["stage_results"]
    assert len(stages) == 1
    assert stages[0]["attempt"] == 1
    assert stages[0]["terminal_result"] == "BLOCKED"
    assert closeout["event_chain_event_count"] == 2
    assert closeout["repair_attempt_count"] == 0
    assert len(closeout["unattempted_stage_ids"]) == 4
    assert closeout["unattempted_stages_prohibited"] is True
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


def test_registry_is_terminal_without_principle_action_or_successor() -> None:
    registry = read(REGISTRY)
    program = registry["bounded_programs_v1"][PROGRAM_ID]
    projection = registry["current_projection_v0"]
    assert program["state"] == "CLOSED"
    assert program["blocked_stage_id"] == "POSITIVE_GRAVITATIONAL_PRINCIPLE_SOURCE_INVENTORY"
    assert program["mandatory_exit_completed"] is True
    assert program["program_terminal_status"] == "CLOSED_AFTER_MANDATORY_EXIT"
    assert program["program_terminal_outcome"] == TERMINAL
    assert program["positive_principle_candidate_count"] == 0
    assert program["positive_native_gravitational_principle_selected_or_derived"] is False
    assert program["permitted_native_action_class_derived_or_selected"] is False
    assert program["native_gravitational_action_constructed_selected_or_adopted"] is False
    assert program["future_route_selected"] == "NONE"
    assert program["proposed_successor_authorized"] is False
    assert program["proposed_successor_installed"] is False
    assert program["proposed_successor_opened"] is False
    assert projection["current_target"] == EXIT_TARGET
    assert projection["current_target_kind"].endswith("derivation_v0_terminal_closeout")
    assert projection["current_target_report"] == REVIEW.relative_to(REPO_ROOT).as_posix()
