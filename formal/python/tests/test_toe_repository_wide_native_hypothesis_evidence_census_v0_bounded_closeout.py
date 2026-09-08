from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
RESULT_PATH = (
    RELEASE_ROOT
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0_BOUNDED_CLOSEOUT_RESULT_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0_BOUNDED_CLOSEOUT_REVIEW_v0.json"
)
STAGE_5_RESULT_PATH = (
    RELEASE_ROOT / "TOE_POST_CENSUS_NATIVE_FRONTIER_DECISION_RESULT_v0.json"
)
STAGE_5_REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_POST_CENSUS_NATIVE_FRONTIER_DECISION_RESULT_REVIEW_v0.json"
)
REGISTRY_PATH = RELEASE_ROOT / "LOOP_CONTROL_REGISTRY_v0.json"

PROGRAM_ID = "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0"
MANDATORY_EXIT = (
    "close_toe_repository_wide_native_hypothesis_evidence_census_v0_"
    "after_bounded_result_v0"
)
SELECTED_HYPOTHESIS = (
    "HYP_TOE_NATIVE_GRAVITATIONAL_PRINCIPLE_ACTION_SELECTION_v0"
)
PROPOSED_SURVEY = (
    "prepare_toe_native_gravitational_requirements_and_candidate_action_"
    "family_survey_bounded_program_v0"
)
TERMINAL_KIND = (
    "toe_repository_wide_native_hypothesis_evidence_census_v0_"
    "terminal_closeout"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_closeout_binds_the_accepted_stage_five_result() -> None:
    result = _read(RESULT_PATH)
    source = result["source_bindings"]
    assert source["stage_5_result_sha256"] == _sha256(STAGE_5_RESULT_PATH)
    assert source["stage_5_review_sha256"] == _sha256(STAGE_5_REVIEW_PATH)
    stage_5 = _read(STAGE_5_RESULT_PATH)
    assert stage_5["selection_decision"]["hypothesis_id"] == SELECTED_HYPOTHESIS
    assert stage_5["selection_decision"]["immediate_prerequisite_count"] == 1
    assert stage_5["nonclaim_boundary"]["canonical_evidence_promoted"] is False


def test_closeout_preserves_the_bounded_nonpromotion_boundary() -> None:
    result = _read(RESULT_PATH)
    census = result["census_result"]
    successor = result["successor_boundary"]
    assert census["bounded_review_status"] == "COMPLETE_FOR_THE_BOUNDED_REVIEW"
    assert census["repository_claim_exhaustion_established"] is False
    assert census["canonical_evidence_promoted"] is False
    assert census["selected_frontier"]["hypothesis_id"] == SELECTED_HYPOTHESIS
    assert census["selected_frontier"]["readiness"] == "AFTER_ONE_PREREQUISITE"
    assert successor["proposed_future_preparation_target"] == PROPOSED_SURVEY
    assert successor["candidate_gravitational_action_selected"] is False
    assert successor["native_gravitational_action_established"] is False
    assert successor["gravitational_survey_authorized"] is False
    assert successor["gravitational_survey_opened"] is False
    assert successor["successor_program_authorized"] is False
    assert successor["successor_program_opened"] is False


def test_all_five_attempts_are_terminal_without_repair() -> None:
    result = _read(RESULT_PATH)
    closeout = result["program_closeout"]
    stages = result["census_result"]["stage_results"]
    assert [item["attempt"] for item in stages] == [1, 2, 3, 4, 5]
    assert all(item["terminal_result"] == "PASSED" for item in stages)
    assert closeout["attempted_stage_count"] == 5
    assert closeout["authorized_stage_count"] == 5
    assert closeout["event_chain_event_count"] == 10
    assert closeout["last_closed_attempt_number"] == 5
    assert closeout["blocked_stage_id"] is None
    assert closeout["repair_attempt_count"] == 0
    assert closeout["mandatory_exit_completed"] is True
    assert closeout["program_terminal_status"] == "CLOSED_AFTER_MANDATORY_EXIT"


def test_independent_review_accepts_every_closeout_check() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["program_terminal"] is True
    assert review["automatic_successor_selected"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
    assert review["reviewed_result"]["sha256"] == _sha256(RESULT_PATH)


def test_registry_is_a_terminal_projection_of_the_closeout() -> None:
    registry = _read(REGISTRY_PATH)
    program = registry["bounded_programs_v1"][PROGRAM_ID]
    projection = registry["current_projection_v0"]
    assert program["state"] == "CLOSED"
    assert program["mandatory_exit_selected"] is True
    assert program["mandatory_exit_completed"] is True
    assert program["program_terminal_status"] == "CLOSED_AFTER_MANDATORY_EXIT"
    assert program["repository_claim_exhaustion_established"] is False
    assert program["canonical_evidence_promoted"] is False
    assert program["selected_frontier_hypothesis_id"] == SELECTED_HYPOTHESIS
    assert program["proposed_future_preparation_target"] == PROPOSED_SURVEY
    assert program["proposed_future_target_authorized"] is False
    assert program["proposed_future_target_opened"] is False
    assert program["native_gravitational_action_selected"] is False
    assert projection["current_target"] == MANDATORY_EXIT
    assert projection["current_target_kind"] == TERMINAL_KIND
    assert projection["current_target_evidence"].endswith(
        "ToeRepositoryWideNativeHypothesisEvidenceCensusV0BoundedCloseout.lean"
    )
    assert projection["current_target_report"] == REVIEW_PATH.relative_to(
        REPO_ROOT
    ).as_posix()

