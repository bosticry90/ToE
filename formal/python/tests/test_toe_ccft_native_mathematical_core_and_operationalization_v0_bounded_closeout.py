from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal/docs/release"
PROGRAM_ID = "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0"
EXIT_TARGET = (
    "close_toe_ccft_native_mathematical_core_and_operationalization_v0_"
    "after_bounded_result_v0"
)
TERMINAL = "NO_CLOSED_CCFT_MATHEMATICAL_CORE_RECOVERED"
RESULT = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_RESULT_v0.json"
REVIEW = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_REVIEW_v0.json"
STAGE4 = RELEASE / "TOE_MINIMAL_CLOSED_CCFT_CORE_DECISION_RESULT_v0.json"
STAGE4_REVIEW = RELEASE / "TOE_MINIMAL_CLOSED_CCFT_CORE_DECISION_RESULT_REVIEW_v0.json"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_closeout_binds_stage_four_without_changing_its_blocked_result() -> None:
    result = read(RESULT)
    stage4 = read(STAGE4)
    assert result["source_bindings"]["stage_4_result_sha256"] == sha(STAGE4)
    assert result["source_bindings"]["stage_4_review_sha256"] == sha(STAGE4_REVIEW)
    assert stage4["terminal_outcome"] == TERMINAL
    assert stage4["lifecycle_result"] == "BLOCKED"
    assert result["source_bindings"]["event_chain_changed_by_mandatory_exit"] is False


def test_closeout_preserves_zero_cores_and_scope_limitation() -> None:
    science = read(RESULT)["scientific_result"]
    assert science["summary_counts"]["candidate_cores_assessed"] == 2
    assert science["summary_counts"]["selected_minimal_cores"] == 0
    assert science["summary_counts"]["fully_physically_operational_objects"] == 0
    assert science["minimal_CCFT_core"] == "NONE"
    assert science["closed_source_bound_surrogate_core"] == "NONE"
    assert science["physical_coherence_quantity"] == "NONE"
    assert science["repository_claim_exhaustion"] == "NOT_ESTABLISHED"


def test_only_four_stages_were_attempted_and_stage_five_is_prohibited() -> None:
    result = read(RESULT)
    closeout = result["program_closeout"]
    stages = result["scientific_result"]["stage_results"]
    assert len(stages) == 4
    assert [row["terminal_result"] for row in stages] == [
        "PASSED", "PASSED", "PASSED", "BLOCKED"
    ]
    assert closeout["event_chain_event_count"] == 8
    assert closeout["repair_attempt_count"] == 0
    assert closeout["unattempted_stage_ids"] == [
        "CCFT_VIABILITY_TEST_HANDOFF_DECISION"
    ]
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


def test_registry_is_terminal_without_core_postulate_or_successor() -> None:
    registry = read(REGISTRY)
    program = registry["bounded_programs_v1"][PROGRAM_ID]
    projection = registry["current_projection_v0"]
    assert program["state"] == "CLOSED"
    assert program["blocked_stage_id"] == "MINIMAL_CLOSED_CCFT_CORE_DECISION"
    assert program["mandatory_exit_completed"] is True
    assert program["program_terminal_status"] == "CLOSED_AFTER_MANDATORY_EXIT"
    assert program["program_terminal_outcome"] == TERMINAL
    assert program["selected_minimal_core_count"] == 0
    assert program["fully_physically_operational_object_count"] == 0
    assert program["closed_source_bound_surrogate_core"] is False
    assert program["new_ccft_postulate_inserted"] is False
    assert program["future_route_selected"] == "NONE"
    assert program["proposed_successor_authorized"] is False
    assert program["proposed_successor_installed"] is False
    assert program["proposed_successor_opened"] is False
    assert projection["current_target"] == EXIT_TARGET
    assert projection["current_target_kind"].endswith("v0_terminal_closeout")
    assert projection["current_target_report"] == REVIEW.relative_to(REPO_ROOT).as_posix()
