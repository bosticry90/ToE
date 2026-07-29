from __future__ import annotations

from formal.python.tools.bounded_program_governance import (
    NATIVE_PROGRAM_ID,
    PROGRAMS_KEY,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
EXECUTION_TARGET = "close_toe_native_surrogate_v0_after_bounded_result_v0"
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
RESULT_PATH = REPO_ROOT / (
    "formal/output/CALC-TOE-NATIVE-COHERENCE-REPRESENTATION-v0.json"
)
REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_COHERENCE_REPRESENTATION_V0_RESULT_REVIEW_20260729_v0.json"
)
OPEN_EVENT_PATH = REPO_ROOT / (
    "formal/docs/release/bounded_program_events/"
    "TOE_NATIVE_SURROGATE_V0_ATTEMPT_01_OPEN_v0.json"
)
CLOSE_EVENT_PATH = REPO_ROOT / (
    "formal/docs/release/bounded_program_events/"
    "TOE_NATIVE_SURROGATE_V0_ATTEMPT_01_CLOSE_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/CALC-TOE-NATIVE-SURROGATE-V0-BOUNDED-CLOSEOUT-v0.json"
)


def build_calculation() -> dict:
    registry = read_json(REGISTRY_PATH)
    projection = registry["current_projection_v0"]
    program = registry[PROGRAMS_KEY][NATIVE_PROGRAM_ID]
    result = read_json(RESULT_PATH)
    review = read_json(REVIEW_PATH)
    open_event = read_json(OPEN_EVENT_PATH)
    close_event = read_json(CLOSE_EVENT_PATH)
    if projection["current_target"] != EXECUTION_TARGET:
        raise QuadraticHyperbolicityError(
            "native-surrogate mandatory closeout is not authoritative"
        )
    if not (
        program["state"] == "CLOSED"
        and program["last_closed_attempt_number"] == 1
        and program["attempted_stage_ids"] == ["COHERENCE_REPRESENTATION"]
        and program["blocked_stage_id"] == "COHERENCE_REPRESENTATION"
        and program["repair_attempt_count"] == 0
        and program["stage_2_authorized"] is False
    ):
        raise QuadraticHyperbolicityError("native-surrogate program is not closed")
    if not (
        open_event["event_type"] == "ATTEMPT_OPEN"
        and close_event["event_type"] == "ATTEMPT_CLOSE"
        and close_event["open_event_hash"] == open_event["event_hash"]
        and close_event["terminal_result"] == "BLOCKED"
    ):
        raise QuadraticHyperbolicityError("native attempt event chain is invalid")
    if not (
        result["terminal_outcome"] == "BLOCKED_CCFT_TO_CONTINUUM_MAP_UNRESOLVED"
        and review["accepted"] is True
        and review["program_v0_closes"] is True
        and review["stage_2_authorized"] is False
    ):
        raise QuadraticHyperbolicityError("accepted Stage 1 boundary changed")

    return {
        "schema_id": "CALC_TOE_NATIVE_SURROGATE_V0_BOUNDED_CLOSEOUT_v0",
        "calculation_id": (
            "CALC-TOE-NATIVE-SURROGATE-V0-BOUNDED-CLOSEOUT-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": EXECUTION_TARGET,
        "program_id": NATIVE_PROGRAM_ID,
        "program_closeout": {
            "authorized_stage_count": 5,
            "attempted_stage_count": 1,
            "attempted_stage_ids": program["attempted_stage_ids"],
            "blocked_stage_id": program["blocked_stage_id"],
            "repair_attempt_count": program["repair_attempt_count"],
            "unattempted_stage_ids": [
                "MINIMAL_ACTION_SELECTION",
                "INTERNAL_VIABILITY",
                "SEAM_AUDIT",
                "OBSERVABLE_AND_UNIQUENESS",
            ],
            "subsidiary_scientific_targets_created": 0,
        },
        "event_chain": {
            "open_event_path": OPEN_EVENT_PATH.relative_to(REPO_ROOT).as_posix(),
            "open_event_sha256": sha256_path(OPEN_EVENT_PATH),
            "open_event_hash": open_event["event_hash"],
            "close_event_path": CLOSE_EVENT_PATH.relative_to(REPO_ROOT).as_posix(),
            "close_event_sha256": sha256_path(CLOSE_EVENT_PATH),
            "close_event_hash": close_event["event_hash"],
        },
        "accepted_blocked_result": {
            "path": RESULT_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(RESULT_PATH),
            "review_path": REVIEW_PATH.relative_to(REPO_ROOT).as_posix(),
            "review_sha256": sha256_path(REVIEW_PATH),
            "terminal_outcome": (
                "BLOCKED_CCFT_TO_CONTINUUM_MAP_UNRESOLVED"
            ),
        },
        "terminal_boundaries": {
            "program_v0_closed": True,
            "repair_authorized": False,
            "stage_2_through_5_authorized": False,
            "portal_action_selected": False,
            "classical_native_sandbox_constructed": False,
            "ccft_rejected": False,
            "ccft_validated": False,
            "new_representation_or_action_requires_separate_v1": True,
        },
        "terminal_outcome": "NO_UNIQUE_TOE_DISCRIMINATOR_V0",
        "verdict": (
            "TOE_NATIVE_SURROGATE_V0_CLOSED_AFTER_STAGE_1_BLOCK_NO_REPAIR_"
            "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description="ToE native-surrogate v0 bounded closeout",
    )


if __name__ == "__main__":
    raise SystemExit(main())
