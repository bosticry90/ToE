from __future__ import annotations

from formal.python.tools.bounded_program_governance import (
    COHERENCE_ONTOLOGY_PROGRAM_ID,
    PROGRAMS_KEY,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-30T00:00:00Z"
EXECUTION_TARGET = (
    "close_toe_native_coherence_ontology_and_representation_v0_"
    "after_bounded_result_v0"
)
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
STAGE_2_RESULT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_COHERENCE_OPERATIONAL_DEFINITION_RESULT_20260729_v0.json"
)
STAGE_2_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_COHERENCE_OPERATIONAL_DEFINITION_RESULT_REVIEW_20260729_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-TOE-NATIVE-COHERENCE-ONTOLOGY-AND-REPRESENTATION-V0-"
    "BOUNDED-CLOSEOUT-v0.json"
)

ATTEMPT_EVENT_PATHS = (
    REPO_ROOT
    / "formal/docs/release/bounded_program_events/"
    "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0_ATTEMPT_01_OPEN_v0.json",
    REPO_ROOT
    / "formal/docs/release/bounded_program_events/"
    "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0_ATTEMPT_01_CLOSE_v0.json",
    REPO_ROOT
    / "formal/docs/release/bounded_program_events/"
    "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0_ATTEMPT_02_OPEN_v0.json",
    REPO_ROOT
    / "formal/docs/release/bounded_program_events/"
    "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0_ATTEMPT_02_CLOSE_v0.json",
)
ATTEMPT_STAGES = (
    "CONTROLLED_COHERENCE_CLAIM_INVENTORY",
    "CONTROLLED_COHERENCE_CLAIM_INVENTORY",
    "COHERENCE_OPERATIONAL_DEFINITION_TEST",
    "COHERENCE_OPERATIONAL_DEFINITION_TEST",
)
UNATTEMPTED_STAGES = [
    "COHERENCE_REPRESENTATION_COMPARISON",
    "COHERENCE_OPERATIONAL_REPRESENTABILITY_DECISION",
    "MINIMAL_NATIVE_FIELD_HANDOFF",
]


def _event_chain() -> list[dict]:
    events = [read_json(path) for path in ATTEMPT_EVENT_PATHS]
    expected_types = (
        "ATTEMPT_OPEN",
        "ATTEMPT_CLOSE",
        "ATTEMPT_OPEN",
        "ATTEMPT_CLOSE",
    )
    if [event["event_type"] for event in events] != list(expected_types):
        raise QuadraticHyperbolicityError("coherence event types are invalid")
    if not (
        events[1]["open_event_hash"] == events[0]["event_hash"]
        and events[3]["open_event_hash"] == events[2]["event_hash"]
        and events[1]["terminal_result"] == "PASSED"
        and events[3]["terminal_result"] == "BLOCKED"
    ):
        raise QuadraticHyperbolicityError("coherence event linkage is invalid")
    return [
        {
            "event_hash": event["event_hash"],
            "event_type": event["event_type"],
            "path": path.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(path),
            "stage": stage,
        }
        for path, event, stage in zip(
            ATTEMPT_EVENT_PATHS, events, ATTEMPT_STAGES, strict=True
        )
    ]


def build_calculation() -> dict:
    registry = read_json(REGISTRY_PATH)
    projection = registry["current_projection_v0"]
    program = registry[PROGRAMS_KEY][COHERENCE_ONTOLOGY_PROGRAM_ID]
    stage_2_result = read_json(STAGE_2_RESULT_PATH)
    stage_2_review = read_json(STAGE_2_REVIEW_PATH)

    if projection["current_target"] != EXECUTION_TARGET:
        raise QuadraticHyperbolicityError(
            "coherence mandatory closeout is not authoritative"
        )
    if not (
        program["state"] == "CLOSED"
        and program["authorized_stage_count"] == 5
        and program["last_closed_attempt_number"] == 2
        and program["attempted_stage_ids"]
        == [
            "CONTROLLED_COHERENCE_CLAIM_INVENTORY",
            "COHERENCE_OPERATIONAL_DEFINITION_TEST",
        ]
        and program["blocked_stage_id"]
        == "COHERENCE_OPERATIONAL_DEFINITION_TEST"
        and program["repair_attempt_count"] == 0
        and program["mandatory_exit_completed"] is True
        and program["stage_3_opened"] is False
        and program["stage_4_opened"] is False
        and program["stage_5_opened"] is False
    ):
        raise QuadraticHyperbolicityError(
            "coherence ontology program is not terminal"
        )
    if not (
        stage_2_result["terminal_outcome"]
        == "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED"
        and stage_2_result["claim_status_after_test"]
        == "COHERENCE_CLAIM_INSUFFICIENTLY_OPERATIONAL"
        and stage_2_review["accepted"] is True
        and stage_2_review["close_recommendation"]["mandatory_exit_target"]
        == EXECUTION_TARGET
        and stage_2_review["close_recommendation"][
            "stage_3_open_permitted"
        ]
        is False
    ):
        raise QuadraticHyperbolicityError(
            "accepted Stage 2 blocked boundary changed"
        )

    return {
        "automatic_successor_selected": False,
        "calculation_id": (
            "CALC-TOE-NATIVE-COHERENCE-ONTOLOGY-AND-REPRESENTATION-V0-"
            "BOUNDED-CLOSEOUT-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "event_chain": _event_chain(),
        "execution_target": EXECUTION_TARGET,
        "program_closeout": {
            "attempted_stage_count": 2,
            "attempted_stage_ids": program["attempted_stage_ids"],
            "authorized_stage_count": 5,
            "blocked_stage_id": program["blocked_stage_id"],
            "mandatory_exit_completed": True,
            "repair_attempt_count": 0,
            "subsidiary_scientific_targets_created": 0,
            "unattempted_stage_ids": UNATTEMPTED_STAGES,
        },
        "program_id": COHERENCE_ONTOLOGY_PROGRAM_ID,
        "scientific_results": {
            "calculation_status": "NOT_REACHED",
            "native_model_status": "NOT_CONSTRUCTED",
            "operational_result": "COHERENCE_CLAIM_INSUFFICIENTLY_OPERATIONAL",
            "program_result": (
                "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED"
            ),
            "representation_status": "NOT_REACHED",
            "stage_1_inventory": {
                "claim_count": 13,
                "conflict_class_count": 6,
                "selected_claim_id": "COH-CLAIM-001",
                "status": "CLAIM_INVENTORY_COMPLETE_WITH_CONFLICTS",
            },
            "stage_2_operational_test": {
                "failed_definition_criterion_count": 9,
                "review_path": STAGE_2_REVIEW_PATH.relative_to(
                    REPO_ROOT
                ).as_posix(),
                "review_sha256": sha256_path(STAGE_2_REVIEW_PATH),
                "result_path": STAGE_2_RESULT_PATH.relative_to(
                    REPO_ROOT
                ).as_posix(),
                "result_sha256": sha256_path(STAGE_2_RESULT_PATH),
                "terminal_outcome": (
                    "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED"
                ),
            },
        },
        "schema_id": (
            "CALC_TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0_"
            "BOUNDED_CLOSEOUT_v0"
        ),
        "terminal_boundaries": {
            "ccft_rejected": False,
            "ccft_validated": False,
            "coherence_impossible_claimed": False,
            "future_coherence_route_requires_new_program_and_new_substantive_input": (
                True
            ),
            "master_action_modified": False,
            "new_representation_or_action_authorized": False,
            "program_closed": True,
            "repair_authorized": False,
            "stages_3_through_5_attempted": False,
        },
        "terminal_outcome": (
            "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED"
        ),
        "verdict": (
            "COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0_CLOSED_AFTER_STAGE_2_"
            "BLOCK_NO_REPAIR_NO_REPRESENTATION_OR_CALCULATION"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description=(
            "ToE native coherence ontology and representation v0 "
            "bounded closeout"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
