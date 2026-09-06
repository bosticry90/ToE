from __future__ import annotations

from formal.python.tools.bounded_program_governance import (
    NATIVE_MANDATORY_EXIT,
    NATIVE_PROGRAM_AUTHORIZATION_TARGET,
    NATIVE_PROGRAM_ID,
    NATIVE_STAGE_DEFINITIONS,
    PROGRAMS_KEY,
    REGISTRY_PATH,
    SET_LIKE_ARRAY_FIELDS,
    authorize_native_program,
    scope_hash,
    strict_json_loads,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
STAGE_1_TARGET = "select_toe_native_coherence_representation_v0"
MANDATORY_CLOSE_TARGET = "close_toe_native_surrogate_v0_after_bounded_result_v0"
NATIVE_HYPOTHESIS_SELECTOR_TARGET = (
    "select_next_native_toe_hypothesis_for_bounded_adjudication_v0"
)
NATIVE_COHERENCE_PROGRAM_PREPARATION_TARGET = (
    "prepare_toe_native_coherence_ontology_and_representation_"
    "bounded_program_v0"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_SURROGATE_V0_BOUNDED_PROGRAM_AUTHORIZATION_20260729_v0.json"
)


def _stage_scope(stage: dict) -> dict:
    return {
        key: stage[key]
        for key in (
            "semantic_stage_id",
            "normalized_scientific_question",
            *SET_LIKE_ARRAY_FIELDS,
        )
    }


def build_authorization() -> dict:
    registry = strict_json_loads(REGISTRY_PATH.read_text(encoding="utf-8"))
    projection = registry["current_projection_v0"]
    if projection["current_target"] not in {
        NATIVE_PROGRAM_AUTHORIZATION_TARGET,
        STAGE_1_TARGET,
        MANDATORY_CLOSE_TARGET,
        NATIVE_HYPOTHESIS_SELECTOR_TARGET,
        NATIVE_COHERENCE_PROGRAM_PREPARATION_TARGET,
    }:
        raise ValueError("native bounded-program authorization is not current")
    programs = registry[PROGRAMS_KEY]
    if NATIVE_PROGRAM_ID in programs:
        native = programs[NATIVE_PROGRAM_ID]
    else:
        native = authorize_native_program(registry)[PROGRAMS_KEY][NATIVE_PROGRAM_ID]
    stages = [
        {
            "stage_number": index,
            "semantic_stage_id": stage["semantic_stage_id"],
            "target": stage["target"],
            "scope_hash": scope_hash(_stage_scope(stage)),
            "terminal_outcome_vocabulary": stage[
                "terminal_outcome_vocabulary"
            ],
        }
        for index, stage in enumerate(NATIVE_STAGE_DEFINITIONS, start=1)
    ]
    if [row["semantic_stage_id"] for row in native["stage_definitions"]] != [
        row["semantic_stage_id"] for row in NATIVE_STAGE_DEFINITIONS
    ]:
        raise ValueError("authorized native stage definitions changed")
    return {
        "schema_id": (
            "TOE_NATIVE_SURROGATE_V0_BOUNDED_PROGRAM_AUTHORIZATION_20260729_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "authorization_target": NATIVE_PROGRAM_AUTHORIZATION_TARGET,
        "program_id": NATIVE_PROGRAM_ID,
        "controls": {
            "authorized_stage_count": 5,
            "repair_attempt_count": 0,
            "no_subsidiary_scientific_targets": True,
            "mandatory_exit_target": NATIVE_MANDATORY_EXIT,
            "attempts_count_when_opened": True,
            "blocked_stage_closes_v0": True,
            "new_representation_or_action_requires_v1": True,
        },
        "claim_boundary": native["claim_boundary"],
        "semantic_stages": stages,
        "program_state_after_authorization": "UNOPENED",
        "scientific_stage_attempted": False,
        "scientific_output_created": False,
        "selected_next_target": STAGE_1_TARGET,
        "verdict": (
            "TOE_NATIVE_SURROGATE_V0_AUTHORIZED_AS_FIVE_ATTEMPT_ZERO_REPAIR_"
            "PROGRAM_STAGE_1_NOT_OPENED_OR_EXECUTED"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_authorization,
        description="ToE native-surrogate bounded-program authorization",
    )


if __name__ == "__main__":
    raise SystemExit(main())
