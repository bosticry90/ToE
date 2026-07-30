from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-30T00:00:00Z"
RESULT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-TOE-NATIVE-COHERENCE-ONTOLOGY-AND-REPRESENTATION-V0-"
    "BOUNDED-CLOSEOUT-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0_"
    "BOUNDED_CLOSEOUT_REVIEW_20260730_v0.json"
)
UNATTEMPTED_STAGES = [
    "COHERENCE_REPRESENTATION_COMPARISON",
    "COHERENCE_OPERATIONAL_REPRESENTABILITY_DECISION",
    "MINIMAL_NATIVE_FIELD_HANDOFF",
]


def build_review() -> dict:
    result = read_json(RESULT_PATH)
    program = result["program_closeout"]
    boundary = result["terminal_boundaries"]
    science = result["scientific_results"]
    checks = {
        "ccft_neither_validated_nor_rejected": (
            boundary["ccft_validated"] is False
            and boundary["ccft_rejected"] is False
        ),
        "event_chain_has_two_matched_open_close_attempts": (
            len(result["event_chain"]) == 4
            and [event["event_type"] for event in result["event_chain"]]
            == [
                "ATTEMPT_OPEN",
                "ATTEMPT_CLOSE",
                "ATTEMPT_OPEN",
                "ATTEMPT_CLOSE",
            ]
        ),
        "mandatory_exit_completed": program["mandatory_exit_completed"],
        "no_action_model_or_calculation_constructed": (
            science["calculation_status"] == "NOT_REACHED"
            and science["native_model_status"] == "NOT_CONSTRUCTED"
        ),
        "no_representation_selected": (
            science["representation_status"] == "NOT_REACHED"
        ),
        "program_closed": boundary["program_closed"],
        "separate_new_program_and_substantive_input_required": boundary[
            "future_coherence_route_requires_new_program_and_new_substantive_input"
        ],
        "stage_1_inventory_preserved": (
            science["stage_1_inventory"]["claim_count"] == 13
            and science["stage_1_inventory"]["conflict_class_count"] == 6
        ),
        "stage_2_block_preserved": (
            science["operational_result"]
            == "COHERENCE_CLAIM_INSUFFICIENTLY_OPERATIONAL"
            and science["program_result"]
            == "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED"
        ),
        "stages_3_through_5_unattempted": (
            program["unattempted_stage_ids"] == UNATTEMPTED_STAGES
            and boundary["stages_3_through_5_attempted"] is False
        ),
        "two_attempts_consumed": program["attempted_stage_count"] == 2,
        "zero_repair": program["repair_attempt_count"] == 0,
    }
    failed = sorted(name for name, passed in checks.items() if not passed)
    if failed:
        raise QuadraticHyperbolicityError(
            f"coherence bounded closeout review failed: {failed}"
        )
    return {
        "accepted": True,
        "artifact_id": (
            "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0_"
            "BOUNDED_CLOSEOUT_REVIEW_20260730_v0"
        ),
        "automatic_successor_selected": False,
        "captured_at_utc": CAPTURED_AT_UTC,
        "checks": checks,
        "failed_checks": failed,
        "program_terminal": True,
        "reviewed_result": {
            "path": RESULT_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(RESULT_PATH),
        },
        "schema_id": (
            "toe.native_coherence_ontology_and_representation."
            "bounded_closeout_review.v0"
        ),
        "scientific_success_claimed": False,
        "terminal_scientific_status": {
            "calculation_status": "NOT_REACHED",
            "native_model_status": "NOT_CONSTRUCTED",
            "operational_result": (
                "COHERENCE_CLAIM_INSUFFICIENTLY_OPERATIONAL"
            ),
            "program_result": (
                "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED"
            ),
            "representation_status": "NOT_REACHED",
        },
        "verdict": (
            "ACCEPT_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0_TERMINAL_"
            "CLOSEOUT_NO_REPAIR_NO_AUTOMATIC_SUCCESSOR"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "ToE native coherence ontology and representation v0 "
            "bounded closeout review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
