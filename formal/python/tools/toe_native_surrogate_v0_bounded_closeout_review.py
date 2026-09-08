from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
RESULT_PATH = REPO_ROOT / (
    "formal/output/CALC-TOE-NATIVE-SURROGATE-V0-BOUNDED-CLOSEOUT-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_SURROGATE_V0_BOUNDED_CLOSEOUT_REVIEW_20260729_v0.json"
)


def build_review() -> dict:
    result = read_json(RESULT_PATH)
    program = result["program_closeout"]
    boundary = result["terminal_boundaries"]
    checks = {
        "one_attempt_consumed": (
            program["attempted_stage_count"] == 1
            and program["attempted_stage_ids"] == ["COHERENCE_REPRESENTATION"]
        ),
        "zero_repair": program["repair_attempt_count"] == 0,
        "four_stages_unattempted": program["unattempted_stage_ids"] == [
            "MINIMAL_ACTION_SELECTION",
            "INTERNAL_VIABILITY",
            "SEAM_AUDIT",
            "OBSERVABLE_AND_UNIQUENESS",
        ],
        "event_chain_closed": all(
            len(result["event_chain"][key]) == 64
            for key in ("open_event_hash", "close_event_hash")
        ),
        "program_v0_closed": boundary["program_v0_closed"],
        "no_action_or_sandbox_constructed": (
            boundary["portal_action_selected"] is False
            and boundary["classical_native_sandbox_constructed"] is False
        ),
        "ccft_neither_validated_nor_rejected": (
            boundary["ccft_validated"] is False
            and boundary["ccft_rejected"] is False
        ),
        "separate_v1_required": (
            boundary["new_representation_or_action_requires_separate_v1"]
        ),
        "no_unique_discriminator": (
            result["terminal_outcome"] == "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
        ),
    }
    failed = sorted(name for name, passed in checks.items() if not passed)
    if failed:
        raise QuadraticHyperbolicityError(
            f"native-surrogate v0 closeout review failed: {failed}"
        )
    return {
        "schema_id": (
            "TOE_NATIVE_SURROGATE_V0_BOUNDED_CLOSEOUT_REVIEW_20260729_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "reviewed_result": {
            "path": RESULT_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(RESULT_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": True,
        "program_terminal": True,
        "terminal_outcome": "NO_UNIQUE_TOE_DISCRIMINATOR_V0",
        "scientific_success_claimed": False,
        "next_scientific_target_selected": False,
        "verdict": (
            "ACCEPT_NATIVE_SURROGATE_V0_TERMINAL_CLOSEOUT_NO_UNIQUE_TOE_"
            "DISCRIMINATOR_AND_NO_AUTOMATIC_V1"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description="ToE native-surrogate v0 bounded closeout review",
    )


if __name__ == "__main__":
    raise SystemExit(main())
