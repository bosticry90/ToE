from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
AUTHORIZATION_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_SURROGATE_V0_BOUNDED_PROGRAM_AUTHORIZATION_20260729_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_SURROGATE_V0_BOUNDED_PROGRAM_AUTHORIZATION_RESULT_REVIEW_"
    "20260729_v0.json"
)


def build_review() -> dict:
    authorization = read_json(AUTHORIZATION_PATH)
    controls = authorization["controls"]
    stages = authorization["semantic_stages"]
    checks = {
        "five_semantic_stages": (
            controls["authorized_stage_count"] == 5 and len(stages) == 5
        ),
        "zero_repair": controls["repair_attempt_count"] == 0,
        "no_subsidiary_targets": controls[
            "no_subsidiary_scientific_targets"
        ],
        "blocked_stage_closes_v0": controls["blocked_stage_closes_v0"],
        "stage_numbers_contiguous": [
            row["stage_number"] for row in stages
        ] == [1, 2, 3, 4, 5],
        "stage_ids_unique": len(
            {row["semantic_stage_id"] for row in stages}
        ) == 5,
        "scope_hashes_present": all(
            len(row["scope_hash"]) == 64 for row in stages
        ),
        "program_unopened": (
            authorization["program_state_after_authorization"] == "UNOPENED"
        ),
        "no_scientific_stage_attempted": (
            authorization["scientific_stage_attempted"] is False
            and authorization["scientific_output_created"] is False
        ),
        "stage_1_selected_only": (
            authorization["selected_next_target"]
            == "select_toe_native_coherence_representation_v0"
        ),
    }
    failed = sorted(name for name, passed in checks.items() if not passed)
    if failed:
        raise ValueError(f"native bounded-program authorization review failed: {failed}")
    return {
        "schema_id": (
            "TOE_NATIVE_SURROGATE_V0_BOUNDED_PROGRAM_AUTHORIZATION_"
            "RESULT_REVIEW_20260729_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "reviewed_authorization": {
            "path": AUTHORIZATION_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(AUTHORIZATION_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": True,
        "program_authorized": True,
        "program_state": "UNOPENED",
        "scientific_stage_attempted": False,
        "selected_next_target": "select_toe_native_coherence_representation_v0",
        "verdict": (
            "TOE_NATIVE_SURROGATE_V0_BOUNDED_PROGRAM_AUTHORIZATION_ACCEPTED_"
            "STAGE_1_REQUIRES_SEPARATE_OPEN_COMMIT"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description="ToE native-surrogate bounded-program authorization review",
    )


if __name__ == "__main__":
    raise SystemExit(main())
