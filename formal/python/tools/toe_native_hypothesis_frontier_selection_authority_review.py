from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
AUTHORITY_PATH = REPO_ROOT / (
    "formal/docs/release/TOE_NATIVE_HYPOTHESIS_FRONTIER_SELECTION_"
    "AUTHORITY_PACKET_20260729_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/TOE_NATIVE_HYPOTHESIS_FRONTIER_SELECTION_"
    "AUTHORITY_PACKET_RESULT_REVIEW_20260729_v0.json"
)


def build_review() -> dict:
    authority = read_json(AUTHORITY_PATH)
    selector = authority["selector_contract"]
    closed = authority["closed_predecessors"]
    checks = {
        "exactly_one_decision": selector["decision_count"] == 1,
        "zero_repair": selector["repair_attempt_count"] == 0,
        "four_candidate_paths": len(selector["candidate_paths"]) == 4,
        "required_decision_outputs_present": len(selector["required_outputs"]) == 5,
        "quadratic_program_remains_closed_control": (
            closed["quadratic"]["state"] == "CLOSED"
            and closed["quadratic"]["toe_role"] == "REFERENCE_CONTROL_ONLY"
            and closed["quadratic"]["control_result"]
            == "UNRESOLVED_AFTER_BOUNDED_ATTEMPT"
        ),
        "native_surrogate_remains_closed_at_stage_one": (
            closed["native_surrogate"]["state"] == "CLOSED"
            and closed["native_surrogate"]["blocked_stage_id"]
            == "COHERENCE_REPRESENTATION"
            and closed["native_surrogate"]["stage_2_authorized"] is False
        ),
        "no_program_installation": (
            authority["program_installation_authorized_here"] is False
        ),
        "no_scientific_calculation": (
            authority["scientific_calculation_authorized_here"] is False
        ),
        "selector_only": (
            authority["selected_next_target"]
            == "select_next_native_toe_hypothesis_for_bounded_adjudication_v0"
        ),
    }
    failed = sorted(name for name, passed in checks.items() if not passed)
    if failed:
        raise ValueError(
            f"native-hypothesis frontier authority review failed: {failed}"
        )
    return {
        "schema_id": (
            "TOE_NATIVE_HYPOTHESIS_FRONTIER_SELECTION_AUTHORITY_PACKET_"
            "RESULT_REVIEW_20260729_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "reviewed_authority": {
            "path": AUTHORITY_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(AUTHORITY_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": True,
        "closed_programs_reopened": False,
        "new_program_installed": False,
        "selected_next_target": (
            "select_next_native_toe_hypothesis_for_bounded_adjudication_v0"
        ),
        "verdict": (
            "NATIVE_HYPOTHESIS_FRONTIER_SELECTOR_AUTHORITY_ACCEPTED_"
            "ONE_DECISION_ONLY_NO_PROGRAM_INSTALLATION_OR_PHYSICS_EXECUTION"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description="native-hypothesis frontier selection authority review",
    )


if __name__ == "__main__":
    raise SystemExit(main())
