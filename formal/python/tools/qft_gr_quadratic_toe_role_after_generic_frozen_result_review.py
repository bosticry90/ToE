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
    "formal/output/CALC-QFT-GR-QUADRATIC-TOE-ROLE-AFTER-"
    "GENERIC-FROZEN-RESULT-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/QFT_GR_QUADRATIC_TOE_ROLE_AFTER_GENERIC_"
    "FROZEN_RESULT_REVIEW_20260729_v0.json"
)


def build_review() -> dict:
    result = read_json(RESULT_PATH)
    role = result["role_decision"]
    boundary = result["claim_boundary"]
    checks = {
        "historical_comparison_role_reproduced": all(
            result["historical_role_evidence"]["checks"].values()
        ),
        "toe_role_is_reference_control_only": (
            role["toe_role"] == "REFERENCE_CONTROL_ONLY"
        ),
        "mathematical_result_is_independent": (
            role["control_result"] == "UNRESOLVED_AFTER_BOUNDED_ATTEMPT"
        ),
        "three_attempts_consumed_without_repair": (
            result["bounded_program_closeout"]["attempted_stage_count"] == 3
            and result["bounded_program_closeout"]["repair_attempt_count"] == 0
        ),
        "stages_4_and_5_unattempted": (
            result["bounded_program_closeout"]["unattempted_stage_ids"]
            == [
                "CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT",
                "SUBPRINCIPAL_PROPAGATOR_GROWTH",
            ]
        ),
        "no_native_or_effective_adoption": (
            boundary["quadratic_gravity_native_toe_sector"] is False
            and boundary["quadratic_gravity_derived_effective_limit"] is False
        ),
        "unresolved_not_recast_as_refutation": (
            boundary["generic_finite_loss_established"] is False
            and boundary["generic_finite_loss_refuted"] is False
            and boundary["generic_frozen_status_unresolved"] is True
        ),
        "no_further_quadratic_work": (
            boundary["further_quadratic_work_authorized"] is False
        ),
        "native_program_requires_separate_authority": (
            boundary["native_surrogate_program_authorized_here"] is False
            and result["selected_next_target"]
            == "authorize_toe_native_surrogate_v0_bounded_program"
        ),
    }
    failed = sorted(name for name, passed in checks.items() if not passed)
    if failed:
        raise QuadraticHyperbolicityError(f"quadratic role review failed: {failed}")
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_TOE_ROLE_AFTER_GENERIC_FROZEN_"
            "RESULT_REVIEW_20260729_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "reviewed_result": {
            "path": RESULT_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(RESULT_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": True,
        "toe_role": "REFERENCE_CONTROL_ONLY",
        "control_result": "UNRESOLVED_AFTER_BOUNDED_ATTEMPT",
        "quadratic_program_terminal": True,
        "selected_next_target": (
            "authorize_toe_native_surrogate_v0_bounded_program"
        ),
        "authority_rotation": {
            "further_quadratic_science_authorized": False,
            "native_program_installed": False,
            "native_program_authorization_target_selected": True,
        },
        "verdict": (
            "REFERENCE_CONTROL_ONLY_ACCEPTED_WITH_UNRESOLVED_BOUNDED_"
            "MATHEMATICAL_RESULT_QUADRATIC_PROGRAM_CLOSED_NATIVE_PROGRAM_"
            "REQUIRES_SEPARATE_AUTHORITY"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description="quadratic-gravity ToE role gate review",
    )


if __name__ == "__main__":
    raise SystemExit(main())
