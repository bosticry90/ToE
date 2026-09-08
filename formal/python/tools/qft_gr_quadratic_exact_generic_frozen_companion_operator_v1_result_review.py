from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
CALCULATION_PATH = REPO_ROOT / (
    "formal/output/CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-"
    "COMPANION-OPERATOR-v1.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/QFT_GR_QUADRATIC_EXACT_GENERIC_FROZEN_"
    "COMPANION_OPERATOR_V1_RESULT_REVIEW_20260729_v0.json"
)
MANDATORY_EXIT_TARGET = (
    "select_qft_gr_quadratic_toe_role_after_generic_frozen_result_v0"
)


def build_review() -> dict:
    result = read_json(CALCULATION_PATH)
    audit = result["generic_companion_closure_audit"]
    charts = audit["tracefree_chart_closure"]["charts"]
    checks = {
        "bounded_stage_3_authority_consumed": (
            result["bounded_authority"]["semantic_stage_id"]
            == "EXACT_FROZEN_COMPANION_OPERATOR"
            and result["bounded_authority"]["attempt_sequence_number"] == 3
        ),
        "Minkowski_control_reproduced": (
            result["Minkowski_regression"]["matrix_shape"] == [128, 128]
            and result["Minkowski_regression"]["nonzero_entry_count"] == 224
        ),
        "metric_wave_slot_ambiguity_demonstrated": (
            audit["metric_wave_slot_audit"]["uses_dk_as_second_derivative_proxy"]
            and not audit["metric_wave_slot_audit"][
                "contains_independent_dh_or_d2h_slots"
            ]
        ),
        "scalar_wave_slot_ambiguity_demonstrated": (
            audit["scalar_wave_slot_audit"]["uses_du_as_second_derivative_proxy"]
            and not audit["scalar_wave_slot_audit"][
                "contains_independent_dq_or_d2q_slots"
            ]
        ),
        "all_trace_charts_retain_dependent_jets": (
            len(charts) == 10
            and all(
                row["dependent_tangent_leaves_retained"]
                and not row["closed_in_its_nine_independent_spin_variables"]
                for row in charts
            )
        ),
        "no_early_constraint_projection": (
            result["prohibitions_respected"]["constraint_surface_imposed_early"]
            is False
        ),
        "no_repair_or_subsidiary_target": (
            result["prohibitions_respected"]["repair_target_created"] is False
            and result["prohibitions_respected"][
                "subsidiary_scientific_target_created"
            ]
            is False
        ),
        "later_claims_remain_false": (
            result["claim_boundary"][
                "exact_generic_frozen_companion_operator_derived"
            ]
            is False
            and result["claim_boundary"]["generic_finite_loss_established"]
            is False
            and result["claim_boundary"]["local_well_posedness_established"]
            is False
        ),
        "mandatory_exit_selected": (
            result["mandatory_exit_target"] == MANDATORY_EXIT_TARGET
        ),
    }
    failed = sorted(name for name, passed in checks.items() if not passed)
    if failed:
        raise QuadraticHyperbolicityError(
            f"Stage 3 failed-closed review checks failed: {failed}"
        )
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_EXACT_GENERIC_FROZEN_COMPANION_"
            "OPERATOR_V1_RESULT_REVIEW_20260729_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "reviewed_result": {
            "path": CALCULATION_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(CALCULATION_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": True,
        "accepted_as": (
            "VALID_FAILED_CLOSED_STAGE_3_RESULT_WITHOUT_GENERIC_OPERATOR"
        ),
        "terminal_result": "BLOCKED",
        "terminal_outcome": "GENERIC_BACKGROUND_OPERATOR_NOT_CLOSED",
        "toe_role_not_decided_here": True,
        "scientific_interpretation": (
            "The accepted component expansion does not determine a unique "
            "generic off-constraint 128-state companion. Treating dk and du as "
            "metric/scalar second derivatives imposes definition constraints "
            "before the authorized tangent-space stage; treating c and r as "
            "independent requires absent dh/d2h and dq/d2q jet slots. Every "
            "trace chart also retains its dependent spin component or derivative."
        ),
        "mandatory_exit_target": MANDATORY_EXIT_TARGET,
        "authority_rotation": {
            "quadratic_stage_4_authorized": False,
            "quadratic_stage_5_authorized": False,
            "quadratic_repair_authorized": False,
            "quadratic_role_gate_mandatory": True,
        },
        "verdict": (
            "STAGE_3_BLOCKED_RESULT_ACCEPTED_NO_EXACT_GENERIC_COMPANION_"
            "NO_REPAIR_OR_LATER_QUADRATIC_STAGE_MANDATORY_ROLE_GATE"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "quadratic-gravity exact generic frozen companion v1 result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
