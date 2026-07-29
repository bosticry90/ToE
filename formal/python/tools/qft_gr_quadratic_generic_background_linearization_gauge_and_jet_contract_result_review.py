from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    canonical_json_bytes,
    read_json,
    sha256_bytes,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
CALCULATION_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-GENERIC-BACKGROUND-LINEARIZATION-"
    "GAUGE-AND-JET-CONTRACT-v0.json"
)
MINKOWSKI_CONTROL_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-COMPANION-"
    "OPERATOR-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_GENERIC_BACKGROUND_LINEARIZATION_GAUGE_AND_"
    "JET_CONTRACT_RESULT_REVIEW_20260729_v0.json"
)
EXPECTED_REVIEW_TARGET = (
    "review_qft_gr_quadratic_generic_background_linearization_"
    "gauge_and_jet_contract_v0_result"
)
EXPECTED_NEXT_TARGET = (
    "derive_qft_gr_quadratic_component_expanded_generic_background_"
    "linearization_v1"
)
SYMMETRIC_COMPONENTS = {
    "00",
    "01",
    "02",
    "03",
    "11",
    "12",
    "13",
    "22",
    "23",
    "33",
}


def _atlas_checks(calculation: dict) -> bool:
    atlas = calculation["tracefree_atlas"]
    charts = atlas["charts"]
    pivots = {row["pivot_component"] for row in charts}
    independent_ok = all(
        set(row["independent_components"])
        == SYMMETRIC_COMPONENTS - {row["pivot_component"]}
        and len(row["independent_components"]) == 9
        for row in charts
    )
    return (
        len(charts) == 10
        and pivots == SYMMETRIC_COMPONENTS
        and independent_ok
        and atlas["linearized_trace_identity"]
        == "gbar^mn*s_mn=Sbar^rs*h_rs"
    )


def _rewrite_checks(calculation: dict) -> bool:
    rewrite = calculation["rewrite_contract"]
    rules = rewrite["rules"]
    heads = [row["lhs_head"] for row in rules]
    ranks = {row["lhs_head"]: row["measure_rank"] for row in rules}
    decreasing = all(
        dependency not in ranks or ranks[dependency] < row["measure_rank"]
        for row in rules
        for dependency in row["rhs_heads"]
    )
    return (
        len(heads) == len(set(heads))
        and decreasing
        and rewrite["termination_established"] is True
        and rewrite["critical_pairs_closed"] is True
        and rewrite["normal_form_unique"] is True
        and rewrite["normalization_idempotent"] is True
    )


def _minkowski_checks(calculation: dict) -> bool:
    regression = calculation["minkowski_regression"]
    control = read_json(MINKOWSKI_CONTROL_PATH)["exact_minkowski_control"]
    recomputed = sha256_bytes(canonical_json_bytes(control["sparse_entries"]))
    return (
        regression["zero_curvature_trace_rule"]
        == "s_33=s_00-s_11-s_22"
        and regression["matrix_shape"] == [128, 128]
        and regression["nonzero_entry_count"] == 224
        and regression["sparse_entry_sha256"] == recomputed
        and control["sparse_entry_sha256"] == recomputed
    )


def build_review() -> dict:
    calculation = read_json(CALCULATION_PATH)
    gauge = calculation["strict_harmonic_gauge_contract"]
    regularity = calculation["regularity_contract"]
    domain = calculation["regular_background_domain"]
    background = calculation["background_classes"]
    claims = calculation["claim_boundary"]
    checks = {
        "bounded_open_event_consumed": (
            calculation["bounded_authority"]["attempt_sequence_number"] == 1
            and calculation["bounded_authority"]["semantic_stage_id"]
            == "STRICT_HARMONIC_GAUGE_JET_CONTRACT"
            and len(calculation["bounded_authority"]["open_event_hash"]) == 64
        ),
        "strict_harmonic_zero_jet_contract_is_exact": (
            gauge["H_mu"] == "0"
            and gauge["delta_H_mu"] == "0"
            and gauge["gauge_source_jet_orders_zero"] == [0, 1, 2, 3]
            and gauge["constraint_additions"] == "ZERO"
            and gauge["gauge_universality_claimed"] is False
        ),
        "ten_chart_tracefree_atlas_is_complete": _atlas_checks(calculation),
        "regular_stratum_is_local_and_conditioned": (
            domain["uniformity_statement"]
            == "locally uniform on compact subsets of the regular stratum"
            and "|q_p| >= trace_epsilon > 0"
            in domain["compact_uniform_subset"]
            and "trace-chart boundary q_p=0" in domain["excluded_controls"]
        ),
        "reduced_and_metric_regularity_are_separate": (
            all(
                row["required_class"] == "C3"
                for row in regularity["reduced_variable_regularity"]
            )
            and regularity["combined_sufficient_metric_class"] == "C6"
            and regularity["combined_sufficient_metric_perturbation_class"]
            == "C6"
            and regularity["optimality_claimed"] is False
        ),
        "finite_jet_order_is_explicit": (
            regularity["identity_verification_jets"][
                "background_reduced_jet_order"
            ]
            == 3
            and regularity["identity_verification_jets"][
                "perturbation_reduced_jet_order"
            ]
            == 3
            and all(
                row["background_jet_in_evolution"] == 2
                and row["perturbation_jet_in_evolution"] == 2
                for row in regularity["reduced_variable_regularity"]
            )
        ),
        "rewrite_termination_and_confluence_are_structural": _rewrite_checks(
            calculation
        ),
        "accepted_64_equations_remain_input_not_stage_1_conclusion": (
            background["accepted_equation_count_input"] == 64
            and background["stage_2_independent_inventory_verification_required"]
            is True
        ),
        "Minkowski_control_is_exact": _minkowski_checks(calculation),
        "claim_ceiling_is_respected": (
            claims["strict_harmonic_contract_frozen"] is True
            and claims["component_expanded_linearization_derived"] is False
            and claims["exact_generic_companion_operator_derived"] is False
            and claims["constraint_tangent_projector_constructed"] is False
            and claims["generic_finite_loss_established"] is False
            and claims["local_well_posedness_established"] is False
            and claims["quadratic_gravity_native_toe_status_claimed"] is False
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    accepted = not failed
    calculation_bytes = CALCULATION_PATH.read_bytes()
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_GENERIC_BACKGROUND_LINEARIZATION_GAUGE_AND_"
            "JET_CONTRACT_RESULT_REVIEW_20260729_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": EXPECTED_REVIEW_TARGET,
        "reviewed_calculation": {
            "path": CALCULATION_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(CALCULATION_PATH),
            "canonical_sha256_recomputed": sha256_bytes(
                canonical_json_bytes(calculation)
            ),
            "canonical_bytes_match": (
                calculation_bytes == canonical_json_bytes(calculation)
            ),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": accepted,
        "reviewer_independence": {
            "imports_calculation_module": False,
            "recomputes_atlas_inventory": True,
            "recomputes_rewrite_dependency_order": True,
            "recomputes_Minkowski_sparse_hash": True,
            "audits_regularity_boundary": True,
            "audits_claim_ceiling": True,
        },
        "accepted_results": (
            ["STRICT_HARMONIC_GAUGE_AND_JET_CONTRACT_COMPLETE"]
            if accepted
            else []
        ),
        "not_established": [
            "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_COMPLETE",
            "EXACT_GENERIC_FROZEN_COMPANION_OPERATOR",
            "CONSTRAINT_TANGENT_PROJECTOR",
            "GENERIC_FINITE_SOBOLEV_LOSS",
            "VARIABLE_COEFFICIENT_LINEAR_ESTIMATE",
            "QUASILINEAR_OR_LOCAL_WELL_POSEDNESS",
        ],
        "authority_rotation": {
            "stage_1_result_accepted": accepted,
            "stage_2_component_expansion_authorized": accepted,
            "stage_3_companion_operator_authorized": False,
            "stage_4_constraint_quotient_authorized": False,
            "stage_5_propagator_growth_authorized": False,
            "subsidiary_scientific_target_authorized": False,
        },
        "selected_next_target": (
            EXPECTED_NEXT_TARGET
            if accepted
            else "select_qft_gr_quadratic_toe_role_after_generic_frozen_result_v0"
        ),
        "terminal_result": "PASSED" if accepted else "BLOCKED",
        "verdict": (
            "ACCEPT_STRICT_HARMONIC_GAUGE_AND_JET_CONTRACT_AUTHORIZE_"
            "BOUNDED_STAGE_2_ONLY"
            if accepted
            else "BLOCK_STRICT_HARMONIC_GAUGE_AND_JET_CONTRACT_EXIT_TO_ROLE_GATE"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "quadratic-gravity strict-harmonic gauge-and-jet contract review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
