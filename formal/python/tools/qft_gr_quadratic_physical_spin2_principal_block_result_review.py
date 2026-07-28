from __future__ import annotations

import sympy as sp

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    read_json,
    sha256_path,
    write_or_check,
)


CALCULATION_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-PHYSICAL-SPIN2-PRINCIPAL-BLOCK-v0.json"
)
SOURCE_PACKET_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_HYPERBOLICITY_ADMISSIBLE_SOURCE_AND_"
    "FROZEN_THEORY_PACKET_20260728_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_PHYSICAL_SPIN2_PRINCIPAL_BLOCK_"
    "RESULT_REVIEW_20260728_v0.json"
)
EXPECTED_CURRENT_TARGET = (
    "review_qft_gr_quadratic_physical_spin2_principal_block_v0_result"
)
EXPECTED_NEXT_TARGET = (
    "prepare_qft_gr_quadratic_auxiliary_harmonic_adapted_norm_"
    "well_posedness_packet_v0"
)


def _independent_symbolic_result() -> dict:
    lam = sp.Symbol("lambda", real=True)
    beta = sp.Symbol("beta", real=True, nonzero=True)
    pencil = -beta * (lam**2 - 1) ** 2 * sp.eye(2)
    determinant = sp.factor(pencil.det())
    roots = sp.roots(determinant, lam)
    multiplicities = {
        int(root): {
            "algebraic": int(multiplicity),
            "geometric": 2 - int(pencil.subs(lam, root).rank()),
        }
        for root, multiplicity in roots.items()
    }
    einstein = (lam**2 - 1) * sp.eye(2)
    einstein_roots = sp.roots(sp.factor(einstein.det()), lam)
    return {
        "matrix": [
            [sp.sstr(pencil[row, column]) for column in range(2)]
            for row in range(2)
        ],
        "determinant": sp.sstr(determinant),
        "multiplicities": multiplicities,
        "einstein_multiplicities": {
            int(root): {
                "algebraic": int(multiplicity),
                "geometric": 2 - int(einstein.subs(lam, root).rank()),
            }
            for root, multiplicity in einstein_roots.items()
        },
    }


def build_review() -> dict:
    calculation = read_json(CALCULATION_PATH)
    source_packet = read_json(SOURCE_PACKET_PATH)
    independent = _independent_symbolic_result()
    observed_roots = {
        row["lambda"]: {
            "algebraic": row["algebraic_multiplicity"],
            "geometric": row["geometric_multiplicity"],
        }
        for row in calculation["physical_pencil"]["roots"]
    }
    controls = calculation["coefficient_controls"]
    conclusions = calculation["conclusions"]
    checks = {
        "calculation_target_is_exact": (
            calculation["execution_target"]
            == "derive_qft_gr_quadratic_physical_spin2_principal_block_v0"
            and calculation["selected_next_target"] == EXPECTED_CURRENT_TARGET
        ),
        "frozen_vacuum_dependency_is_bound": (
            calculation["theory_and_domain"]["source"] == "VACUUM"
            and len(calculation["consumed_source_review"]["sha256"]) == 64
        ),
        "metric_equation_contains_all_fourth_order_terms": (
            calculation["metric_equations"]["fourth_order_derivative_terms"]
            == (
                "2 alpha (g_mn Box - nabla_m nabla_n)R "
                "+ beta(Box R_mn + (1/2)g_mn Box R "
                "- nabla_m nabla_n R)"
            )
        ),
        "tt_projection_removes_R2_spin2_principal_term": (
            calculation["physical_tt_projection"][
                "linearized_scalar_curvature_principal"
            ]
            == "delta R = 0"
            and calculation["physical_tt_projection"][
                "alpha_R2_spin2_principal_contribution"
            ]
            == "0"
        ),
        "physical_pencil_is_independently_reproduced": (
            calculation["physical_pencil"]["matrix"] == independent["matrix"]
            and calculation["physical_pencil"]["determinant"]
            == independent["determinant"]
        ),
        "light_cone_multiplicities_are_defective": (
            observed_roots == independent["multiplicities"]
            == {
                -1: {"algebraic": 4, "geometric": 2},
                1: {"algebraic": 4, "geometric": 2},
            }
        ),
        "physical_quotient_invariance_boundary_is_explicit": (
            calculation["physical_block_invariance"][
                "physical_block_alterable_within_boundary"
            ]
            is False
            and "changing the physical equations"
            in calculation["physical_block_invariance"]["assumption_boundary"]
        ),
        "coefficient_controls_change_the_expected_ranks": (
            controls["beta_eq_0"]["generic_result_applies"] is False
            and controls["3alpha_plus_beta_eq_0"][
                "spin2_obstruction_remains"
            ]
            is True
            and independent["einstein_multiplicities"]
            == {
                -1: {"algebraic": 2, "geometric": 2},
                1: {"algebraic": 2, "geometric": 2},
            }
            and controls["c_R_eq_0"][
                "spin2_obstruction_remains_when_beta_nonzero"
            ]
            is True
        ),
        "generic_strong_and_symmetric_hyperbolicity_are_refuted": (
            conclusions["real_characteristics"] is True
            and conclusions["complete_eigenbasis"] is False
            and conclusions["strong_hyperbolicity"] is False
            and conclusions["symmetric_hyperbolicity"] is False
            and conclusions["terminal_outcome"]
            == "GENERIC_STRONG_HYPERBOLICITY_REFUTED"
        ),
        "adapted_norm_and_existence_claims_remain_open": (
            calculation["claim_boundary"][
                "adapted_norm_local_well_posedness_established"
            ]
            is False
            and calculation["claim_boundary"]["smooth_existence_refuted"]
            is False
            and calculation["claim_boundary"][
                "historical_harmonic_auxiliary_results_refuted"
            ]
            is False
        ),
        "historical_comparator_boundary_is_retained": any(
            source["source_id"] == "ARXIV_1811_07869_V4"
            and "identified there as a conjecture" in source["claim_boundary"]
            for source in source_packet["admissible_primary_sources"]
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    accepted = not failed
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_PHYSICAL_SPIN2_PRINCIPAL_BLOCK_"
            "RESULT_REVIEW_20260728_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": EXPECTED_CURRENT_TARGET,
        "reviewed_calculation": {
            "path": CALCULATION_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(CALCULATION_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": accepted,
        "reviewer_independence": {
            "imports_calculation_module": False,
            "rebuilds_symbolic_pencil": True,
            "recomputes_quadratic_and_einstein_multiplicities": True,
            "rechecks_claim_boundaries": True,
        },
        "accepted_results": (
            [
                "GENERIC_STRONG_HYPERBOLICITY_REFUTED",
                "PHYSICAL_SPIN2_REPEATED_ROOT_DEFECT_IDENTIFIED",
            ]
            if accepted
            else []
        ),
        "not_established": [
            "ADAPTED_NORM_LOCAL_WELL_POSEDNESS_ESTABLISHED",
            "SMOOTH_EXISTENCE_WITHOUT_HADAMARD_WELL_POSEDNESS",
            "GENERIC_LOCAL_WELL_POSEDNESS_BLOCKED",
            "SOURCE_EXTENSION_CHANGES_PRINCIPAL_STRUCTURE",
        ],
        "reconciliation": {
            "ordinary_same_order_metric_derivative_estimate": (
                "UNAVAILABLE_IN_GENERIC_SPIN2_SECTOR"
                if accepted
                else "UNRESOLVED"
            ),
            "older_smooth_existence_results": "NOT_REFUTED",
            "continuous_dependence_in_required_sobolev_norm": "NOT_ESTABLISHED",
            "adapted_derivative_loss_estimate": "REQUIRES_FRESH_PHASE_B_C_PACKET",
        },
        "authority_rotation": {
            "phase_a_result_accepted": accepted,
            "phase_b_c_packet_preparation_authorized": accepted,
            "phase_b_c_execution_authorized": False,
            "source_extension_authorized": False,
            "preserved_descendant_adoption_authorized": False,
            "yukawa_work_authorized": False,
        },
        "selected_next_target": (
            EXPECTED_NEXT_TARGET
            if accepted
            else "repair_qft_gr_quadratic_physical_spin2_principal_block_v0"
        ),
        "verdict": (
            "ACCEPT_GENERIC_WEAK_HYPERBOLICITY_OBSTRUCTION_"
            "PREPARE_ADAPTED_NORM_PACKET"
            if accepted
            else "B_BLOCKED_PHASE_A_RESULT_REQUIRES_CORRECTION"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "quadratic-gravity physical spin-2 principal-block result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
