from __future__ import annotations

import sympy as sp

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


SOURCE_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_HYPERBOLICITY_ADMISSIBLE_SOURCE_AND_"
    "FROZEN_THEORY_PACKET_RESULT_REVIEW_20260728_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-PHYSICAL-SPIN2-PRINCIPAL-BLOCK-v0.json"
)
CURRENT_TARGET = "derive_qft_gr_quadratic_physical_spin2_principal_block_v0"
RESULT_REVIEW_TARGET = (
    "review_qft_gr_quadratic_physical_spin2_principal_block_v0_result"
)


def analyze_pencil(
    *,
    repeated_wave_power: int = 2,
    polarization_count: int = 2,
    beta_nonzero: bool = True,
) -> dict:
    if repeated_wave_power < 1:
        raise ValueError("repeated_wave_power must be positive")
    if polarization_count < 1:
        raise ValueError("polarization_count must be positive")
    lam = sp.Symbol("lambda", real=True)
    beta = sp.Symbol("beta", real=True, nonzero=True)
    if not beta_nonzero:
        return {
            "block_present": False,
            "reason": "beta=0 removes the fourth-order physical spin-2 block",
        }
    scalar = -beta * (lam**2 - 1) ** repeated_wave_power
    pencil = scalar * sp.eye(polarization_count)
    determinant = sp.factor(pencil.det())
    root_map = sp.roots(determinant, lam)
    roots = []
    for root in sorted(root_map, key=lambda value: float(value)):
        algebraic = int(root_map[root])
        geometric = polarization_count - int(pencil.subs(lam, root).rank())
        roots.append(
            {
                "lambda": int(root),
                "algebraic_multiplicity": algebraic,
                "geometric_multiplicity": geometric,
                "complete_at_root": algebraic == geometric,
            }
        )
    complete = all(row["complete_at_root"] for row in roots)
    return {
        "block_present": True,
        "polarization_count": polarization_count,
        "repeated_wave_power": repeated_wave_power,
        "matrix": [
            [sp.sstr(pencil[row, column]) for column in range(polarization_count)]
            for row in range(polarization_count)
        ],
        "scalar_factor": sp.sstr(sp.factor(scalar)),
        "determinant": sp.sstr(determinant),
        "roots": roots,
        "all_characteristic_roots_real": all(
            bool(root.is_real) for root in root_map
        ),
        "complete_eigenbasis": complete,
        "strongly_hyperbolic_physical_block": complete,
        "symmetrically_hyperbolic_physical_block": complete,
    }


def build_calculation() -> dict:
    source_review = read_json(SOURCE_REVIEW_PATH)
    if source_review["accepted"] is not True:
        raise QuadraticHyperbolicityError("frozen-theory review was not accepted")
    if source_review["selected_next_target"] != CURRENT_TARGET:
        raise QuadraticHyperbolicityError("Phase A authority mismatch")
    pencil = analyze_pencil()
    if pencil["strongly_hyperbolic_physical_block"]:
        raise QuadraticHyperbolicityError("expected defective repeated-root block")
    return {
        "schema_id": "CALC_QFT_GR_QUADRATIC_PHYSICAL_SPIN2_PRINCIPAL_BLOCK_v0",
        "calculation_id": (
            "CALC-QFT-GR-QUADRATIC-PHYSICAL-SPIN2-PRINCIPAL-BLOCK-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": CURRENT_TARGET,
        "consumed_source_review": {
            "path": SOURCE_REVIEW_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(SOURCE_REVIEW_PATH),
        },
        "theory_and_domain": {
            "action_density": (
                "sqrt(-g) [c_R R + c_Lambda + alpha R^2 "
                "+ beta R_mn R^mn]"
            ),
            "source": "VACUUM",
            "G_principal": ["beta != 0", "3 alpha + beta != 0"],
            "G_Stelle": [
                "beta != 0",
                "3 alpha + beta != 0",
                "c_R != 0",
            ],
            "spin2_obstruction_minimal_domain": ["beta != 0"],
        },
        "metric_equations": {
            "equation": (
                "c_R G_mn - (1/2)c_Lambda g_mn "
                "+ alpha[2 R R_mn - (1/2)g_mn R^2 "
                "+ 2(g_mn Box - nabla_m nabla_n)R] "
                "+ beta[2 R_mrns R^rs - (1/2)g_mn R_rs R^rs "
                "+ Box R_mn + (1/2)g_mn Box R "
                "- nabla_m nabla_n R] = 0"
            ),
            "fourth_order_derivative_terms": (
                "2 alpha (g_mn Box - nabla_m nabla_n)R "
                "+ beta(Box R_mn + (1/2)g_mn Box R "
                "- nabla_m nabla_n R)"
            ),
            "curvature_convention_bound_in_source_packet": True,
        },
        "physical_tt_projection": {
            "polarizations": 2,
            "conditions": [
                "trace(h)=0",
                "ell^m h_mn=0",
                "h_mn is represented in the physical gauge quotient",
            ],
            "linearized_scalar_curvature_principal": "delta R = 0",
            "linearized_ricci_principal": "delta R_mn = -(1/2) Box h_mn",
            "alpha_R2_spin2_principal_contribution": "0",
            "beta_Ricci2_spin2_principal_contribution": (
                "-(beta/2) Box^2 h_mn"
            ),
            "normalization": (
                "Multiply the physical equation by 2; a nonzero scalar "
                "multiple does not change roots or multiplicities."
            ),
        },
        "principal_covector": {
            "definition": (
                "ell_mu = lambda n_mu + k_mu, "
                "n.n=-1, k.k=1, n.k=0"
            ),
            "box_symbol": "1-lambda^2",
            "spatial_covector_scope": (
                "arbitrary nonzero k, normalized to k.k=1 by homogeneity"
            ),
        },
        "physical_pencil": pencil,
        "multiplicity_criterion": {
            "algebraic": (
                "order of the root in det(P_phys(lambda))"
            ),
            "geometric": "dimension of ker(P_phys(lambda_root))",
            "strong_hyperbolicity_requirement": (
                "Each real characteristic root must have a complete "
                "physical eigenspace with a uniformly bounded diagonalizer."
            ),
            "failure": (
                "At each light-cone root, algebraic multiplicity 4 exceeds "
                "geometric multiplicity 2."
            ),
        },
        "physical_block_invariance": {
            "quotient": (
                "principal constraint kernel modulo principal gauge image"
            ),
            "gauge_fixing": (
                "Gauge-sector additions factor through gauge generators and "
                "vanish after projection to the physical TT quotient."
            ),
            "constraint_additions": (
                "Additions proportional to the principal constraints vanish "
                "on the principal constraint kernel and therefore induce the "
                "same physical quotient map."
            ),
            "assumption_boundary": (
                "The additions must be genuine gauge fixing or constraint "
                "addition; changing the physical equations, adding regulator "
                "fields, or order reducing is excluded."
            ),
            "physical_block_alterable_within_boundary": False,
        },
        "coefficient_controls": {
            "beta_eq_0": {
                "effect": "removes fourth-order physical spin-2 block",
                "generic_result_applies": False,
            },
            "3alpha_plus_beta_eq_0": {
                "effect": (
                    "removes or degenerates scalar quadratic mode; physical "
                    "spin-2 block is unchanged when beta != 0"
                ),
                "spin2_obstruction_remains": True,
            },
            "alpha_eq_beta_eq_0": {
                "effect": "returns Einstein second-order principal structure",
                "control_pencil": "(lambda^2-1) I_2",
                "light_cone_algebraic_multiplicity": 2,
                "light_cone_geometric_multiplicity": 2,
            },
            "c_R_eq_0": {
                "effect": (
                    "pure-quadratic rather than Einstein-connected sector; "
                    "fourth-order physical spin-2 principal block unchanged"
                ),
                "spin2_obstruction_remains_when_beta_nonzero": True,
            },
            "c_Lambda": {
                "effect": "lower order; no fourth-order principal effect"
            },
        },
        "conclusions": {
            "real_characteristics": True,
            "complete_eigenbasis": False,
            "strong_hyperbolicity": False,
            "symmetric_hyperbolicity": False,
            "obstruction": "PHYSICAL_SPIN2_REPEATED_ROOT_DEFECT",
            "terminal_outcome": "GENERIC_STRONG_HYPERBOLICITY_REFUTED",
        },
        "claim_boundary": {
            "adapted_norm_local_well_posedness_established": False,
            "smooth_existence_refuted": False,
            "historical_harmonic_auxiliary_results_refuted": False,
            "source_extension_executed": False,
            "phase_b_or_c_executed": False,
            "interpretation": (
                "The same-order metric-derivative strong-hyperbolicity "
                "estimate is unavailable in the generic spin-2 sector. "
                "A distinct auxiliary-variable or derivative-loss theorem "
                "remains a separate question."
            ),
        },
        "selected_next_target": RESULT_REVIEW_TARGET,
        "verdict": (
            "PHASE_A_GENERIC_PHYSICAL_SPIN2_WEAK_HYPERBOLICITY_"
            "OBSTRUCTION_REPRODUCED"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description="quadratic-gravity physical spin-2 principal-block calculation",
    )


if __name__ == "__main__":
    raise SystemExit(main())
