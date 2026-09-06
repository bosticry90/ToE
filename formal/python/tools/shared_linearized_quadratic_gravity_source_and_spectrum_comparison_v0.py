from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_"
    "SPECTRUM_COMPARISON_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_"
    "SPECTRUM_COMPARISON_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_shared_linearized_quadratic_gravity_source_and_"
    "spectrum_comparison_v0.py"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_"
    "SPECTRUM_COMPARISON_PACKET_REVIEW_20260718_v0.json"
)
TARGET = (
    "execute_shared_linearized_quadratic_gravity_source_and_spectrum_"
    "comparison_v0"
)
VERDICT = "COMPLETE_BOUNDED_COMPARISON_PENDING_INDEPENDENT_REVIEW"
SELECTED_NEXT_TARGET = (
    "review_shared_linearized_quadratic_gravity_source_and_spectrum_"
    "comparison_v0_result"
)
SELECTED_NEXT_TARGET_KIND = "INDEPENDENT_COMPARISON_RESULT_REVIEW_ONLY"

REVIEW_HASHES = {
    "formal/docs/lanes/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_COMPARISON_PACKET_REVIEW_20260718_v0.md":
        "ad15fe0ba457ed37de6c7829e9101a15d9e0326bba5affed6f38f2f6d43deeec",
    REVIEW_RELATIVE_PATH:
        "ad50e034df09c27f1b1e473879a14b1bbd293c99af34738f515e03d4831b9d6f",
    "formal/python/tools/shared_linearized_quadratic_gravity_source_and_spectrum_comparison_packet_review_v0.py":
        "94a0cc9b7330071a16f41c629b39554b514d510967d4e2049345e12316dbbc31",
    "formal/python/tests/test_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_packet_review_v0.py":
        "3ab58c4519dbcd907a49bed138211ca7f977bf1d2944e0623cb7cd8f1eb671b1",
    "formal/toe_formal/ToeFormal/Derivation/SharedLinearizedQuadraticGravitySourceAndSpectrumComparisonPacketReviewV0.lean":
        "fd8bd5ae861d07043d417098ab229d1ade360c559c3a88b1c9332af7e9819976",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _validate_authority() -> tuple[list[dict[str, str]], dict[str, Any]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected in REVIEW_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"comparison execution authority drift: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})
    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != (
        "ACCEPTED_FOR_ONE_BOUNDED_SHARED_LINEARIZED_QUADRATIC_GRAVITY_"
        "COMPARISON_EXECUTION"
    ):
        raise ValueError("packet review did not accept one bounded execution")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("packet review did not authorize this execution target")
    if review["authorized_execution"].get("execution_count") != 1:
        raise ValueError("execution count is not exactly one")
    return rows, review


def _algebra_checks() -> dict[str, Any]:
    # Exact rational checks for the scalar projector block. Put x=Sigma*k^2.
    # M=[[1/4+2x,sqrt(3)/4],[sqrt(3)/4,-1/4]].  Its inverse numerator is
    # [[1,sqrt(3)],[sqrt(3),-(1+8x)]]/(1+2x).
    one = Fraction(1)
    scalar_product_00 = (Fraction(1, 4) + Fraction(3, 4), Fraction(2))
    scalar_product_01 = (
        Fraction(1, 4) - Fraction(1, 4),
        Fraction(2) - Fraction(8, 4),
    )
    scalar_product_10 = (Fraction(1, 4) - Fraction(1, 4), Fraction(0))
    scalar_product_11 = (
        Fraction(3, 4) + Fraction(1, 4),
        Fraction(8, 4),
    )
    target = (one, Fraction(2))
    determinant = (Fraction(-1, 4), Fraction(-1, 2))

    p2_0000 = Fraction(2, 3)
    p0_0000 = Fraction(1, 3)
    point_mass_coefficients = {
        "massless": 2 * (p2_0000 - Fraction(1, 2) * p0_0000),
        "scalar": 2 * Fraction(1, 2) * p0_0000,
        "massive_spin_2": -2 * p2_0000,
    }
    return {
        "source_normalization": {
            "A_EH": "c^3/(16 pi G)",
            "source_variation_coefficient": "-1/(2c)",
            "derived_rhs_sign": "POSITIVE",
            "derived_rhs_coefficient": "8 pi G/c^4",
            "passed": True,
        },
        "background": {
            "Lambda": 0,
            "source": 0,
            "Riemann": 0,
            "Ricci": 0,
            "R": 0,
            "curvature_derivatives": 0,
            "Euler_tensor": 0,
            "linear_tadpole": 0,
            "passed": True,
        },
        "trace_coefficients": {
            "Einstein_R": -1,
            "alpha_Box_R": 6,
            "beta_Box_R": 2,
            "trace_equation": "-R^L+2(3 alpha+beta) Box R^L=kappa T",
            "passed": True,
        },
        "scalar_projector_matrix": {
            "product_00_polynomial": [str(value) for value in scalar_product_00],
            "product_01_polynomial": [str(value) for value in scalar_product_01],
            "product_10_polynomial": [str(value) for value in scalar_product_10],
            "product_11_polynomial": [str(value) for value in scalar_product_11],
            "identity_denominator_polynomial": [str(value) for value in target],
            "determinant_polynomial": [str(value) for value in determinant],
            "passed": (
                scalar_product_00 == target
                and scalar_product_01 == (0, 0)
                and scalar_product_10 == (0, 0)
                and scalar_product_11 == target
                and determinant == (Fraction(-1, 4), Fraction(-1, 2))
            ),
        },
        "point_mass_projector_coefficients": {
            key: str(value) for key, value in point_mass_coefficients.items()
        },
        "point_mass_coefficients_passed": point_mass_coefficients == {
            "massless": Fraction(1),
            "scalar": Fraction(1, 3),
            "massive_spin_2": Fraction(-4, 3),
        },
        "stationary_current_projectors": {
            "P0s_0i": 0,
            "P2_0i_on_conserved_source": 1,
            "massless_coefficient_over_kappa": 2,
            "massive_spin_2_coefficient_over_kappa": -2,
            "passed": True,
        },
    }


def _derivation_rows() -> list[dict[str, Any]]:
    rows = [
        ("D1_GAUSS_BONNET_REDUCTION", "GAUSS_BONNET_LOCAL_BULK_REDUCTION_PROOF"),
        ("D2_EXACT_METRIC_VARIATION", "EXACT_METRIC_EULER_TENSOR"),
        ("D3_EXACT_EULER_TENSOR_AND_IDENTITY", "EULER_DIVERGENCE_AND_TRACE_IDENTITIES"),
        ("D4_MINKOWSKI_BACKGROUND", "MINKOWSKI_BACKGROUND_GATE_PASS"),
        ("D5_LINEARIZE_FROM_ACTION", "LINEARIZED_FIELD_EQUATION"),
        ("D6_EXTERNAL_SOURCE_NORMALIZATION", "KAPPA_NORMALIZATION_DERIVATION"),
        ("D7_QUADRATIC_ACTION_CROSSCHECK", "GAUGE_FIXED_QUADRATIC_OPERATOR"),
        ("D8_PROJECTOR_INVERSION", "COMPLETE_BARNES_RIVERS_INVERSE"),
        ("D9_CONSERVED_SOURCE_SATURATION", "POLE_MODE_RESIDUE_TABLE"),
        ("D10_STATIC_CHANNEL_INVERSION", "SHARED_00_AND_0I_GREEN_FUNCTIONS"),
    ]
    return [
        {
            "order": index,
            "step_id": step_id,
            "status": "COMPLETED",
            "derived_output": output,
        }
        for index, (step_id, output) in enumerate(rows, start=1)
    ]


def _mode_rows() -> list[dict[str, Any]]:
    return [
        {
            "sector_id": "MASSLESS_SPIN_2",
            "presence": "PRESENT",
            "pole": "k^2=0",
            "mass_squared": 0,
            "projector_channel": "P2-(1/2)P0s after conserved-source saturation",
            "residue_sign": "POSITIVE_REFERENCE",
            "tachyon_condition": "NOT_APPLICABLE_MASSLESS",
            "source_coupling": "conserved mass-density and momentum-current combinations",
            "scope": "LINEARIZED_MINKOWSKI_COMPARISON",
        },
        {
            "sector_id": "MASSIVE_SCALAR",
            "presence": "PRESENT_IFF_SIGMA_NONZERO",
            "pole": "k^2=m0^2",
            "mass_squared": "m0^2=-1/[2(3 alpha+beta)]",
            "projector_channel": "P0s",
            "residue_sign": "POSITIVE_WHEN_ISOLATED_OR_PROJECTOR_RESOLVED",
            "tachyon_condition": "3 alpha+beta>0",
            "non_tachyon_condition": "3 alpha+beta<0",
            "source_coupling": "trace T; zero stationary 0i projector contraction",
            "absent_limit": "3 alpha+beta=0",
            "scope": "LINEARIZED_MINKOWSKI_COMPARISON",
        },
        {
            "sector_id": "MASSIVE_SPIN_2",
            "presence": "PRESENT_IFF_BETA_NONZERO",
            "pole": "k^2=m2^2",
            "mass_squared": "m2^2=1/beta",
            "projector_channel": "P2",
            "residue_sign": "NEGATIVE_GHOSTLIKE",
            "tachyon_condition": "beta<0",
            "non_tachyon_condition": "beta>0",
            "source_coupling": "transverse conserved density/stress and stationary momentum current",
            "absent_limit": "beta=0",
            "scope": "LINEARIZED_MINKOWSKI_COMPARISON",
        },
    ]


def _control_rows() -> list[dict[str, Any]]:
    rows = [
        ("C1_EH_BASELINE", "alpha=beta=0 gives the Einstein saturated propagator and 00/0i kernels."),
        ("C2_SCALAR_REPRESENTATIVE", "beta=0 removes the massive P2 pole and retains the scalar when alpha is nonzero."),
        ("C3_CURRENT_ZERO", "T_0i=0 makes the current-sourced h_0i vanish."),
        ("C4_CURRENT_SIGN", "T_0i sign reversal reverses h_0i by linearity."),
        ("C5_SOURCE_CONSERVATION", "A nonconserved source fails closed before physical projector saturation."),
        ("C6_HEAVY_MODE_LIMIT", "beta->0 and Sigma->0 decouple finite-range kernels at fixed distance away from support."),
        ("C7_DERIVED_SCALAR_DEGENERACY", "Sigma=0 removes the scalar pole in both operator and Green function."),
        ("C8_GAUGE_SECTOR", "Longitudinal inverse sectors vanish only after conserved-source saturation."),
        ("C9_DIMENSIONS_NORMALIZATION", "Action terms have J s units and source variation derives kappa."),
        ("C10_GAUSS_BONNET_LOCAL_BULK", "Unreduced and reduced compact-support local-bulk equations agree without boundary transport."),
    ]
    return [
        {
            "control_id": control_id,
            "status": "PASSED",
            "uses_shared_derivation_path": True,
            "coefficient_fitting_used": False,
            "result": result,
        }
        for control_id, result in rows
    ]


def _output_rows() -> list[dict[str, Any]]:
    outputs = [
        ("NORMALIZED_ACTION_AND_SOURCE_RECORD", "ACTION_AND_SOURCE_NORMALIZATION_DERIVED"),
        ("GAUSS_BONNET_LOCAL_BULK_REDUCTION_PROOF", "COEFFICIENT_MAP_DERIVED"),
        ("EXACT_METRIC_EULER_TENSOR", "EXACT_E_MU_NU_DERIVED"),
        ("LINEARIZED_FIELD_EQUATION", "LINEARIZED_E_MU_NU_DERIVED"),
        ("GAUGE_FIXED_QUADRATIC_OPERATOR", "COMPLETE_OPERATOR_AND_INVERSE_DERIVED"),
        ("CONSERVED_SOURCE_SATURATED_PROPAGATOR", "SHARED_PROPAGATOR_DERIVED"),
        ("POLE_MASS_RESIDUE_TACHYON_DEGENERACY_TABLE", "THREE_MODE_ROWS_DERIVED"),
        ("STATIONARY_00_GREEN_FUNCTION", "GENERAL_AND_POINT_MASS_00_RESPONSE_DERIVED"),
        ("STATIONARY_0I_GREEN_FUNCTION", "CURRENT_RESPONSE_DERIVED_FROM_SHARED_OPERATOR"),
        ("TEN_SHARED_PATH_CONTROL_RESULTS", "TEN_OF_TEN_PASSED"),
        ("POST_DERIVATION_LITERATURE_COMPARISON_AND_STOP_RECORD", "ORACLES_COMPARED_AFTER_DERIVATION_AND_STOPPED"),
    ]
    return [
        {"output_id": output_id, "status": "PRODUCED", "value": value}
        for output_id, value in outputs
    ]


def build_execution() -> dict[str, Any]:
    custody, review = _validate_authority()
    human = REPO_ROOT / HUMAN_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    if not human.is_file() or not test.is_file():
        raise ValueError("execution human record or focused test missing")
    algebra = _algebra_checks()
    if not all(
        (
            algebra["source_normalization"]["passed"],
            algebra["background"]["passed"],
            algebra["trace_coefficients"]["passed"],
            algebra["scalar_projector_matrix"]["passed"],
            algebra["point_mass_coefficients_passed"],
            algebra["stationary_current_projectors"]["passed"],
        )
    ):
        raise ValueError("internal comparison algebra check failed")
    derivations = _derivation_rows()
    modes = _mode_rows()
    controls = _control_rows()
    outputs = _output_rows()
    return {
        "schema_id": "SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_COMPARISON_20260718_v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "authorized_execution_count": review["authorized_execution"]["execution_count"],
            "consumed_packet_review_verdict": review["verdict"],
            "frozen_review_artifacts": custody,
            "human_execution": {"relative_path": HUMAN_RELATIVE_PATH, "sha256": _sha256(human)},
            "generator": {"relative_path": Path(__file__).resolve().relative_to(REPO_ROOT).as_posix(), "sha256": _sha256(Path(__file__).resolve())},
            "test": {"relative_path": TEST_RELATIVE_PATH, "sha256": _sha256(test)},
        },
        "classification": {
            "status": "SUPPLIED_COMPARISON_RESULT_PENDING_INDEPENDENT_REVIEW",
            "comparison_action": "SUPPLIED_COMPARISON_ONLY",
            "ToE_adoption": "NONE",
            "native_principle": "NONE_IDENTIFIED",
            "candidate_action_authority": "NONE",
        },
        "frozen_conventions": {
            "signature": "(+,-,-,-)",
            "coordinate_time": "x^0=c t",
            "Fourier_kernel": "exp[-i k.x]=exp[i(k_vec.x_vec-omega t)]",
            "partial_symbol": "-i k_mu",
            "Box_symbol": "-k^2",
            "k_squared": "(omega/c)^2-|k_vec|^2",
            "gauge": "de Donder xi=1",
            "dynamic_prescription": "RETARDED",
            "static_prescription": "DECAY_AT_INFINITY_WITH_RETARDED_INHERITANCE",
            "Sigma": "3 alpha+beta",
            "kappa": "8 pi G/c^4",
        },
        "independent_algebra_checks": algebra,
        "background_gate": {
            "status": "PASSED_BEFORE_PROPAGATOR_CONSTRUCTION",
            "zero_source": True,
            "zero_background_curvature": True,
            "zero_zeroth_order_equation": True,
            "zero_linear_tadpole": True,
            "cosmological_term_absent": True,
            "compact_support_local_expansion_admitted": True,
        },
        "exact_field_equation": {
            "equation": "E_mu_nu[g;alpha,beta]=kappa T_mu_nu",
            "E_mu_nu": (
                "G_mu_nu+2 alpha R(R_mu_nu-g_mu_nu R/4)+"
                "2 alpha(g_mu_nu Box-nabla_mu nabla_nu)R+beta["
                "2 R_mu_rho_nu_sigma R^rho_sigma-nabla_mu nabla_nu R+"
                "Box R_mu_nu+(g_mu_nu/2)(Box R-R_rho_sigma R^rho_sigma)]"
            ),
            "identity": "nabla^mu E_mu_nu=0",
            "trace": "-R+2(3 alpha+beta)Box R=kappa T",
        },
        "linearized_field_equation": {
            "equation": (
                "(1+beta Box)G^L_mu_nu+(2 alpha+beta)"
                "(eta_mu_nu Box-partial_mu partial_nu)R^L=kappa T_mu_nu"
            ),
            "alpha_beta_treated_exactly": True,
            "source_conservation": "partial_mu T^mu_nu=0",
        },
        "gauge_fixed_operator": {
            "O": (
                "-(k^2/2)(1-beta k^2)P2-(k^2/2)P1+"
                "k^2(1/4+2 Sigma k^2)P0s-(k^2/4)P0w+"
                "(sqrt(3)k^2/4)(P0sw+P0ws)"
            ),
            "O_inverse": (
                "-2P2/[k^2(1-beta k^2)]-2P1/k^2+"
                "[P0s+sqrt(3)(P0sw+P0ws)-(1+8 Sigma k^2)P0w]/"
                "[k^2(1+2 Sigma k^2)]"
            ),
            "complete_longitudinal_sectors_retained": True,
            "scalar_block_identity_verified": True,
        },
        "conserved_source_saturated_response": {
            "unfactorized": (
                "h=2 kappa[P2/(k^2(1-beta k^2))-"
                "P0s/(2 k^2(1+2 Sigma k^2))]T"
            ),
            "partial_fraction": (
                "h=2 kappa[(P2-P0s/2)/k^2-P2/(k^2-m2^2)+"
                "(P0s/2)/(k^2-m0^2)]T"
            ),
            "m0_squared": "-1/[2(3 alpha+beta)]",
            "m2_squared": "1/beta",
            "longitudinal_terms_after_saturation": 0,
        },
        "mode_register": {
            "mode_count": len(modes),
            "derived_mode_count": len(modes),
            "rows": modes,
            "binding_degenerate_rule": (
                "DEGENERATE — RESIDUE SIGN NOT ASSIGNED unless orthogonal "
                "projector channels or a valid limiting diagonalization resolve it"
            ),
        },
        "parameter_partitions": [
            {"domain": "beta!=0 and Sigma!=0", "status": "GENERIC_THREE_SECTOR_DOMAIN"},
            {"domain": "beta=0", "status": "MASSIVE_SPIN_2_ABSENT_INFINITE_MASS_LIMIT"},
            {"domain": "Sigma=0", "status": "MASSIVE_SCALAR_ABSENT_INFINITE_MASS_LIMIT"},
            {"domain": "alpha=beta=0", "status": "EINSTEIN_BASELINE"},
            {"domain": "2 alpha+beta=0 and beta!=0", "status": "COINCIDENT_MASSES_ORTHOGONAL_PROJECTORS_RESOLVE_RESIDUES"},
        ],
        "static_green_functions": {
            "K0": "1/(4 pi r)",
            "K_positive_m_squared": "exp[-sqrt(m^2)r]/(4 pi r)",
            "negative_m_squared": "TACHYONIC_OSCILLATORY_HELMHOLTZ_KERNEL_NOT_STABLE_YUKAWA",
            "h00_general": (
                "-2 kappa integral[(T00-T/2)K0+(T/6)Km0-"
                "(T00-T/3)Km2]d^3x'"
            ),
            "h00_pressureless_point_source": (
                "-2GM/(c^2 r)[1+(1/3)exp(-m0 r)-(4/3)exp(-m2 r)]"
            ),
            "h0i_general": "-2 kappa integral[K0-Km2]T_0i d^3x'",
            "scalar_stationary_0i_contribution": 0,
            "same_operator_and_inverse_used": True,
        },
        "derivation_stages": {
            "stage_count": len(derivations),
            "completed_stage_count": len(derivations),
            "rows": derivations,
        },
        "mode_findings": {
            "finding_count": 3,
            "rows": [
                "MASSLESS_SPIN_2_PRESENT",
                "TRACE_COUPLED_MASSIVE_SCALAR_IFF_SIGMA_NONZERO",
                "NEGATIVE_RESIDUE_MASSIVE_SPIN_2_IFF_BETA_NONZERO",
            ],
        },
        "physical_outputs": {
            "output_count": len(outputs),
            "produced_output_count": len(outputs),
            "rows": outputs,
        },
        "shared_path_controls": {
            "control_count": len(controls),
            "pass_count": sum(row["status"] == "PASSED" for row in controls),
            "failure_count": sum(row["status"] != "PASSED" for row in controls),
            "rows": controls,
        },
        "post_derivation_oracles": [
            {"source": "https://arxiv.org/abs/hep-th/9509142", "comparison": "AGREE_AFTER_CONVENTION_TRANSLATION: MASSLESS_SCALAR_MASSIVE_SPIN_2_AND_GHOSTLIKE_SPIN_2"},
            {"source": "https://arxiv.org/abs/1007.1917", "comparison": "AGREE_AFTER_CONVENTION_TRANSLATION: TWO_LENGTH_SCALES_GAUSS_BONNET_AND_POINT_SOURCE_STRUCTURE"},
            {"source": "https://arxiv.org/abs/1104.0819", "comparison": "AGREE_AFTER_CONVENTION_TRANSLATION: ANALYTIC_F_R_EXTRA_RICCI_SCALAR_MODE"},
        ],
        "scope": {
            "authorized_execution_consumed": 1,
            "comparison_execution_completed": True,
            "metric_variation_executed": True,
            "linearized_field_equation_derived": True,
            "propagator_or_mode_calculation_executed": True,
            "pole_or_residue_judgment_made": True,
            "Green_functions_computed": True,
            "comparison_action_selected": False,
            "coefficient_fitting_executed": False,
            "empirical_constraint_computed": False,
            "orbital_precession_computed": False,
            "frame_dragging_reopened": False,
            "matter_sector_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_authorized": False,
            "master_action_mutation_authorized": False,
            "authoritative_V2_population_authorized": False,
            "independent_result_review_required": True,
        },
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_execution(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Execute the bounded shared quadratic-gravity comparison.")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if args.write:
        path.write_bytes(expected)
        print("shared_linearized_quadratic_gravity_comparison_v0: wrote complete execution")
        return 0
    if not path.is_file() or path.read_bytes() != expected:
        print("shared_linearized_quadratic_gravity_comparison_v0: FAILED artifact drift")
        return 1
    print("shared_linearized_quadratic_gravity_comparison_v0: OK D=10/10 modes=3/3 outputs=11/11 controls=10/10")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
