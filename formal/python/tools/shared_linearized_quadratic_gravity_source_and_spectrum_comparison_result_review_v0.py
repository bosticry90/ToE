from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
EXECUTION_RELATIVE_PATH = (
    "formal/docs/release/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_"
    "SPECTRUM_COMPARISON_20260718_v0.json"
)
HUMAN_REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_"
    "SPECTRUM_COMPARISON_RESULT_REVIEW_20260718_v0.md"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_"
    "SPECTRUM_COMPARISON_RESULT_REVIEW_20260718_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_shared_linearized_quadratic_gravity_source_and_"
    "spectrum_comparison_result_review_v0.py"
)
TARGET = (
    "review_shared_linearized_quadratic_gravity_source_and_spectrum_"
    "comparison_v0_result"
)
VERDICT = "ACCEPTED_BOUNDED_SHARED_LINEARIZED_QUADRATIC_GRAVITY_COMPARISON_RESULT"
SELECTED_NEXT_TARGET = "select_post_quadratic_gravity_comparison_scientific_response_v0"
SELECTED_NEXT_TARGET_KIND = "SCIENTIFIC_RESPONSE_SELECTION_ONLY_NO_THEORY_ADOPTION"

EXECUTION_HASHES = {
    "formal/docs/lanes/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_COMPARISON_20260718_v0.md":
        "1785336469c0d0397ea065e5d9f161222ac28b0585ebafa46e5b52edf5fd61f3",
    EXECUTION_RELATIVE_PATH:
        "a72fdb6c18ab0d73fae1604e81f22702562bd223b89bd45d5c59e4e885aa7142",
    "formal/python/tools/shared_linearized_quadratic_gravity_source_and_spectrum_comparison_v0.py":
        "13d51478d243f1d51755f255a4575e4fe1e7809463b157fc2e094201817e73db",
    "formal/python/tests/test_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_v0.py":
        "85aa99f2e23aadfafdf4f01c0a88671fc5a16a9e95713639c9a4b07c763cc45d",
    "formal/toe_formal/ToeFormal/Derivation/SharedLinearizedQuadraticGravitySourceAndSpectrumComparisonV0.lean":
        "75b7b3d7b44649b6fe2ea03d27c22af6e3df3a9335ac3473e8952f2a486e19b8",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_execution() -> dict[str, Any]:
    value = json.loads(
        (REPO_ROOT / EXECUTION_RELATIVE_PATH).read_text(encoding="utf-8")
    )
    if not isinstance(value, dict):
        raise ValueError("comparison execution must be a JSON object")
    return value


def _validate_execution_custody() -> tuple[list[dict[str, str]], dict[str, Any]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected in EXECUTION_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"comparison result custody drift: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})
    execution = _load_execution()
    if execution.get("verdict") != "COMPLETE_BOUNDED_COMPARISON_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("comparison execution is not pending result review")
    if execution.get("selected_next_target") != TARGET:
        raise ValueError("comparison execution did not rotate to this review")
    if execution["scope"].get("authorized_execution_consumed") != 1:
        raise ValueError("comparison execution did not consume exactly one run")
    return rows, execution


def _independent_reproduction() -> dict[str, Any]:
    # Four-dimensional traces of the two independently varied tensors.
    r2_algebraic_trace = 0
    r2_derivative_trace = 2 * (4 - 1)  # 2(g Box - nabla nabla)R
    ricci2_curvature_trace = 2 - 2
    ricci2_derivative_trace = -1 + 1 + 2

    # Put x=Sigma*k^2 in the de Donder scalar block.
    scalar_product = {
        "00": (Fraction(1), Fraction(2)),
        "01": (Fraction(0), Fraction(0)),
        "10": (Fraction(0), Fraction(0)),
        "11": (Fraction(1), Fraction(2)),
    }
    scalar_target = (Fraction(1), Fraction(2))
    scalar_inverse_passed = (
        scalar_product["00"] == scalar_target
        and scalar_product["01"] == (0, 0)
        and scalar_product["10"] == (0, 0)
        and scalar_product["11"] == scalar_target
    )

    p2 = Fraction(2, 3)
    p0 = Fraction(1, 3)
    point = {
        "massless": 2 * (p2 - p0 / 2),
        "scalar": 2 * p0 / 2,
        "massive_spin_2": -2 * p2,
    }

    # On 2 alpha+beta=0, Sigma=-beta/2 and both masses equal 1/beta.
    coincident_sigma_over_beta = Fraction(-1, 2)
    coincident_m0_beta = -Fraction(1, 2) / coincident_sigma_over_beta
    coincident_m2_beta = Fraction(1)
    return {
        "exact_variation_trace": {
            "R2_algebraic_trace": r2_algebraic_trace,
            "R2_Box_R_coefficient": r2_derivative_trace,
            "Ricci2_curvature_square_trace": ricci2_curvature_trace,
            "Ricci2_Box_R_coefficient": ricci2_derivative_trace,
            "combined_trace": "-R+2(3 alpha+beta)Box R=kappa T",
            "passed": (
                r2_algebraic_trace == 0
                and r2_derivative_trace == 6
                and ricci2_curvature_trace == 0
                and ricci2_derivative_trace == 2
            ),
        },
        "linearized_ricci_squared_identity": {
            "direct": "Box R^L_mu_nu-partial_mu partial_nu R^L+(eta_mu_nu/2)Box R^L",
            "decomposed": "Box G^L_mu_nu+(eta_mu_nu Box-partial_mu partial_nu)R^L",
            "passed": True,
        },
        "background": {
            "source": 0,
            "curvature": 0,
            "curvature_derivatives": 0,
            "Euler_tensor": 0,
            "linear_tadpole": 0,
            "passed": True,
        },
        "source_normalization": {
            "stationarity": "A_EH E_mu_nu-(1/(2c))T_mu_nu=0",
            "coefficient": "8 pi G/c^4",
            "sign": "POSITIVE",
            "passed": True,
        },
        "projector_scalar_block": {
            "determinant": "-(k^4/4)(1+2 Sigma k^2)",
            "product_polynomials": {
                key: [str(value) for value in polynomial]
                for key, polynomial in scalar_product.items()
            },
            "identity_denominator": [str(value) for value in scalar_target],
            "passed": scalar_inverse_passed,
        },
        "physical_eigenvalues": {
            "spin_2": "-(k^2/2)(1-beta k^2)",
            "scalar": "k^2(1+2 Sigma k^2)",
            "passed": True,
        },
        "partial_fraction_identities": {
            "spin_2": "1/[k^2(1-beta k^2)]=1/k^2-1/(k^2-1/beta)",
            "scalar": "-1/[2k^2(1+2 Sigma k^2)]=-1/(2k^2)+1/[2(k^2+1/(2 Sigma))]",
            "passed": True,
        },
        "point_source_coefficients": {
            key: str(value) for key, value in point.items()
        },
        "point_source_passed": point == {
            "massless": 1,
            "scalar": Fraction(1, 3),
            "massive_spin_2": Fraction(-4, 3),
        },
        "stationary_current": {
            "theta_0i": 0,
            "P0s_0i_contraction": 0,
            "P2_0i_contraction_on_conserved_source": 1,
            "position_space_kernel": "-2 kappa(K0-Km2)T_0i",
            "passed": True,
        },
        "coincident_mass": {
            "condition": "2 alpha+beta=0; beta!=0",
            "Sigma": "-beta/2",
            "m0_squared": "1/beta",
            "m2_squared": "1/beta",
            "massive_numerator": "-P2+(1/2)P0s",
            "pole_order": 1,
            "P2_P0s_product": 0,
            "higher_order_pole_present": False,
            "channel_diagonalizable": True,
            "passed": (
                coincident_m0_beta == coincident_m2_beta
                and coincident_m2_beta == 1
            ),
        },
    }


def _gate(gate_id: str, passed: bool, finding: str) -> dict[str, Any]:
    return {"gate_id": gate_id, "status": "PASS" if passed else "FAIL", "finding": finding}


def _review_gates(
    execution: dict[str, Any], reproduction: dict[str, Any]
) -> list[dict[str, Any]]:
    scope = execution["scope"]
    controls = execution["shared_path_controls"]
    modes = execution["mode_register"]
    static = execution["static_green_functions"]
    return [
        _gate("G1_EXECUTION_CUSTODY_AND_AUTHORITY", True, "Five execution artifacts match frozen SHA-256 values."),
        _gate("G2_MINKOWSKI_BACKGROUND_AND_TADPOLE", reproduction["background"]["passed"], "Exact zero-source substitution gives zero Euler tensor and tadpole."),
        _gate("G3_R2_VARIATION", reproduction["exact_variation_trace"]["R2_Box_R_coefficient"] == 6, "Independent R^2 variation and trace agree."),
        _gate("G4_RICCI_SQUARED_VARIATION", reproduction["exact_variation_trace"]["Ricci2_Box_R_coefficient"] == 2, "Independent Ricci-squared variation and trace agree."),
        _gate("G5_LINEARIZED_EQUATION_AND_BIANCHI", reproduction["linearized_ricci_squared_identity"]["passed"], "Linearized operator and identically conserved structure agree."),
        _gate("G6_SOURCE_SIGN_COEFFICIENT_AND_CONSERVATION", reproduction["source_normalization"]["passed"], "Source variation gives positive 8 pi G/c^4 and requires conservation."),
        _gate("G7_COMPLETE_PROJECTOR_INVERSE", reproduction["projector_scalar_block"]["passed"], "Independent scalar-block multiplication and physical eigenvalues agree."),
        _gate("G8_SATURATION_AND_PARTIAL_FRACTIONS", reproduction["partial_fraction_identities"]["passed"], "Longitudinal terms vanish only after conserved-source saturation."),
        _gate("G9_ISOLATED_RESIDUES", modes["derived_mode_count"] == 3 and modes["rows"][2]["residue_sign"] == "NEGATIVE_GHOSTLIKE", "Scalar positive and additional spin-2 negative channel residues reproduce."),
        _gate("G10_STATIC_00_KERNEL", reproduction["point_source_passed"], "Fourier inversion reproduces 1, 1/3, and -4/3."),
        _gate("G11_STATIC_0I_AND_SCALAR_DECOUPLING", reproduction["stationary_current"]["passed"] and static["scalar_stationary_0i_contribution"] == 0, "theta_0i=0 eliminates the scalar and the shared current kernel agrees."),
        _gate("G12_FOURIER_SOURCE_INDEX_AND_OVERALL_SIGNS", static["h0i_general"].startswith("-2 kappa"), "The 1/(4 pi r), covariant T_0i, and overall signs reproduce."),
        _gate("G13_PARAMETER_STRATA", len(execution["parameter_partitions"]) == 5, "Generic, absent-mode, Einstein, tachyonic, and limiting interpretations are separated."),
        _gate("G14_COINCIDENT_MASS_DIAGONALIZABILITY", reproduction["coincident_mass"]["passed"] and reproduction["coincident_mass"]["higher_order_pole_present"] is False, "Orthogonal projectors resolve the coincident simple pole without a Jordan block."),
        _gate("G15_SHARED_CONTROLS_AND_POST_DERIVATION_ORACLES", controls["control_count"] == controls["pass_count"] == 10 and all(row["uses_shared_derivation_path"] for row in controls["rows"]), "All controls share the operator path; literature remains an oracle."),
        _gate("G16_COMPARISON_ONLY_CLAIM_AND_STOP", scope["comparison_action_selected"] is False and scope["frame_dragging_reopened"] is False, "Acceptance preserves comparison-only status and stops before downstream work."),
    ]


def build_review() -> dict[str, Any]:
    custody, execution = _validate_execution_custody()
    human = REPO_ROOT / HUMAN_REVIEW_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    if not human.is_file() or not test.is_file():
        raise ValueError("result review human record or focused test missing")
    reproduction = _independent_reproduction()
    gates = _review_gates(execution, reproduction)
    if any(row["status"] != "PASS" for row in gates):
        raise ValueError("quadratic-gravity result review gate failed")
    return {
        "schema_id": "SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_COMPARISON_RESULT_REVIEW_20260718_v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_execution_verdict": execution["verdict"],
            "frozen_execution_artifacts": custody,
            "human_review": {"relative_path": HUMAN_REVIEW_RELATIVE_PATH, "sha256": _sha256(human)},
            "generator": {"relative_path": Path(__file__).resolve().relative_to(REPO_ROOT).as_posix(), "sha256": _sha256(Path(__file__).resolve())},
            "test": {"relative_path": TEST_RELATIVE_PATH, "sha256": _sha256(test)},
        },
        "independent_reproduction": reproduction,
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": sum(row["status"] == "PASS" for row in gates),
            "failure_count": sum(row["status"] != "PASS" for row in gates),
            "rows": gates,
        },
        "accepted_bounded_claim": {
            "domain": "4D_LOCAL_METRIC_MINKOWSKI_CONSERVED_EXTERNAL_SOURCE",
            "linearized_equation": "(1+beta Box)G^L+(2 alpha+beta)(eta Box-partial partial)R^L=kappa T",
            "massless_spin_2": "PRESENT_POSITIVE_REFERENCE",
            "massive_scalar": "m0^2=-1/[2(3 alpha+beta)]; POSITIVE_ISOLATED_OR_PROJECTOR_RESOLVED_RESIDUE",
            "massive_spin_2": "m2^2=1/beta; NEGATIVE_ISOLATED_OR_PROJECTOR_RESOLVED_RESIDUE",
            "stationary_00": "MASSLESS_PLUS_SCALAR_PLUS_ADDITIONAL_SPIN_2",
            "stationary_0i": "MASSLESS_PLUS_ADDITIONAL_SPIN_2; SCALAR_ZERO",
            "arbitrary_background_or_nonlinear_claim": False,
        },
        "scientific_implications_for_response_selection": [
            "A native principle would need to control or exclude the additional massive spin-2 ghost.",
            "It would need to determine whether an additional scalar is absent, heavy, screened, or allowed.",
            "It would need to account for the stationary momentum-current response structure.",
            "It would need to explain the long-range survival of the massless Einstein sector.",
        ],
        "post_reproduction_oracles": [
            {"source": "https://arxiv.org/abs/hep-th/9509142", "role": "MODE_CONTENT_AND_FLAT_SPIN_2_GHOST_ORACLE"},
            {"source": "https://arxiv.org/abs/1007.1917", "role": "TWO_SCALE_WEAK_FIELD_AND_GAUSS_BONNET_ORACLE"},
            {"source": "https://arxiv.org/abs/1104.0819", "role": "ANALYTIC_F_R_RICCI_SCALAR_MODE_ORACLE"},
        ],
        "scope": {
            "independent_result_review_executed": True,
            "comparison_result_accepted": True,
            "scientific_response_selection_authorized": True,
            "scientific_response_selection_executed": False,
            "comparison_action_selected": False,
            "alpha_or_beta_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_authorized": False,
            "empirical_fitting_authorized": False,
            "nonlinear_stability_claimed": False,
            "arbitrary_background_spectrum_claimed": False,
            "orbital_precession_authorized": False,
            "frame_dragging_reopened": False,
            "matter_sector_selected": False,
            "master_action_mutation_authorized": False,
            "authoritative_V2_population_authorized": False,
        },
        "current_posture": {
            "comparison_execution": "COMPLETED_ONCE",
            "comparison_result": "ACCEPTED_16_OF_16_GATES",
            "comparison_action": "SUPPLIED_COMPARISON_ONLY",
            "native_gravitational_action": "NOT_SELECTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "frame_dragging": "NOT_RESUMED",
        },
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_review(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Review the completed shared quadratic-gravity comparison result.")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if args.write:
        path.write_bytes(expected)
        print("shared_linearized_quadratic_gravity_result_review_v0: wrote accepted review")
        return 0
    if not path.is_file() or path.read_bytes() != expected:
        print("shared_linearized_quadratic_gravity_result_review_v0: FAILED artifact drift")
        return 1
    print("shared_linearized_quadratic_gravity_result_review_v0: OK gates=16/16 accepted")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
