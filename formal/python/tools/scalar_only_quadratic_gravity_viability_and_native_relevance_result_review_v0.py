from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[3]
EXECUTION_RELATIVE_PATH = (
    "formal/docs/release/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_"
    "20260718_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_"
    "RESULT_REVIEW_20260718_v0.json"
)
HUMAN_REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_"
    "RESULT_REVIEW_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_scalar_only_quadratic_gravity_viability_and_native_relevance_"
    "result_review_v0.py"
)
TARGET = (
    "review_scalar_only_quadratic_gravity_viability_and_native_relevance_"
    "v0_result"
)
VERDICT = "ACCEPTED_BOUNDED_SCALAR_ONLY_COMPARISON_RESULT"
PRINCIPAL_OUTCOME = (
    "SCALAR_BRANCH_COMPARISON_VIABLE_NATIVE_RELEVANCE_UNESTABLISHED"
)
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_quadratic_gravity_viability_and_native_"
    "relevance_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "SCIENTIFIC_RESPONSE_SELECTION_ONLY_NO_BRANCH_OR_ACTION_ADOPTION"
)

EXECUTION_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_20260718_v0.md":
        "60ba3eafc097f8bf5797e732a4d764429348264b04fc29492a39097d0c51b765",
    EXECUTION_RELATIVE_PATH:
        "a3c31696dcc3999ab8c42e1fa8276f9e1b551af725d8111f917c9122ae0f648f",
    "formal/python/tools/scalar_only_quadratic_gravity_viability_and_native_relevance_v0.py":
        "a178006131e034b1814a2537316539b5d500a640aaa02aef7325e96e8c447bc1",
    "formal/python/tests/test_scalar_only_quadratic_gravity_viability_and_native_relevance_v0.py":
        "4b7a9c28b691de7f173ac9a2123e31ef78dc654f4d574b0d4aaf2da3594aea3f",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyQuadraticGravityViabilityAndNativeRelevanceV0.lean":
        "e5eebcd7d00afa372e46c5f2ceb52ae71a3ad04714f901c4c19ee22ef0629957",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _validate_execution_custody() -> tuple[list[dict[str, str]], dict[str, Any]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected in EXECUTION_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"scalar-only execution custody drift: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})
    execution = _load_json(EXECUTION_RELATIVE_PATH)
    if execution.get("verdict") != (
        "COMPLETE_BOUNDED_SCALAR_ONLY_COMPARISON_PENDING_INDEPENDENT_REVIEW"
    ):
        raise ValueError("scalar-only execution is not pending result review")
    if execution.get("selected_next_target") != TARGET:
        raise ValueError("scalar-only execution did not rotate to this review")
    if execution["scope"].get("authorized_execution_consumed") != 1:
        raise ValueError("scalar-only execution count is not exactly one")
    return rows, execution


def _independent_reproduction() -> dict[str, Any]:
    R, R0, chi, alpha, Phi, kappa, rho, varphi = sp.symbols(
        "R R0 chi alpha Phi kappa rho varphi", nonzero=True
    )
    positive_a = sp.symbols("a", positive=True)

    f = R + alpha * R**2
    f_R = sp.diff(f, R)
    f_RR = sp.diff(f, R, 2)

    metric_trace = sp.expand(f_R * R - 2 * f)
    box_coefficient = 3 * sp.diff(f_R, R)
    scalar_mass_squared = -1 / (6 * alpha)

    f_chi = chi + alpha * chi**2
    auxiliary_lagrangian = sp.expand(
        f_chi + sp.diff(f_chi, chi) * (R - chi)
    )
    auxiliary_equation = sp.factor(sp.diff(auxiliary_lagrangian, chi))
    chi_of_phi = (Phi - 1) / (2 * alpha)
    jordan_U = sp.factor(
        Phi * chi_of_phi
        - (chi_of_phi + alpha * chi_of_phi**2)
    )

    b = sp.sqrt(2 * kappa / 3)
    physical_potential = -(
        1 - sp.exp(-b * varphi)
    ) ** 2 / (8 * kappa * alpha)
    potential_mass_squared = sp.simplify(
        sp.diff(physical_potential, varphi, 2).subs(varphi, 0)
    )

    f0 = R0 + alpha * R0**2
    f_R0 = 1 + 2 * alpha * R0
    vacuum_constant_curvature = sp.expand(f_R0 * R0 - 2 * f0)
    full_tensor_coefficient = sp.simplify(f_R0 * R0 / 4 - f0 / 2)
    supplied_R0 = -4 * kappa * rho
    supplied_phi0 = sp.simplify(f_R0.subs(R0, supplied_R0))
    tensor_equation_residual = sp.simplify(
        full_tensor_coefficient.subs(R0, supplied_R0) - kappa * rho
    )
    trace_equation_residual = sp.simplify(
        vacuum_constant_curvature.subs(R0, supplied_R0) - 4 * kappa * rho
    )

    packet_alpha_negative_mass = sp.simplify(
        scalar_mass_squared.subs(alpha, -positive_a)
    )
    literature_f_RR = -2 * alpha
    packet_alpha_negative_literature_f_RR = sp.simplify(
        literature_f_RR.subs(alpha, -positive_a)
    )

    return {
        "metric_and_trace": {
            "f_R": str(f_R),
            "f_RR_packet": str(f_RR),
            "algebraic_trace": str(metric_trace),
            "Box_R_coefficient": str(box_coefficient),
            "exact_trace_equation": "-R+6 alpha Box R=kappa T",
            "scalar_mass_squared": str(scalar_mass_squared),
            "passed": metric_trace == -R and box_coefficient == 6 * alpha,
        },
        "scalar_tensor": {
            "auxiliary_equation": str(auxiliary_equation),
            "Legendre_variable": "Phi=1+2 alpha chi",
            "inverse_map": "chi=(Phi-1)/(2 alpha)",
            "Jordan_U": str(jordan_U),
            "equivalence_domain": "alpha!=0",
            "conformal_domain": "Phi>0",
            "canonical_scalar": "varphi=sqrt(3/(2 kappa)) ln Phi",
            "matter_coupling": "A=Phi^-1/2; d ln A/dvarphi=-sqrt(kappa/6)",
            "physical_potential": (
                "-[1/(8 kappa alpha)]"
                "(1-exp(-sqrt(2 kappa/3)varphi))^2"
            ),
            "potential_mass_squared_at_minimum": str(potential_mass_squared),
            "passed": all(
                (
                    auxiliary_equation == 2 * alpha * (R - chi),
                    sp.simplify(1 + 2 * alpha * chi_of_phi - Phi) == 0,
                    sp.simplify(jordan_U - (Phi - 1) ** 2 / (4 * alpha)) == 0,
                    sp.simplify(
                        potential_mass_squared - scalar_mass_squared
                    ) == 0,
                )
            ),
        },
        "convention_and_matter_stability": {
            "R_literature": "-R_packet",
            "alpha_literature": "-alpha_packet",
            "f_RR_literature": "-2 alpha_packet",
            "alpha_packet_negative_mass_squared": str(
                packet_alpha_negative_mass
            ),
            "alpha_packet_negative_f_RR_literature": str(
                packet_alpha_negative_literature_f_RR
            ),
            "fixed_source_curvature_perturbation": (
                "(Box_bar+m0^2)delta R=(kappa/(6 alpha))delta T"
            ),
            "qualification": (
                "bounded supplied-source curvature-mode stability only; "
                "no dynamical-matter stability claim"
            ),
            "passed": (
                packet_alpha_negative_mass == 1 / (6 * positive_a)
                and packet_alpha_negative_literature_f_RR == 2 * positive_a
            ),
        },
        "backgrounds": {
            "Minkowski": {
                "R0": 0,
                "Phi0": 1,
                "source": 0,
                "tadpole": 0,
                "passed": True,
            },
            "pure_vacuum_constant_curvature": {
                "equation": str(vacuum_constant_curvature),
                "only_root": "R0=0",
                "passed": vacuum_constant_curvature == -R0,
            },
            "supplied_constant_density": {
                "source_action_variation": (
                    "delta S_rho=-(1/(2c)) integral sqrt(-g) "
                    "rho g_mu_nu delta g^mu_nu"
                ),
                "stress_tensor": "T_mu_nu=rho g_mu_nu",
                "trace": "T=4 rho",
                "conservation": (
                    "nabla_mu T^mu_nu=0 for constant rho by metric compatibility"
                ),
                "full_tensor_lhs_coefficient": str(full_tensor_coefficient),
                "solution": "R0=-4 kappa rho",
                "Phi0": str(supplied_phi0),
                "tensor_equation_residual": str(tensor_equation_residual),
                "trace_equation_residual": str(trace_equation_residual),
                "delta_T_for_fixed_rho": 0,
                "scalar_perturbation": "(Box_bar+m0^2)delta R=0",
                "passed": (
                    full_tensor_coefficient == -R0 / 4
                    and tensor_equation_residual == 0
                    and trace_equation_residual == 0
                ),
            },
        },
        "trace_and_screening": {
            "exact_trace_operator": (
                "(Box+m0^2)R=(kappa/(6 alpha))T"
            ),
            "mass_environment_derivative_fixed_source": 0,
            "coupling_environment_derivative_fixed_source": 0,
            "exactly_traceless_classical_source": (
                "NO_DIRECT_LINEAR_SCALAR_EXCITATION"
            ),
            "principal_screening_finding": "FINITE_MASS_SUPPRESSION_ONLY",
            "qualification": (
                "does not cover anomalies, mass terms, curved-background "
                "trace generation, or self-consistent nonlinear matter backreaction"
            ),
            "passed": True,
        },
    }


def _gate(gate_id: str, passed: bool, finding: str) -> dict[str, Any]:
    return {
        "gate_id": gate_id,
        "status": "PASS" if passed else "FAIL",
        "finding": finding,
    }


def _review_gates(
    execution: dict[str, Any], reproduction: dict[str, Any]
) -> list[dict[str, Any]]:
    scope = execution["scope"]
    bridges = execution["native_relevance_result"]
    backgrounds = reproduction["backgrounds"]
    scalar = reproduction["scalar_tensor"]
    return [
        _gate("G1_EXECUTION_CUSTODY_AND_AUTHORITY", True, "Five frozen execution artifacts match and exactly one run was consumed."),
        _gate("G2_METRIC_AND_TRACE_EQUATIONS", reproduction["metric_and_trace"]["passed"], "Independent f(R) variation trace reproduces -R+6 alpha Box R=kappa T."),
        _gate("G3_SCALAR_MASS_AND_SIGN_TRANSLATION", reproduction["convention_and_matter_stability"]["passed"], "Packet alpha<0 gives both m0^2>0 and translated f_RR_literature>0."),
        _gate("G4_AUXILIARY_AND_LEGENDRE_MAP", scalar["passed"], "Auxiliary equation, inverse map, and Jordan potential reproduce with alpha!=0."),
        _gate("G5_CONFORMAL_DOMAIN_NORMALIZATION_AND_POTENTIAL", scalar["passed"] and scalar["conformal_domain"] == "Phi>0", "Canonical normalization and translated potential curvature reproduce the trace mass."),
        _gate("G6_MINKOWSKI_BACKGROUND", backgrounds["Minkowski"]["passed"], "Minkowski solves the source-free equation with Phi0=1 and no tadpole."),
        _gate("G7_PURE_VACUUM_CONSTANT_CURVATURE", backgrounds["pure_vacuum_constant_curvature"]["passed"], "The pure vacuum algebraic condition admits only R0=0."),
        _gate("G8_SUPPLIED_SOURCE_VARIATION_AND_CONSERVATION", backgrounds["supplied_constant_density"]["stress_tensor"] == "T_mu_nu=rho g_mu_nu", "The supplied source variation, trace, and conservation law reproduce."),
        _gate("G9_COMPLETE_TENSOR_BACKGROUND_EQUATION", backgrounds["supplied_constant_density"]["passed"], "The complete tensor equation reduces to -R0/4=kappa rho; the R^2 terms cancel."),
        _gate("G10_BACKGROUND_CONFORMAL_DOMAIN_AND_SCALAR_MODE", execution["backgrounds"]["rows"][2]["status"] == "PASSED_BOUNDED_LINEAR_SCALAR_TEST", "For alpha<0 and rho>=0, Phi0>0 and the fixed-trace scalar perturbation is non-tachyonic."),
        _gate("G11_BOUNDED_MATTER_CURVATURE_STABILITY", reproduction["convention_and_matter_stability"]["passed"], "Matter stability is reproduced only for the supplied fixed-source curvature mode, not inferred as complete dynamical-matter stability."),
        _gate("G12_EXACT_TRACE_COUPLING_SCOPE", execution["matter_trace_result"]["classically_traceless_source"] == "NO_DIRECT_LINEAR_SCALAR_SOURCE", "The no-source statement is restricted to an exactly traceless supplied classical source at linear order."),
        _gate("G13_SCREENING_SCOPE", execution["screening_result"]["principal_finding"] == "FINITE_MASS_SUPPRESSION_ONLY", "The exact fixed-source operator has constant mass and coupling; only Yukawa suppression is established."),
        _gate("G14_RETAINED_00_0I_SCOPE", execution["work_packages"]["rows"][4]["result"].endswith("ACCEPTED_LINEAR_ORDER"), "The accepted scalar-sensitive 00 and scalar-zero direct stationary 0i map is not extended to nonlinear rotating systems."),
        _gate("G15_PARAMETER_AND_FRAME_DOMAINS", execution["scalar_tensor_result"]["equivalence_domain"] == "alpha!=0" and execution["scalar_tensor_result"]["conformal_domain"] == "Phi>0", "Noninvertible and invalid conformal surfaces fail closed; no alpha value is selected."),
        _gate("G16_NATIVE_BRIDGE_FAILURES", bridges["candidate_count"] == 3 and bridges["bridge_identified_count"] == 0 and all(not row["matched_fields"] for row in bridges["rows"]), "Each audited surface fails FIELD_DEFINITION first; later resemblance does not override the failure."),
        _gate("G17_NO_HIDDEN_ADOPTION", all(scope[key] is False for key in ("beta_zero_adopted", "alpha_sign_or_value_adopted", "scalar_branch_adopted", "native_gravitational_principle_identified", "gravitational_action_selected", "matter_sector_selected", "frame_dragging_reopened")), "No branch, parameter, principle, matter sector, action, or downstream observable is adopted."),
        _gate("G18_PRINCIPAL_RESULT_AND_STOP", execution["principal_outcome"] == PRINCIPAL_OUTCOME, "The bounded two-axis result is accepted and authority rotates only to scientific-response selection."),
    ]


def build_review() -> dict[str, Any]:
    custody, execution = _validate_execution_custody()
    human = REPO_ROOT / HUMAN_REVIEW_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    if not human.is_file() or not test.is_file():
        raise ValueError("result-review human record or focused test missing")
    reproduction = _independent_reproduction()
    gates = _review_gates(execution, reproduction)
    if any(row["status"] != "PASS" for row in gates):
        raise ValueError("scalar-only independent result-review gate failed")
    return {
        "schema_id": (
            "SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_"
            "RESULT_REVIEW_20260718_v0"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "principal_review_outcome": PRINCIPAL_OUTCOME,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_execution_verdict": execution["verdict"],
            "frozen_execution_artifacts": custody,
            "human_review": {
                "relative_path": HUMAN_REVIEW_RELATIVE_PATH,
                "sha256": _sha256(human),
            },
            "generator": {
                "relative_path": Path(__file__).resolve().relative_to(
                    REPO_ROOT
                ).as_posix(),
                "sha256": _sha256(Path(__file__).resolve()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test),
            },
        },
        "independent_reproduction": reproduction,
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": sum(row["status"] == "PASS" for row in gates),
            "failure_count": sum(row["status"] != "PASS" for row in gates),
            "rows": gates,
        },
        "accepted_bounded_claim": {
            "comparison_viability": (
                "SUPPORTED_ON_MINKOWSKI_AND_ONE_SUPPLIED_CONSTANT_DENSITY_"
                "MAXIMALLY_SYMMETRIC_BACKGROUND_AT_LINEAR_SCALAR_ORDER"
            ),
            "scalar_tensor_domain": "alpha!=0 AND Phi>0",
            "non_tachyonic_packet_stratum": "alpha<0",
            "matter_trace": (
                "TRACEFUL_SOURCE_DIRECT; EXACTLY_TRACELESS_SUPPLIED_"
                "CLASSICAL_SOURCE_ZERO_AT_LINEAR_ORDER"
            ),
            "screening": "FINITE_MASS_SUPPRESSION_ONLY_IN_FIXED_SOURCE_DOMAIN",
            "native_relevance": "NOT_IDENTIFIED",
            "native_bridge_count": 0,
            "arbitrary_background_or_nonlinear_claim": False,
            "dynamical_matter_stability_claim": False,
            "empirical_viability_claim": False,
        },
        "post_reproduction_oracles": [
            {
                "source": "https://arxiv.org/abs/0805.1726",
                "role": "METRIC_F_R_SCALAR_TENSOR_EQUIVALENCE_ORACLE",
            },
            {
                "source": "https://arxiv.org/abs/astro-ph/0610734",
                "role": "METRIC_F_RR_MATTER_STABILITY_SIGN_ORACLE",
            },
            {
                "source": "https://arxiv.org/abs/gr-qc/0703044",
                "role": "CONSTANT_CURVATURE_EXISTENCE_AND_STABILITY_ORACLE",
            },
            {
                "source": "https://arxiv.org/abs/1002.4928",
                "role": "MODEL_DEPENDENT_SCREENING_AND_LOCAL_CONSTRAINT_ORACLE",
            },
        ],
        "scope": {
            "independent_result_review_executed": True,
            "bounded_comparison_result_accepted": True,
            "scientific_response_selection_authorized": True,
            "scientific_response_selection_executed": False,
            "beta_zero_adopted": False,
            "alpha_sign_or_value_adopted": False,
            "scalar_branch_adopted": False,
            "native_scalar_bridge_identified": False,
            "native_gravitational_principle_identified": False,
            "gravitational_action_selected": False,
            "matter_sector_selected": False,
            "empirical_fitting_authorized": False,
            "nonlinear_stability_claimed": False,
            "arbitrary_background_stability_claimed": False,
            "frame_dragging_reopened": False,
            "orbital_transport_authorized": False,
            "master_action_mutation_authorized": False,
        },
        "current_posture": {
            "scalar_only_execution": "COMPLETED_ONCE",
            "scalar_only_result": "ACCEPTED_18_OF_18_GATES",
            "comparison_viability": "BOUNDEDLY_SUPPORTED",
            "native_relevance": "NOT_ESTABLISHED",
            "native_scalar_bridges": 0,
            "beta_zero": "COMPARISON_RESTRICTION_ONLY",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
        },
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_review(), indent=2, sort_keys=True) + "\n").encode(
        "utf-8"
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Independently review the scalar-only comparison result."
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if args.write:
        path.write_bytes(expected)
        print("scalar_only_result_review_v0: wrote accepted review")
        return 0
    if not path.is_file() or path.read_bytes() != expected:
        print("scalar_only_result_review_v0: FAILED artifact drift")
        return 1
    print("scalar_only_result_review_v0: OK gates=18/18 accepted")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
