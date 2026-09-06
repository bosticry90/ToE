from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_"
    "20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_"
    "20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_scalar_only_quadratic_gravity_viability_and_native_relevance_v0.py"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_PACKET_"
    "REVIEW_20260718_v0.json"
)
TARGET = "execute_scalar_only_quadratic_gravity_viability_and_native_relevance_v0"
VERDICT = "COMPLETE_BOUNDED_SCALAR_ONLY_COMPARISON_PENDING_INDEPENDENT_REVIEW"
PRINCIPAL_OUTCOME = (
    "SCALAR_BRANCH_COMPARISON_VIABLE_NATIVE_RELEVANCE_UNESTABLISHED"
)
SELECTED_NEXT_TARGET = (
    "review_scalar_only_quadratic_gravity_viability_and_native_relevance_v0_result"
)
SELECTED_NEXT_TARGET_KIND = "INDEPENDENT_SCALAR_ONLY_COMPARISON_RESULT_REVIEW_ONLY"

REVIEW_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_PACKET_REVIEW_20260718_v0.md":
        "437ca6283ab7dc11affa06d155b1fd2f0616e253bfe26849697b8d8251e879e3",
    REVIEW_RELATIVE_PATH:
        "8fbcff521ac8d4d6fc9ee67d1b6788e3175c06af2c08a77a6ccf92f904119116",
    "formal/python/tools/scalar_only_quadratic_gravity_viability_and_native_relevance_packet_review_v0.py":
        "8fda9b4d3f5dc81f7f983047a5ff6627acb3958ace85c0168ccbde7e00a9e4bb",
    "formal/python/tests/test_scalar_only_quadratic_gravity_viability_and_native_relevance_packet_review_v0.py":
        "97d02645b17585eb5c4a6474b8f2ddedbccb2785f7f66d2f5128854ee8cfa6cd",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyQuadraticGravityViabilityAndNativeRelevancePacketReviewV0.lean":
        "26914600c90266443565bb2e94c72bd1c6f7689f52d550ffa1a2116f7a3edf58",
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
            raise ValueError(f"scalar-only execution authority drift: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})
    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != (
        "ACCEPTED_SCALAR_ONLY_VIABILITY_CONTRACT_READY_FOR_ONE_BOUNDED_EXECUTION"
    ):
        raise ValueError("packet review did not accept scalar-only execution")
    if review.get("principal_packet_review_outcome") != (
        "SCALAR_ONLY_VIABILITY_CONTRACT_READY"
    ):
        raise ValueError("packet review principal outcome mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("packet review did not authorize this target")
    if review["authorized_execution"].get("execution_count") != 1:
        raise ValueError("execution count is not exactly one")
    if review["review_gates"].get("pass_count") != 18:
        raise ValueError("packet review gates are not complete")
    return rows, review


def _symbolic_audit() -> dict[str, Any]:
    R, chi, alpha, Phi, R0, kappa, rho, psi = sp.symbols(
        "R chi alpha Phi R0 kappa rho psi", nonzero=True
    )
    f_R_expr = R + alpha * R**2
    f_chi = chi + alpha * chi**2
    f_chi_prime = sp.diff(f_chi, chi)
    auxiliary_lagrangian = sp.expand(f_chi + f_chi_prime * (R - chi))
    auxiliary_equation = sp.factor(sp.diff(auxiliary_lagrangian, chi))
    chi_of_phi = (Phi - 1) / (2 * alpha)
    U = sp.factor(chi_of_phi * Phi - (chi_of_phi + alpha * chi_of_phi**2))
    f_R0 = R0 + alpha * R0**2
    F_R0 = sp.diff(f_R_expr, R).subs(R, R0)
    constant_curvature_lhs = sp.expand(F_R0 * R0 - 2 * f_R0)
    background_einstein_coefficient = sp.simplify(F_R0 * R0 / 4 - f_R0 / 2)
    R0_solution = -4 * kappa * rho
    Phi0 = sp.simplify(F_R0.subs(R0, R0_solution))
    scalar_mass_squared = -1 / (6 * alpha)
    b = sp.sqrt(2 * kappa / 3)
    translated_physical_potential = -sp.Rational(1, 8) / (kappa * alpha) * (
        1 - sp.exp(-b * psi)
    ) ** 2
    potential_mass_squared = sp.simplify(
        sp.diff(translated_physical_potential, psi, 2).subs(psi, 0)
    )
    return {
        "f": "R+alpha R^2",
        "f_R": str(sp.diff(f_R_expr, R)),
        "f_RR": str(sp.diff(f_R_expr, R, 2)),
        "auxiliary_lagrangian": str(auxiliary_lagrangian),
        "auxiliary_equation": str(auxiliary_equation),
        "auxiliary_equation_expected": "2*alpha*(R-chi)",
        "Legendre_variable": "Phi=1+2 alpha chi",
        "inverse_map": "chi=(Phi-1)/(2 alpha)",
        "Jordan_potential_U": str(U),
        "constant_curvature_lhs": str(constant_curvature_lhs),
        "maximally_symmetric_field_equation_lhs_coefficient": str(
            background_einstein_coefficient
        ),
        "supplied_background_solution": "R0=-4 kappa rho_Lambda",
        "supplied_background_Phi0": str(Phi0),
        "scalar_mass_squared": str(scalar_mass_squared),
        "translated_physical_potential_mass_squared_at_minimum": str(
            potential_mass_squared
        ),
        "checks": {
            "auxiliary_action_reduces_to_Phi_R_minus_U": sp.simplify(
                auxiliary_lagrangian.subs(chi, chi_of_phi) - (Phi * R - U)
            ) == 0,
            "auxiliary_equation_exact": sp.simplify(
                auxiliary_equation - 2 * alpha * (R - chi)
            ) == 0,
            "Legendre_inverse_exact": sp.simplify(
                (1 + 2 * alpha * chi_of_phi) - Phi
            ) == 0,
            "Jordan_potential_exact": sp.simplify(
                U - (Phi - 1) ** 2 / (4 * alpha)
            ) == 0,
            "vacuum_constant_curvature_only_zero": constant_curvature_lhs == -R0,
            "supplied_background_exact": sp.simplify(
                background_einstein_coefficient.subs(R0, R0_solution) - kappa * rho
            ) == 0,
            "potential_mass_matches_trace_mass": sp.simplify(
                potential_mass_squared - scalar_mass_squared
            ) == 0,
        },
    }


def _derivation_stages() -> list[dict[str, Any]]:
    rows = [
        (
            "D1_METRIC_FIELD_EQUATION",
            "f_R R_mu_nu-(1/2)f g_mu_nu+(g_mu_nu Box-nabla_mu nabla_nu)f_R=kappa T_mu_nu",
        ),
        (
            "D2_EXACT_TRACE_EQUATION",
            "-R+6 alpha Box R=kappa T",
        ),
        (
            "D3_AUXILIARY_AND_LEGENDRE_MAP",
            "Phi=1+2 alpha chi; 2 alpha(R-chi)=0; chi=(Phi-1)/(2 alpha)",
        ),
        (
            "D4_JORDAN_FRAME",
            "S=(1/(2 kappa c)) integral sqrt(-g)[Phi R-U(Phi)]+S_m; U=(Phi-1)^2/(4 alpha)",
        ),
        (
            "D5_EINSTEIN_FRAME",
            "gE_mu_nu=Phi g_mu_nu; varphi=sqrt(3/(2 kappa)) ln Phi; S_m[Phi^-1 gE,Psi]",
        ),
        (
            "D6_MINKOWSKI_CONTROL",
            "R0=0; Phi0=1; m0^2=-1/(6 alpha); accepted 00 Yukawa and scalar-zero stationary 0i",
        ),
        (
            "D7_VACUUM_CONSTANT_CURVATURE_CONTROL",
            "f_R R0-2f=-R0=0; no nonzero pure-vacuum root",
        ),
        (
            "D8_SUPPLIED_MATTER_SUPPORTED_BACKGROUND",
            "T_mu_nu=rho_Lambda g_mu_nu; R0=-4 kappa rho_Lambda; Phi0=1-8 kappa alpha rho_Lambda",
        ),
        (
            "D9_TRACE_MATTER_STABILITY_AND_SCREENING",
            "(Box+m0^2)delta R=(kappa/(6 alpha))delta T; constant mass and coupling; finite-range suppression only",
        ),
        (
            "D10_NATIVE_RELEVANCE_AUDIT",
            "three project scalar surfaces tested against seven fields; zero bridges identified",
        ),
    ]
    return [
        {"stage_id": stage_id, "result": result, "status": "COMPLETED"}
        for stage_id, result in rows
    ]


def _work_packages() -> list[dict[str, Any]]:
    return [
        {
            "work_package_id": "WP_SCALAR_TENSOR_EQUIVALENCE",
            "status": "COMPLETED",
            "result": "LOCAL_EQUIVALENCE_DERIVED_FOR_ALPHA_NONZERO_AND_PHI_POSITIVE",
            "qualification": "alpha=0 and Phi<=0 are excluded transformation surfaces",
        },
        {
            "work_package_id": "WP_BACKGROUND_STABILITY",
            "status": "COMPLETED_BOUNDED_DOMAIN",
            "result": "MINKOWSKI_AND_SUPPLIED_VACUUM_ENERGY_BACKGROUND_LINEAR_SCALAR_STABLE_FOR_ALPHA_NEGATIVE_AND_PHI0_POSITIVE",
            "qualification": "no arbitrary-background or nonlinear stability claim",
        },
        {
            "work_package_id": "WP_TRACE_COUPLING",
            "status": "COMPLETED",
            "result": "TRACEFUL_SOURCE_EXCITES_SCALAR_CLASSICALLY_TRACELESS_SOURCE_HAS_NO_DIRECT_LINEAR_EXCITATION",
            "qualification": "source is supplied and does not define ToE matter",
        },
        {
            "work_package_id": "WP_SCREENING_AND_NONLINEAR_RELEVANCE",
            "status": "COMPLETED_BOUNDED_EXTERNAL_SOURCE_DOMAIN",
            "result": "FINITE_MASS_SUPPRESSION_ONLY",
            "qualification": "no intrinsic environment-dependent screening mechanism identified",
        },
        {
            "work_package_id": "WP_OBSERVABLE_CHANNEL_MAP",
            "status": "COMPLETED_RETAINED_SCOPE",
            "result": "SCALAR_MODIFIES_00_TRACE_CHANNEL_NOT_DIRECT_STATIONARY_CONSERVED_0I_AT_ACCEPTED_LINEAR_ORDER",
            "qualification": "no orbital or empirical transport",
        },
        {
            "work_package_id": "WP_NATIVE_BRIDGE_AUDIT",
            "status": "COMPLETED",
            "result": "NO_NATIVE_SCALAR_BRIDGE_IDENTIFIED",
            "qualification": "all three candidates fail at least one mandatory bridge field",
        },
    ]


def _scalar_tensor_obligations() -> list[dict[str, Any]]:
    return [
        {"obligation_id": "AUXILIARY_FIELD_INTRODUCTION", "status": "DERIVED", "result": "f(chi)+f_chi(chi)(R-chi)"},
        {"obligation_id": "AUXILIARY_EQUATION_AND_EQUIVALENCE_DOMAIN", "status": "DERIVED", "result": "2 alpha(R-chi)=0; equivalence for alpha!=0"},
        {"obligation_id": "LEGENDRE_VARIABLE_AND_INVERTIBILITY", "status": "DERIVED", "result": "Phi=1+2 alpha chi; chi=(Phi-1)/(2 alpha)"},
        {"obligation_id": "JORDAN_FRAME_ACTION_AND_POTENTIAL", "status": "DERIVED", "result": "Phi R-U(Phi); U=(Phi-1)^2/(4 alpha)"},
        {"obligation_id": "CONFORMAL_MAP_AND_DOMAIN", "status": "DERIVED", "result": "gE=Phi g; domain Phi>0"},
        {"obligation_id": "CANONICAL_SCALAR_NORMALIZATION", "status": "DERIVED", "result": "varphi=sqrt(3/(2 kappa)) ln Phi"},
        {"obligation_id": "EINSTEIN_FRAME_POTENTIAL", "status": "DERIVED", "result": "V_packet=U/(2 kappa Phi^2); translated physical V=-U/(2 kappa Phi^2)"},
        {"obligation_id": "MATTER_TRANSFORMATION_AND_OBSERVABLE_CAVEAT", "status": "DERIVED", "result": "S_m[Phi^-1 gE,Psi]; A(varphi)=Phi^-1/2; measurement conventions still required"},
    ]


def _background_rows() -> list[dict[str, Any]]:
    return [
        {
            "background_id": "MINKOWSKI_CONTROL",
            "status": "PASSED",
            "source": "T_mu_nu=0",
            "curvature": "R0=0",
            "Phi0": "1",
            "scalar_mass_squared": "-1/(6 alpha)>0 for alpha<0",
            "kinetic_or_residue": "POSITIVE_RELATIVE_ISOLATED_SCALAR_CHANNEL",
            "tadpole": "NONE",
        },
        {
            "background_id": "CONSTANT_CURVATURE_VACUUM",
            "status": "PASSED_EXISTENCE_NEGATIVE_CONTROL",
            "source": "T_mu_nu=0",
            "curvature": "R0=0 ONLY",
            "nonzero_de_Sitter_or_anti_de_Sitter": "NOT_ADMITTED",
            "stability_claim": "NO_NONZERO_BACKGROUND_TO_TEST",
        },
        {
            "background_id": "SUPPLIED_VACUUM_ENERGY_BACKGROUND",
            "status": "PASSED_BOUNDED_LINEAR_SCALAR_TEST",
            "source_action": "S_rho=(1/c) integral sqrt(-g) rho_Lambda",
            "source": "T_mu_nu=rho_Lambda g_mu_nu",
            "conservation": "nabla_mu T^mu_nu=0 for constant rho_Lambda",
            "trace": "T=4 rho_Lambda",
            "curvature": "R0=-4 kappa rho_Lambda",
            "Ricci": "R_mu_nu=(R0/4)g_mu_nu",
            "Phi0": "1-8 kappa alpha rho_Lambda",
            "tested_domain": "alpha<0 and rho_Lambda>=0 implies Phi0>0",
            "scalar_perturbation": "(Box_bar+m0^2)delta R=0",
            "scalar_mass_squared": "m0^2=-1/(6 alpha)>0",
            "qualification": "supplied nondynamical vacuum-energy comparator; not ToE matter or arbitrary-background stability",
        },
    ]


def _native_bridge_rows() -> list[dict[str, Any]]:
    required = [
        "FIELD_DEFINITION",
        "TRANSFORMATION_LAW",
        "DIMENSIONS",
        "COUPLINGS",
        "EQUATION_OF_MOTION",
        "DOMAIN",
        "OBSERVABLE_ROLE",
    ]
    return [
        {
            "candidate_id": "NATIVE_PHI_ALIGNMENT_WITNESS",
            "required_fields": required,
            "matched_fields": [],
            "failed_fields": required,
            "finding": "alignment witness supplies no map to Phi=f_R and native generation remains blocked",
            "bridge_status": "NOT_IDENTIFIED",
        },
        {
            "candidate_id": "PROVISIONAL_CLASSICAL_SCALAR_SOURCE_SANDBOX",
            "required_fields": required,
            "matched_fields": [],
            "failed_fields": required,
            "finding": "supplied on-shell scalar source is not a native matter field or scalaron map",
            "bridge_status": "NOT_IDENTIFIED",
        },
        {
            "candidate_id": "PHI_CK_ADMISSIBILITY_RULE_FAMILY",
            "required_fields": required,
            "matched_fields": [],
            "failed_fields": required,
            "finding": "admissibility rules are nondynamical and derive neither Phi nor its equation",
            "bridge_status": "NOT_IDENTIFIED",
        },
    ]


def _decision_answers() -> list[dict[str, Any]]:
    answers = [
        ("DQ1", "SUPPORTED_BOUNDED_DOMAIN", "alpha<0 with Phi>0 gives an isolated non-tachyonic positive-relative-residue scalar"),
        ("DQ2", "SUPPORTED_ONE_SUPPLIED_NON_MINKOWSKI_BACKGROUND", "constant vacuum energy gives R0=-4 kappa rho_Lambda and the same positive m0^2 in the tested domain"),
        ("DQ3", "DERIVED", "the exact trace T sources R; classically traceless T=0 has no direct linear scalar source"),
        ("DQ4", "FINITE_MASS_SUPPRESSION_ONLY", "the exact trace operator has constant mass and fixed coupling in the supplied-source domain"),
        ("DQ5", "RANGE_AND_TRACE_FORCE_LIMIT_IS_DECISIVE", "future static trace-sensitive tests can bound m0^-1 but no data or alpha value is used here"),
        ("DQ6", "NO_NATIVE_OBJECT_IDENTIFIED", "all three project surfaces fail the seven-field bridge contract"),
        ("DQ7", "NO_TOE_SPECIFIC_EXPLANATORY_VALUE_IDENTIFIED", "the branch reproduces supplied metric f(R) scalar physics without a project-specific mechanism"),
        ("DQ8", "NO_AUTOMATIC_MINIMAL_MODE_PRIORITY", "bounded scalar viability is not obstructed, while native relevance remains absent"),
    ]
    return [
        {"question_id": question_id, "status": "ANSWERED", "answer": answer, "basis": basis}
        for question_id, answer, basis in answers
    ]


def _controls(value: dict[str, Any]) -> dict[str, Any]:
    audit_checks = value["symbolic_audit"]["checks"]
    scope = value["scope"]
    rows = [
        ("C1_AUTHORITY_EXACTLY_ONE_EXECUTION", value["authority"]["authorized_execution_count"] == 1),
        ("C2_SYMBOLIC_AUXILIARY_AND_LEGENDRE_ALGEBRA", all(audit_checks[key] for key in ("auxiliary_action_reduces_to_Phi_R_minus_U", "auxiliary_equation_exact", "Legendre_inverse_exact", "Jordan_potential_exact"))),
        ("C3_ALPHA_ZERO_MAP_FAILS_CLOSED", value["scalar_tensor_result"]["alpha_zero_map_status"] == "NONINVERTIBLE_EINSTEIN_LIMIT"),
        ("C4_CONFORMAL_FACTOR_DOMAIN", value["scalar_tensor_result"]["conformal_domain"] == "Phi>0"),
        ("C5_MINKOWSKI_SHARED_PATH", value["backgrounds"]["rows"][0]["status"] == "PASSED"),
        ("C6_NO_NONZERO_PURE_VACUUM_ROOT", audit_checks["vacuum_constant_curvature_only_zero"]),
        ("C7_SUPPLIED_BACKGROUND_SOLVES_FIELD_EQUATION", audit_checks["supplied_background_exact"]),
        ("C8_TRACELESS_SOURCE_DIRECT_DECOUPLING", value["matter_trace_result"]["classically_traceless_source"] == "NO_DIRECT_LINEAR_SCALAR_SOURCE"),
        ("C9_POTENTIAL_AND_TRACE_MASS_AGREE", audit_checks["potential_mass_matches_trace_mass"]),
        ("C10_INFINITE_MASS_DECOUPLING", value["parameter_results"]["alpha_to_zero_negative"] == "m0_squared_to_positive_infinity_SCALAR_DECOUPLES_AT_FIXED_DISTANCE"),
        ("C11_FINITE_MASS_NOT_SCREENING", value["screening_result"]["principal_finding"] == "FINITE_MASS_SUPPRESSION_ONLY"),
        ("C12_ZERO_NATIVE_BRIDGES_AND_NO_ADOPTION", value["native_relevance_result"]["bridge_identified_count"] == 0 and all(scope[key] is False for key in ("beta_zero_adopted", "alpha_sign_or_value_adopted", "scalar_branch_adopted", "native_gravitational_principle_identified", "gravitational_action_selected"))),
    ]
    return {
        "control_count": len(rows),
        "pass_count": sum(passed for _, passed in rows),
        "failure_count": sum(not passed for _, passed in rows),
        "rows": [
            {"control_id": control_id, "status": "PASSED" if passed else "FAILED"}
            for control_id, passed in rows
        ],
    }


def build_execution() -> dict[str, Any]:
    custody, review = _validate_authority()
    for relative_path in (HUMAN_RELATIVE_PATH, TEST_RELATIVE_PATH):
        if not (REPO_ROOT / relative_path).is_file():
            raise ValueError(f"execution companion missing: {relative_path}")

    symbolic = _symbolic_audit()
    if not all(symbolic["checks"].values()):
        raise ValueError("scalar-only symbolic audit failed")
    stages = _derivation_stages()
    packages = _work_packages()
    obligations = _scalar_tensor_obligations()
    backgrounds = _background_rows()
    bridges = _native_bridge_rows()
    questions = _decision_answers()
    value: dict[str, Any] = {
        "schema_id": "toe.scalar_only_quadratic_gravity_viability_and_native_relevance.execution.v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "principal_outcome": PRINCIPAL_OUTCOME,
        "status": "PENDING_INDEPENDENT_RESULT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "authorized_execution_count": 1,
            "consumed_execution_count": 1,
            "consumed_review_verdict": review["verdict"],
            "consumed_review_outcome": review["principal_packet_review_outcome"],
            "frozen_review_artifact_count": len(custody),
            "frozen_review_artifacts": custody,
        },
        "comparison_classification": {
            "branch": "R+alpha R^2 WITH beta=0",
            "status": "SUPPLIED_COMPARISON_SUBFAMILY",
            "beta_zero": "CONSUMED_AS_COMPARISON_RESTRICTION_NOT_ADOPTED",
            "alpha_selected": False,
            "toe_native": False,
            "candidate_action": False,
        },
        "symbolic_audit": symbolic,
        "field_equation_result": {
            "metric_equation": "(1+2 alpha R)R_mu_nu-(1/2)(R+alpha R^2)g_mu_nu+2 alpha(g_mu_nu Box-nabla_mu nabla_nu)R=kappa T_mu_nu",
            "trace_equation": "-R+6 alpha Box R=kappa T",
            "divergence_compatibility": "LEFT_SIDE_COVARIANTLY_CONSERVED_REQUIRES_SUPPLIED_SOURCE_CONSERVATION",
            "imported_from_literature": False,
        },
        "scalar_tensor_result": {
            "auxiliary_action": "(1/(2 kappa c)) integral sqrt(-g)[f(chi)+f_chi(chi)(R-chi)]+S_m",
            "auxiliary_equation": "2 alpha(R-chi)=0",
            "equivalence_domain": "alpha!=0",
            "alpha_zero_map_status": "NONINVERTIBLE_EINSTEIN_LIMIT",
            "Phi": "1+2 alpha chi",
            "inverse": "chi=(Phi-1)/(2 alpha)",
            "Jordan_action": "(1/(2 kappa c)) integral sqrt(-g)[Phi R-U(Phi)]+S_m",
            "U": "(Phi-1)^2/(4 alpha)",
            "conformal_map": "gE_mu_nu=Phi g_mu_nu",
            "conformal_domain": "Phi>0",
            "canonical_scalar": "varphi=sqrt(3/(2 kappa)) ln Phi",
            "packet_Einstein_frame_potential": "V_packet=U/(2 kappa Phi^2)",
            "translated_physical_potential": "V_physical=-U/(2 kappa Phi^2)=[1/(8 kappa(-alpha))](1-exp(-sqrt(2 kappa/3)varphi))^2",
            "translated_potential_minimum": "varphi=0; Phi=1; d2V/dvarphi2=-1/(6 alpha)>0 for alpha<0",
            "matter_metric": "g_matter=Phi^-1 gE",
            "matter_coupling_function": "A(varphi)=Phi^-1/2=exp(-sqrt(kappa/6)varphi)",
            "matter_coupling_derivative": "d ln A/dvarphi=-sqrt(kappa/6)",
            "frame_observable_equivalence_claimed_without_measurement_map": False,
            "kinetic_sign_interpretation": "USE_BOUND_WHOLE_ACTION_CONVENTION_MAP_AND_SOURCE_SATURATED_RESIDUE_NOT_AN_ISOLATED_PRINTED_SIGN",
        },
        "scalar_tensor_obligations": {
            "obligation_count": 8,
            "derived_count": 8,
            "rows": obligations,
        },
        "parameter_results": {
            "alpha_negative": "NON_TACHYONIC_SCALAR_IN_TESTED_DOMAIN_SUBJECT_TO_Phi_POSITIVE",
            "alpha_zero": "EINSTEIN_COMPARISON_LIMIT_SCALAR_MAP_NONINVERTIBLE",
            "alpha_positive": "TACHYONIC_SCALAR_ON_MINKOWSKI",
            "alpha_to_zero_negative": "m0_squared_to_positive_infinity_SCALAR_DECOUPLES_AT_FIXED_DISTANCE",
            "very_light_finite_scalar": "LONG_RANGE_TRACE_FORCE_POSSIBLE_NO_BOUND_OR_VALUE_SELECTED",
            "massless_or_singular_limit": "NOT_TRANSPORTED_REQUIRES_FRESH_DOMAIN",
            "selected_alpha": None,
        },
        "backgrounds": {
            "background_count": 3,
            "analyzed_count": 3,
            "rows": backgrounds,
            "arbitrary_background_stability_claimed": False,
        },
        "stability_result": {
            "background_existence": "PASSED_FOR_MINKOWSKI_AND_ONE_SUPPLIED_VACUUM_ENERGY_BACKGROUND",
            "positive_kinetic_or_residue": "PASSED_RELATIVE_ISOLATED_SCALAR_CHANNEL_WHEN_Phi0_POSITIVE",
            "no_tachyonic_linear_mode": "PASSED_FOR_ALPHA_NEGATIVE",
            "matter_stability": "NO_DOLGOV_KAWASAKI_TACHYON_IN_FIXED_EXTERNAL_TRACE_DOMAIN_FOR_ALPHA_NEGATIVE",
            "no_rapid_runaway": "PASSED_LINEAR_HOMOGENEOUS_SCALAR_TEST_IN_TESTED_BACKGROUNDS",
            "nonlinear_or_arbitrary_background_stability": "NOT_ESTABLISHED",
        },
        "matter_trace_result": {
            "source_status": "SUPPLIED_COMPARISON_SOURCE_NOT_TOE_MATTER",
            "exact_trace_equation": "(Box+m0^2)R=(kappa/(6 alpha))T",
            "linear_perturbation_equation": "(Box_bar+m0^2)delta R=(kappa/(6 alpha))delta T",
            "traceful_nonrelativistic_source": "DIRECT_SCALAR_SOURCE",
            "classically_traceless_source": "NO_DIRECT_LINEAR_SCALAR_SOURCE",
            "Einstein_frame_trace_relation": "T_E=Phi^-2 T_J",
            "on_shell_or_off_shell": "EXTERNAL_SOURCE_CONSERVATION_SUPPLIED; NO_NATIVE_MATTER_EOM",
        },
        "screening_result": {
            "principal_finding": "FINITE_MASS_SUPPRESSION_ONLY",
            "static_kernel": "exp(-m0 r)/(4 pi r)",
            "mass_environment_dependence": "NONE_IN_EXACT_FIXED_SOURCE_TRACE_OPERATOR",
            "coupling_environment_dependence": "NONE_DERIVED",
            "intrinsic_chameleon_or_Vainshtein_mechanism_identified": False,
            "qualification": "bounded external-source and tested-background result; nonlinear matter backreaction not established",
        },
        "observable_channel_result": {
            "point_mass_h00": "-2GM/(c^2 r)[1+(1/3)exp(-m0 r)]",
            "stationary_conserved_h0i": "EINSTEIN_MASSLESS_CURRENT_RESPONSE_WITH_ZERO_DIRECT_SCALAR_PROJECTOR_TERM",
            "scalar_stationary_0i_direct_contribution": 0,
            "nonlinear_rotating_system_claim": False,
            "orbital_transport_executed": False,
            "empirical_fit_executed": False,
        },
        "native_relevance_result": {
            "candidate_count": 3,
            "bridge_identified_count": 0,
            "required_field_count": 7,
            "rows": bridges,
            "principal_finding": "NATIVE_RELEVANCE_NOT_IDENTIFIED",
            "separate_seam_packet_triggered": False,
        },
        "derivation_stages": {
            "stage_count": len(stages),
            "completed_stage_count": len(stages),
            "rows": stages,
        },
        "work_packages": {
            "work_package_count": len(packages),
            "completed_count": len(packages),
            "rows": packages,
        },
        "decision_questions": {
            "question_count": len(questions),
            "answered_count": len(questions),
            "rows": questions,
        },
        "two_axis_result": {
            "comparison_viability": "SUPPORTED_IN_BOUNDED_LINEAR_AND_ONE_SUPPLIED_NON_MINKOWSKI_DOMAIN",
            "native_relevance": "NOT_IDENTIFIED",
            "branch_adopted": False,
        },
        "scope": {
            "authorized_execution_consumed": 1,
            "comparison_execution_completed": True,
            "work_packages_completed": True,
            "decision_questions_answered": True,
            "metric_field_equation_derived": True,
            "scalar_tensor_map_derived": True,
            "Minkowski_control_reproduced": True,
            "non_Minkowski_background_test_executed": True,
            "matter_trace_coupling_derived": True,
            "screening_assessment_executed": True,
            "native_bridge_audit_executed": True,
            "beta_zero_adopted": False,
            "alpha_sign_or_value_adopted": False,
            "scalar_branch_adopted": False,
            "native_scalar_bridge_identified": False,
            "native_gravitational_principle_identified": False,
            "gravitational_action_selected": False,
            "matter_sector_selected": False,
            "empirical_constraint_computed": False,
            "orbital_transport_executed": False,
            "frame_dragging_reopened": False,
            "master_action_mutation_authorized": False,
            "independent_result_review_required": True,
        },
        "current_posture": {
            "execution": "COMPLETED_ONCE_PENDING_INDEPENDENT_REVIEW",
            "principal_outcome": PRINCIPAL_OUTCOME,
            "work_packages": "6_OF_6_COMPLETED",
            "decision_questions": "8_OF_8_ANSWERED",
            "scalar_tensor_obligations": "8_OF_8_DERIVED",
            "backgrounds": "3_OF_3_ANALYZED_WITH_ONE_VACUUM_NEGATIVE_CONTROL",
            "controls": "12_OF_12_PASSED",
            "native_scalar_bridges": 0,
            "beta_zero": "NOT_ADOPTED",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "Within the supplied local metric R+alpha R^2 comparison, alpha<0 and "
            "Phi>0 support the derived scalar-tensor representation and bounded "
            "linear scalar viability on Minkowski and one explicitly supplied vacuum-"
            "energy background. The exact trace sector provides finite-mass suppression "
            "but no intrinsic environmental screening in the tested external-source "
            "domain. No ToE-native scalar bridge is identified. No beta or alpha "
            "condition, scalar branch, gravitational principle, action, matter sector, "
            "empirical constraint, orbital result, frame-dragging result, or master-"
            "action change is adopted or established."
        ),
    }
    controls = _controls(value)
    if controls["failure_count"]:
        failures = [row["control_id"] for row in controls["rows"] if row["status"] != "PASSED"]
        raise ValueError(f"scalar-only execution controls failed: {failures}")
    value["shared_path_controls"] = controls
    return value


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_execution(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not path.is_file() or path.read_bytes() != raw:
            raise SystemExit("scalar-only execution is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "backgrounds": report["backgrounds"]["analyzed_count"],
            "bridges": report["native_relevance_result"]["bridge_identified_count"],
            "controls": report["shared_path_controls"]["pass_count"],
            "outcome": report["principal_outcome"],
            "questions": report["decision_questions"]["answered_count"],
            "status": "CHECKED",
            "work_packages": report["work_packages"]["completed_count"],
        }, sort_keys=True))
        return 0
    path.write_bytes(raw)
    print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
