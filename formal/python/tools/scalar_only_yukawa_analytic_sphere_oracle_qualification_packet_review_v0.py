from __future__ import annotations

import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_PACKET_20260719_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_PACKET_REVIEW_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_PACKET_REVIEW_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_oracle_"
    "qualification_packet_review_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaAnalyticSphereOracleQualificationPacketReviewV0.lean"
)

TARGET = "review_scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_v0_result"
VERDICT = "ANALYTIC_SPHERE_ORACLE_QUALIFICATION_CONTRACT_READY"
SELECTED_NEXT_TARGET = "execute_scalar_only_yukawa_analytic_sphere_oracle_qualification_v0_once"
SELECTED_NEXT_TARGET_KIND = (
    "ONE_SMALL_ANALYTIC_ORACLE_QUALIFICATION_EXECUTION_ONLY_NO_PRODUCTION_COMPARISON"
)

PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_PACKET_20260719_v0.md":
        "6450af7a7aa314ee86802a63fef19da20d738905e28f4463bd2523d0457745f2",
    PACKET_RELATIVE_PATH:
        "8e2e93963182a27b1618c0fe1d02aa34eb8740f4a422429a041f2bcc02323bb5",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_v0.py":
        "38a2f5e856cfa97f805877a01efe8801da336ffae6e44e3e8c279d19aeb6941e",
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_v0.py":
        "1b601b0f76eeffbe592bc77178d34f2c6648f48a6bd03b5567a30e8ef05a1f49",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaAnalyticSphereOracleQualificationPacketV0.lean":
        "70f46a6d1053249bced8d4c8a9cb836edcb79022bedfd2f1d1d596c1e803ab36",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _domain_reproduction(packet: dict[str, Any]) -> dict[str, Any]:
    rows = []
    for row in packet["representative_domain"]["rows"]:
        r1 = float(row["radius_1_m"])
        r2 = float(row["radius_2_m"])
        gap = float(row["surface_gap_m"])
        distance = float(row["center_distance_m"])
        lam = float(row["lambda_m"])
        roles = list(row["roles"])
        rows.append({
            "case_id": row["case_id"],
            "D_gt_R1_plus_R2": distance > r1 + r2,
            "reported_gap_positive": gap > 0.0,
            "reconstructed_gap_m": distance - r1 - r2,
            "gap_reconstruction_absolute_error_m": abs((distance - r1 - r2) - gap),
            "R1_over_lambda": round(r1 / lam, 12),
            "R2_over_lambda": round(r2 / lam, 12),
            "g_over_lambda": round(gap / lam, 12),
            "g_over_min_radius": round(gap / min(r1, r2), 12),
            "roles": roles,
        })
    all_roles = {role for row in rows for role in row["roles"]}
    required_roles = {
        "SMALL_X", "X_NEAR_ONE", "LARGE_X", "X_MAX_1000", "EQUAL_RADII",
        "UNEQUAL_RADII", "WIDE_SEPARATION", "SMALL_POSITIVE_GAP",
    }
    return {
        "case_count": len(rows),
        "all_strictly_nonoverlapping": all(
            row["D_gt_R1_plus_R2"] and row["reported_gap_positive"] for row in rows
        ),
        "maximum_gap_reconstruction_absolute_error_m": max(
            row["gap_reconstruction_absolute_error_m"] for row in rows
        ),
        "minimum_gap_over_min_radius": min(row["g_over_min_radius"] for row in rows),
        "maximum_gap_over_min_radius": max(row["g_over_min_radius"] for row in rows),
        "minimum_x": min(min(row["R1_over_lambda"], row["R2_over_lambda"]) for row in rows),
        "maximum_x": max(max(row["R1_over_lambda"], row["R2_over_lambda"]) for row in rows),
        "failed_stage_a_case_count": sum(
            "FAILED_STAGE_A_CONFIGURATION" in row["roles"] for row in rows
        ),
        "required_roles": sorted(required_roles),
        "observed_roles": sorted(all_roles),
        "role_coverage_complete": required_roles <= all_roles,
        "claim_domain": "EIGHT_FROZEN_CASES_PLUS_TWO_FROZEN_OVERLAP_GRIDS_ONLY",
        "continuous_domain_numerical_qualification_claimed": False,
        "rows": rows,
    }


def _formula_reproduction(packet: dict[str, Any]) -> dict[str, Any]:
    derivation = packet["derivation_contract"]
    evaluator = packet["stable_evaluator_contract"]
    expected_series = [
        Fraction(6 * (k + 1), math.factorial(2 * k + 3)) for k in range(5)
    ]
    frozen_series = [
        Fraction(1, 1), Fraction(1, 10), Fraction(1, 280),
        Fraction(1, 15120), Fraction(1, 1330560),
    ]
    overlaps = evaluator["overlap_checks"]
    return {
        "newtonian": {
            "mass_formula": packet["physical_conventions"]["mass_formula"],
            "energy_formula": derivation["newtonian_oracle"],
            "strict_nonoverlap_domain": derivation["domain"],
            "unit_reduction": "(m^3 kg^-1 s^-2)*kg^2/m = kg m^2 s^-2 = J",
            "passed": (
                derivation["newtonian_oracle"] == "U_N(D)=-G*M1*M2/D"
                and derivation["domain"] == "STRICTLY_NONOVERLAPPING_HOMOGENEOUS_SPHERES"
            ),
        },
        "yukawa": {
            "amplitude_exact": packet["physical_conventions"]["yukawa_amplitude_exact"],
            "form_factor": derivation["sphere_form_factor"],
            "pair_energy": derivation["yukawa_oracle"],
            "both_form_factors": "F(x1)*F(x2)" in derivation["yukawa_oracle"],
            "center_distance_exponential": "exp(-D/lambda)" in derivation["yukawa_oracle"],
            "point_limit_obligation": "VERIFY_POINT_PARTICLE_LIMIT_F_TO_ONE" in derivation["obligations"],
            "sphere_exchange_symmetry_obligation": (
                "VERIFY_SPHERE_EXCHANGE_SYMMETRY_UNITS_AND_SIGN" in derivation["obligations"]
            ),
            "passed": (
                packet["physical_conventions"]["yukawa_amplitude_exact"] == "1/3"
                and derivation["sphere_form_factor"] == "F(x)=3*(x*cosh(x)-sinh(x))/x^3"
                and "F(x1)*F(x2)" in derivation["yukawa_oracle"]
                and "exp(-D/lambda)" in derivation["yukawa_oracle"]
            ),
        },
        "small_x": {
            "coefficient_formula": "a_k=6*(k+1)/(2*k+3)! for k=0..4",
            "independently_reproduced_coefficients": [str(value) for value in expected_series],
            "frozen_coefficients": [str(value) for value in frozen_series],
            "coefficients_match": expected_series == frozen_series,
            "primary_domain": evaluator["small_x"]["primary_domain"],
            "fixed_highest_power": evaluator["small_x"]["fixed_highest_power"],
        },
        "moderate_x": {
            "primary_domain": evaluator["moderate_x"]["primary_domain"],
            "binary64_finite_required": evaluator["moderate_x"]["binary64_finite_required"],
        },
        "large_x": {
            "primary_domain": evaluator["large_x"]["primary_domain"],
            "formula": evaluator["large_x"]["formula"],
            "direct_hyperbolic_forbidden": evaluator["large_x"]["direct_sinh_or_cosh_forbidden"],
            "scaled_identity": evaluator["stable_pair_factor"],
            "log_domain_required": evaluator["log_domain_energy_required"],
            "silent_overflow_or_underflow_forbidden": evaluator["silent_overflow_or_underflow_forbidden"],
            "passed": (
                "exp(-2*x)" in evaluator["large_x"]["formula"]
                and "exp(-g/lambda)*H(x1)*H(x2)" in evaluator["stable_pair_factor"]
                and evaluator["large_x"]["direct_sinh_or_cosh_forbidden"] is True
                and evaluator["log_domain_energy_required"] is True
            ),
        },
        "overlaps": {
            "grid_count": len(overlaps),
            "small_direct_x": overlaps[0]["x_values"],
            "direct_scaled_x": overlaps[1]["x_values"],
            "absolute_and_relative_tolerances_present": all(
                row["absolute_tolerance_H"] > 0.0 and row["relative_tolerance_H"] > 0.0
                for row in overlaps
            ),
            "post_result_boundary_change_forbidden": (
                evaluator["post_result_regime_boundary_change"] == "FORBIDDEN"
            ),
        },
    }


def _cross_check_reproduction(packet: dict[str, Any]) -> dict[str, Any]:
    cross = packet["independent_cross_check_contract"]
    return {
        "path_id": cross["path_id"],
        "path_count": cross["path_count"],
        "dimension": cross["dimension"],
        "scaled_integral": cross["scaled_integral"],
        "density_kernel_reduction": (
            "H=exp(-x)*3/x^3*integral_0^x(t*sinh(t),dt), followed by t=x*u; "
            "the expm1 integrand is the stable radial density moment, not the closed-form antiderivative"
        ),
        "precision_ladder": cross["decimal_precision_ladder"],
        "plateau_levels": cross["plateau_levels"],
        "analytic_form_factor_call_forbidden": cross["analytic_form_factor_call_forbidden"],
        "closed_form_scaled_factor_call_forbidden": cross["closed_form_scaled_factor_call_forbidden"],
        "production_import_forbidden": cross["production_kernel_or_cubature_import_forbidden"],
        "self_convergence_rule": cross["self_convergence"]["rule"],
        "agreement_rule": cross["cross_agreement"]["rule"],
        "numerically_independent_of_closed_form_evaluator": (
            cross["path_count"] == 1
            and cross["dimension"] == 1
            and "expm1" in cross["scaled_integral"]
            and cross["analytic_form_factor_call_forbidden"] is True
            and cross["closed_form_scaled_factor_call_forbidden"] is True
            and cross["production_kernel_or_cubature_import_forbidden"] is True
        ),
        "independence_qualification": (
            "The radial path is independent at the numerical implementation level after "
            "analytic angular reduction. It does not independently prove the two-sphere "
            "factorization; the derivation gate must pass before numerical agreement can "
            "qualify the oracle."
        ),
        "pair_factorization_may_be_accepted_from_cross_check_alone": False,
        "derivation_gate_must_pass_first": True,
    }


def _execution_contract_reproduction(packet: dict[str, Any]) -> dict[str, Any]:
    custody = packet["resource_and_custody_contract"]
    mutations = packet["mutation_controls"]
    output = packet["execution_output_contract"]
    review = packet["packet_review_contract"]
    return {
        "scientific_stage_records": [
            {"record": "ANALYTIC_DERIVATION", "values": ["PASS", "FAIL"]},
            {"record": "STABLE_EVALUATOR", "values": ["PASS", "FAIL", "NOT_EVALUATED"]},
            {"record": "RADIAL_SELF_CONVERGENCE", "values": ["PASS", "FAIL", "TIMEOUT"]},
            {"record": "ANALYTIC_RADIAL_AGREEMENT", "values": ["PASS", "FAIL", "NOT_EVALUATED"]},
        ],
        "nonconverged_radial_value_may_confirm_or_reject_formula": False,
        "mutation_count": mutations["mutation_count"],
        "mutation_ids": [row["mutation_id"] for row in mutations["rows"]],
        "live_path_required": mutations["same_live_oracle_evaluator_and_adjudicator_required"],
        "metadata_only_rejection_forbidden": mutations["metadata_only_rejection_forbidden"],
        "resource_envelope": {
            "total_seconds": custody["total_wall_clock_seconds_max"],
            "memory_mib": custody["memory_mib_max"],
            "stage_seconds_sum": sum(row["wall_clock_seconds_max"] for row in custody["stage_rows"]),
            "stage_count": len(custody["stage_rows"]),
        },
        "custody": {
            "process_group_termination": custody["process_group_termination"],
            "raw_launcher_transcript": custody["raw_launcher_transcript"],
            "timeout_timestamp": custody["timeout_initiation_timestamp"],
            "child_termination_records": custody["child_process_tree_and_termination_timestamps"],
            "zero_survivors": custody["zero_surviving_process_check"],
            "stage_atomic": custody["stage_level_atomic_status"],
            "all_stages_required": custody["packet_wide_qualified_outcome_requires_all_stages_complete"],
        },
        "terminal_outcomes": output["terminal_outcomes"],
        "only_success_eligibility": output["only_success_eligibility"],
        "forbidden_outputs": output["forbidden_outputs"],
        "authorized_execution_count": review["authorized_execution_count"],
        "executions_consumed": review["executions_consumed"],
        "post_execution_review_required": review["post_execution_independent_result_review_required"],
        "fresh_selector_required": review["post_result_fresh_scientific_response_selector_required"],
    }


def build_report() -> dict[str, Any]:
    frozen = []
    for relative_path, expected in PACKET_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"analytic-oracle packet custody drift: {relative_path}")
        frozen.append({"relative_path": relative_path, "sha256": observed})
    packet = _load_json(PACKET_RELATIVE_PATH)
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("packet did not rotate to this independent review")
    if packet.get("status") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("packet is not pending independent review")
    if packet.get("preparation_gates", {}).get("pass_count") != 42:
        raise ValueError("packet preparation gates are incomplete")
    if packet.get("scope", {}).get("oracle_qualification_executed") is not False:
        raise ValueError("packet preparation unexpectedly executed the oracle")

    domain = _domain_reproduction(packet)
    formula = _formula_reproduction(packet)
    cross = _cross_check_reproduction(packet)
    execution = _execution_contract_reproduction(packet)
    gates = [
        ("R01_EXACT_PACKET_CUSTODY_AND_TARGET", True, "five packet surfaces hash-verified"),
        ("R02_PENDING_REVIEW_AND_ZERO_EXECUTION", packet["scope"]["oracle_qualification_executed"] is False, "no oracle, radial integral, or mutation executed"),
        ("R03_EXACT_EIGHT_CASE_GRID", domain["case_count"] == 8, "bounded six-to-nine requirement satisfied"),
        ("R04_ALL_CASES_STRICTLY_NONOVERLAPPING", domain["all_strictly_nonoverlapping"], "D>R1+R2 and g>0 independently reproduced"),
        ("R05_CENTER_DISTANCE_GAP_SEMANTICS", domain["maximum_gap_reconstruction_absolute_error_m"] <= 2e-17, "D=R1+R2+g reproduced"),
        ("R06_DIMENSIONLESS_ROLE_COVERAGE", domain["role_coverage_complete"], "small, transition, large, equal, unequal, wide, and small-gap roles present"),
        ("R07_ALL_THREE_FAILED_STAGE_A_CASES", domain["failed_stage_a_case_count"] == 3, "legacy configurations retained"),
        ("R08_REQUIRED_X_1000_ENDPOINT", math.isclose(domain["maximum_x"], 1000.0), "large-x endpoint reproduced"),
        ("R09_NUMERICAL_CLAIM_LIMITED_TO_FROZEN_PROBES", not domain["continuous_domain_numerical_qualification_claimed"], domain["claim_domain"]),
        ("R10_NEWTONIAN_FORMULA_MASS_AND_DOMAIN", formula["newtonian"]["passed"], "shell-theorem energy and nonoverlap domain complete"),
        ("R11_NEWTONIAN_UNITS_AND_ATTRACTIVE_SIGN", packet["physical_conventions"]["newtonian_sign"] == "NEGATIVE_ATTRACTIVE", formula["newtonian"]["unit_reduction"]),
        ("R12_YUKAWA_FORM_FACTOR_AND_PAIR_FORMULA", formula["yukawa"]["passed"], "convention-specific formula exact"),
        ("R13_A_Y_TWO_FACTORS_AND_CENTER_EXPONENT", formula["yukawa"]["amplitude_exact"] == "1/3" and formula["yukawa"]["both_form_factors"] and formula["yukawa"]["center_distance_exponential"], "A_Y=1/3, F1*F2, exp(-D/lambda)"),
        ("R14_POINT_LIMIT_SYMMETRY_UNITS_AND_SIGN_OBLIGATIONS", formula["yukawa"]["point_limit_obligation"] and formula["yukawa"]["sphere_exchange_symmetry_obligation"], "decision-bearing derivation gates explicit"),
        ("R15_SMALL_X_SERIES_COEFFICIENTS_REPRODUCED", formula["small_x"]["coefficients_match"], "series through x^8 independently reconstructed"),
        ("R16_SMALL_X_TRUNCATION_AND_BOUNDARY", formula["small_x"]["fixed_highest_power"] == 8 and formula["small_x"]["primary_domain"] == "0<x<=0.1", "fixed series order and primary boundary"),
        ("R17_MODERATE_X_DIRECT_DOMAIN", formula["moderate_x"]["primary_domain"] == "0.1<x<=40" and formula["moderate_x"]["binary64_finite_required"], "finite direct central regime"),
        ("R18_LARGE_X_SCALED_DOMAIN", formula["large_x"]["passed"], "no direct hyperbolic evaluation through x=1000"),
        ("R19_SURFACE_GAP_SCALED_PAIR_IDENTITY", "exp(-g/lambda)*H(x1)*H(x2)" in formula["large_x"]["scaled_identity"], "center exponential cancellation performed analytically"),
        ("R20_LOG_DOMAIN_AND_UNDERFLOW_BEHAVIOR", formula["large_x"]["log_domain_required"] and formula["large_x"]["silent_overflow_or_underflow_forbidden"], "no silent zero or infinity"),
        ("R21_BOTH_REGIME_OVERLAPS_QUANTITATIVE", formula["overlaps"]["grid_count"] == 2 and formula["overlaps"]["absolute_and_relative_tolerances_present"] and formula["overlaps"]["post_result_boundary_change_forbidden"], "two frozen overlap grids"),
        ("R22_RADIAL_DENSITY_MOMENT_IDENTITY", "integral_0^1" in cross["scaled_integral"] and "expm1" in cross["scaled_integral"], "stable one-dimensional density moment"),
        ("R23_CROSS_CHECK_IMPLEMENTATION_INDEPENDENCE", cross["numerically_independent_of_closed_form_evaluator"], "closed form and production imports forbidden"),
        ("R24_CROSS_CHECK_INDEPENDENCE_CLAIM_QUALIFIED", cross["derivation_gate_must_pass_first"] and not cross["pair_factorization_may_be_accepted_from_cross_check_alone"], cross["independence_qualification"]),
        ("R25_PRECISION_LADDER_EXACT", cross["precision_ladder"] == [50, 80, 120] and cross["plateau_levels"] == [80, 120], "three precision levels and final-two plateau"),
        ("R26_RADIAL_SELF_CONVERGENCE_BEFORE_USE", "1e-30" in cross["self_convergence_rule"] and not execution["nonconverged_radial_value_may_confirm_or_reject_formula"], "nonconverged values remain non-decision-bearing"),
        ("R27_ANALYTIC_RADIAL_AGREEMENT_RULE", "abs_tol+rel_tol" in cross["agreement_rule"], "absolute-plus-relative envelope frozen"),
        ("R28_FOUR_SCIENTIFIC_STAGE_RECORDS_SEPARATE", len(execution["scientific_stage_records"]) == 4, "derivation, evaluator, self-convergence, and agreement adjudicated separately"),
        ("R29_EXACT_EIGHT_MUTATIONS", execution["mutation_count"] == len(execution["mutation_ids"]) == 8, "geometry, normalization, kernel, overflow, and cancellation mutations"),
        ("R30_MUTATIONS_USE_LIVE_PATH", execution["live_path_required"] and execution["metadata_only_rejection_forbidden"], "metadata-only rejection prohibited"),
        ("R31_RESOURCE_ENVELOPE_EXACT", execution["resource_envelope"]["total_seconds"] == 600 and execution["resource_envelope"]["memory_mib"] == 2048, "600 seconds and 2048 MiB"),
        ("R32_STAGE_CAPS_SUM_TO_TOTAL", execution["resource_envelope"]["stage_count"] == 6 and execution["resource_envelope"]["stage_seconds_sum"] == 600, "all stage budgets frozen"),
        ("R33_PROCESS_GROUP_TERMINATION_MANDATORY", execution["custody"]["process_group_termination"] == "MANDATORY", "orphan prevention explicit"),
        ("R34_RAW_LOG_TIMEOUT_CHILD_AND_ZERO_SURVIVOR_RECORDS", all(execution["custody"][key] in {"PRESERVED", "MANDATORY"} for key in ("raw_launcher_transcript", "timeout_timestamp", "child_termination_records", "zero_survivors")), "complete launcher custody"),
        ("R35_STAGE_ATOMIC_AND_ALL_STAGES_REQUIRED", execution["custody"]["stage_atomic"] == "REQUIRED" and execution["custody"]["all_stages_required"], "partial stages cannot qualify the packet"),
        ("R36_EXACT_FIVE_TERMINAL_OUTCOMES", len(execution["terminal_outcomes"]) == 5, "frozen vocabulary complete"),
        ("R37_ONLY_QUALIFIED_OUTCOME_CREATES_ELIGIBILITY", execution["only_success_eligibility"].startswith("Only ANALYTIC_SPHERE_ORACLE_QUALIFIED"), "eligibility is not automatic execution authority"),
        ("R38_EXACTLY_ONE_SMALL_EXECUTION_AUTHORIZED", execution["authorized_execution_count"] == 1 and execution["executions_consumed"] == 0, "one future oracle run only"),
        ("R39_PRODUCTION_TORQUE_INFERENCE_AND_STAGE_B_FIREWALLS", len(execution["forbidden_outputs"]) == 9 and packet["scope"]["stage_b_authorized"] is False, "no production judgment or downstream science"),
        ("R40_POST_EXECUTION_REVIEW_AND_FRESH_SELECTOR_REQUIRED", execution["post_execution_review_required"] and execution["fresh_selector_required"], "future result cannot self-authorize its remedy"),
    ]
    gate_rows = [
        {"gate_id": gate_id, "status": "PASS" if passed else "FAIL", "detail": detail}
        for gate_id, passed, detail in gates
    ]
    failures = [row["gate_id"] for row in gate_rows if row["status"] != "PASS"]
    if failures:
        raise ValueError(f"independent analytic-oracle packet review failed: {failures}")

    scope = {
        "independent_packet_review_executed": True,
        "packet_custody_verified": True,
        "analytic_oracle_qualification_contract_ready": True,
        "one_small_oracle_execution_authorized": True,
        "oracle_execution_performed": False,
        "interaction_value_computed_during_review": False,
        "radial_integral_evaluated_during_review": False,
        "mutation_executed_during_review": False,
        "oracle_qualification_status_issued_during_review": False,
        "production_cubature_called_during_review": False,
        "production_comparison_authorized": False,
        "production_method_replacement_authorized": False,
        "diagnosis_rerun_authorized": False,
        "stage_a_rerun_authorized": False,
        "automatic_v2_authorized": False,
        "torque_authorized": False,
        "angular_dft_authorized": False,
        "final_real_150_vector_authorized": False,
        "jacobian_or_svd_authorized": False,
        "identifiability_authorized": False,
        "stage_b_eligible": False,
        "stage_b_authorized": False,
    }
    return {
        "schema_id": "toe.scalar_only_yukawa.analytic_sphere_oracle.qualification_packet_review.v0",
        "review_id": "SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_PACKET_REVIEW_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "status": "INDEPENDENT_PACKET_REVIEW_COMPLETE",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_verdict": packet["verdict"],
            "frozen_packet_artifacts": frozen,
            "human_review": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_analytic_sphere_oracle_"
                "qualification_packet_review_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
            "authorized_oracle_execution_count": 1,
            "performed_oracle_execution_count": 0,
        },
        "independent_domain_reproduction": domain,
        "independent_formula_reproduction": formula,
        "independent_cross_check_reproduction": cross,
        "independent_execution_contract_reproduction": execution,
        "review_qualification": {
            "qualification_id": "RADIAL_NUMERICAL_INDEPENDENCE_AFTER_ANALYTIC_ANGULAR_REDUCTION",
            "accepted": True,
            "text": cross["independence_qualification"],
            "consequence": (
                "The future derivation gate is independently decision-bearing and must pass. "
                "Radial numerical agreement cannot repair or override a failed derivation."
            ),
        },
        "review_gates": {
            "gate_count": len(gate_rows),
            "pass_count": len(gate_rows),
            "failure_count": 0,
            "rows": gate_rows,
        },
        "accepted_contract": {
            "case_count": 8,
            "maximum_x": 1000,
            "evaluator_regime_count": 3,
            "overlap_grid_count": 2,
            "independent_cross_check_path_count": 1,
            "mutation_count": 8,
            "terminal_outcome_count": 5,
            "oracle_execution_authorized": 1,
            "oracle_execution_performed": 0,
            "required_stop": "INDEPENDENT_ANALYTIC_ORACLE_EXECUTION_RESULT_REVIEW",
        },
        "scope": scope,
        "claim_ceiling": (
            "This review accepts one bounded analytic-oracle qualification contract and "
            "authorizes one small execution only. It computes no interaction or radial "
            "integral, qualifies no oracle now, judges or replaces no production method, "
            "and authorizes no torque, DFT, Stage A rerun, identifiability, or Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Independently review the analytic sphere-oracle qualification packet without executing it."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    rendered = artifact_bytes()
    if args.write:
        report_path.write_bytes(rendered)
        print(f"wrote {REPORT_RELATIVE_PATH} verdict={VERDICT}")
        return 0
    if not report_path.exists() or report_path.read_bytes() != rendered:
        print("analytic sphere-oracle packet review artifact missing or stale")
        return 1
    report = json.loads(report_path.read_text(encoding="utf-8"))
    print(
        "analytic sphere-oracle packet review OK "
        f"verdict={VERDICT} gates={report['review_gates']['pass_count']}/"
        f"{report['review_gates']['gate_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
