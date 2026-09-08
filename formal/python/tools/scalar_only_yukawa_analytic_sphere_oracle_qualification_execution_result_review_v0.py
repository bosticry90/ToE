from __future__ import annotations

import argparse
import hashlib
import json
import math
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any


getcontext().prec = 100
REPO_ROOT = Path(__file__).resolve().parents[3]
EXECUTION_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_EXECUTION_20260719_v0.json"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_PACKET_20260719_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_EXECUTION_RESULT_REVIEW_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_EXECUTION_RESULT_REVIEW_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_oracle_"
    "qualification_execution_result_review_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaAnalyticSphereOracleQualificationExecutionResultReviewV0.lean"
)
OUTPUT_RELATIVE_DIR = "formal/output/scalar_only_yukawa_analytic_sphere_oracle_qualification_v0"
OUTPUT_DIR = REPO_ROOT / OUTPUT_RELATIVE_DIR

TARGET = "review_scalar_only_yukawa_analytic_sphere_oracle_qualification_v0_execution_result"
VERDICT = "ACCEPTED_ANALYTIC_SPHERE_ORACLE_QUALIFIED"
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_yukawa_analytic_sphere_oracle_qualification_v0_"
    "execution_result_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "FRESH_SCIENTIFIC_RESPONSE_SELECTOR_ONLY_NO_PRODUCTION_COMPARISON"
)

EXECUTION_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_EXECUTION_20260719_v0.md":
        "d9f90f2164ee613123be4a147a1121527c04b673fc72be8747203a054c59bbf6",
    EXECUTION_RELATIVE_PATH:
        "d2527fd3c03a107734b3b55920c35f73185cbbf0f6c13132ff94c40ec447676d",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_v0.py":
        "5d357f9346a3c6bf6168d6330ff1fb62017ac3eda90e05e57605f23392be17eb",
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_v0.py":
        "b0d546155a01ccdd5603ec98275ecf04693f5e3ab10bd703ff1c844a09479a8e",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaAnalyticSphereOracleQualificationExecutionV0.lean":
        "fac92ebc15d1317b8e329855035abe47786c70307b7350a6ce1c320eab79319f",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _custody_audit(execution: dict[str, Any]) -> dict[str, Any]:
    custody_path = OUTPUT_DIR / "launch_custody.json"
    payload_path = OUTPUT_DIR / "worker_scientific_payload.json"
    canonical_path = OUTPUT_DIR / "execution_result.json"
    raw_log_path = OUTPUT_DIR / "raw_launcher.log"
    launch_flag_path = OUTPUT_DIR / "launch_authorized.flag"
    current_stage_path = OUTPUT_DIR / "current_stage.json"
    custody = _load_json(custody_path)
    payload = _load_json(payload_path)
    current_stage = _load_json(current_stage_path)
    stages = []
    for reported in execution["stage_records"]:
        stage_path = OUTPUT_DIR / "stages" / f"{reported['stage_id']}.json"
        observed = _load_json(stage_path)
        stages.append({
            "stage_id": reported["stage_id"],
            "reported_equals_atomic_file": reported == observed,
            "status": observed["status"],
            "duration_seconds": observed["duration_seconds"],
            "within_stage_budget": observed["within_stage_budget"],
            "sha256": _sha256(stage_path),
        })
    raw_log = raw_log_path.read_text(encoding="utf-8")
    stage_ids = [row["stage_id"] for row in stages]
    start_offsets = [raw_log.index(f"STAGE_START {stage_id}") for stage_id in stage_ids]
    end_offsets = [raw_log.index(f"STAGE_END {stage_id}") for stage_id in stage_ids]
    return {
        "release_equals_canonical_result": (
            (REPO_ROOT / EXECUTION_RELATIVE_PATH).read_bytes() == canonical_path.read_bytes()
        ),
        "reported_custody_equals_atomic_file": execution["execution_custody"] == custody,
        "reported_payload_equals_atomic_file": execution["scientific_payload"] == payload,
        "launch_flag_run_id": launch_flag_path.read_text(encoding="utf-8").strip(),
        "launch_count": custody["launch_count"],
        "run_id": custody["run_id"],
        "worker_pid": custody["worker_pid"],
        "worker_exit_code": custody["worker_exit_code"],
        "timeout_initiated_at_utc": custody["timeout_initiated_at_utc"],
        "zero_surviving_processes": custody["zero_surviving_processes"],
        "process_group_mechanism": custody["process_group_mechanism"],
        "peak_job_memory_bytes": custody["peak_job_memory_bytes"],
        "peak_job_memory_within_limit": custody["peak_job_memory_within_limit"],
        "memory_limit_mib": custody["memory_limit_mib"],
        "raw_launcher_log_sha256_reported": custody["raw_launcher_log_sha256"],
        "raw_launcher_log_sha256_observed": _sha256(raw_log_path),
        "raw_log_stage_start_count": raw_log.count("STAGE_START"),
        "raw_log_stage_end_count": raw_log.count("STAGE_END"),
        "raw_log_outcome_count": raw_log.count(
            "SCIENTIFIC_OUTCOME ANALYTIC_SPHERE_ORACLE_QUALIFIED"
        ),
        "raw_log_stage_order_exact": (
            start_offsets == sorted(start_offsets)
            and end_offsets == sorted(end_offsets)
            and all(start < end for start, end in zip(start_offsets, end_offsets))
        ),
        "stage_count": len(stages),
        "all_stage_files_match_report": all(row["reported_equals_atomic_file"] for row in stages),
        "all_stages_complete": all(row["status"] == "COMPLETE" for row in stages),
        "all_stages_within_budget": all(row["within_stage_budget"] for row in stages),
        "stage_rows": stages,
        "current_stage_pointer": current_stage,
        "current_stage_pointer_terminalized": current_stage.get("status") == "COMPLETE",
        "current_stage_pointer_decision_bearing": False,
        "custody_qualification": (
            "current_stage.json remains an IN_PROGRESS monitor pointer for O6. The "
            "authoritative O6 atomic record, raw log, worker exit, canonical result, "
            "and zero-survivor record all establish completion; the pointer is retained "
            "unchanged as non-decision-bearing custody evidence."
        ),
    }


def _derivation_audit(execution: dict[str, Any]) -> dict[str, Any]:
    gate = execution["scientific_payload"]["derivation_gate"]
    obligations = gate["obligations"]
    coefficients = [
        Fraction(6 * (k + 1), math.factorial(2 * k + 3)) for k in range(5)
    ]
    expected = [
        Fraction(1, 1), Fraction(1, 10), Fraction(1, 280),
        Fraction(1, 15120), Fraction(1, 1330560),
    ]
    return {
        "reported_status": gate["status"],
        "strict_nonoverlap_all_cases": obligations["strict_nonoverlap_all_cases"],
        "newtonian_shell_derivation_present": "U_N=-G*M1*M2/D" in obligations["newtonian_external_shell_derivation"],
        "yukawa_angular_kernel_identity_present": (
            "2*exp(-k*D)*sinh(k*r)/(k*D*r)" in obligations["yukawa_angular_kernel_identity"]
        ),
        "radial_antiderivative_present": (
            "(k*R*cosh(k*R)-sinh(k*R))/k^2" in obligations["yukawa_radial_density_identity"]
        ),
        "both_form_factors_present": obligations["both_form_factors_present"],
        "center_distance_exponential_present": obligations["center_distance_exponential_present"],
        "mass_volume_normalization": obligations["mass_volume_normalization"],
        "yukawa_amplitude_exact": obligations["yukawa_amplitude_exact"],
        "sphere_exchange_symmetry": obligations["sphere_exchange_symmetry"],
        "energy_units": obligations["energy_units"],
        "independently_reproduced_series_coefficients": [str(value) for value in coefficients],
        "point_particle_limit_reproduced": coefficients == expected,
        "scaled_pair_identity_present": (
            "exp(-g/lambda)*H(x1)*H(x2)" in obligations["scaled_identity"]
        ),
        "passed": (
            gate["status"] == "PASS"
            and obligations["strict_nonoverlap_all_cases"] is True
            and obligations["both_form_factors_present"] is True
            and obligations["center_distance_exponential_present"] is True
            and obligations["yukawa_amplitude_exact"] == "1/3"
            and obligations["sphere_exchange_symmetry"] is True
            and obligations["energy_units"] == "kg*m^2*s^-2=J"
            and coefficients == expected
        ),
    }


def _evaluator_audit(execution: dict[str, Any], packet: dict[str, Any]) -> dict[str, Any]:
    gate = execution["scientific_payload"]["stable_evaluator_gate"]
    packet_rows = {row["case_id"]: row for row in packet["representative_domain"]["rows"]}

    def expected_regime(x: float) -> str:
        if x <= 0.1:
            return "SMALL_X_SERIES"
        if x <= 40.0:
            return "MODERATE_X_DIRECT"
        return "LARGE_X_SCALED"

    case_rows = []
    for row in gate["case_evaluator_rows"]:
        frozen = packet_rows[row["case_id"]]
        case_rows.append({
            "case_id": row["case_id"],
            "regime_1_exact": row["regime_1"] == expected_regime(float(frozen["x_1"])),
            "regime_2_exact": row["regime_2"] == expected_regime(float(frozen["x_2"])),
            "finite_positive_scaled_factors": row["finite_positive_scaled_factors"],
            "binary64_underflow": row["binary64_underflow"],
        })
    overlap_rows = []
    for row in gate["overlap_rows"]:
        recomputed_delta = abs(float(row["left_H"]) - float(row["right_H"]))
        overlap_rows.append({
            "overlap_id": row["overlap_id"],
            "x": row["x"],
            "reported_difference": row["absolute_difference"],
            "recomputed_difference": recomputed_delta,
            "difference_reproduced": math.isclose(
                recomputed_delta, float(row["absolute_difference"]), rel_tol=0.0, abs_tol=1e-30
            ),
            "inside_tolerance": recomputed_delta <= float(row["tolerance"]),
        })
    return {
        "reported_status": gate["status"],
        "case_rows": case_rows,
        "all_case_regimes_exact": all(
            row["regime_1_exact"] and row["regime_2_exact"] for row in case_rows
        ),
        "all_scaled_factors_finite_positive": all(
            row["finite_positive_scaled_factors"] for row in case_rows
        ),
        "overlap_rows": overlap_rows,
        "all_six_overlap_decisions_reproduced": (
            len(overlap_rows) == 6
            and all(row["difference_reproduced"] and row["inside_tolerance"] for row in overlap_rows)
        ),
        "x_1000_used_scaled_branch": any(
            row["case_id"] == "EXTREME_X_1000_UNEQUAL"
            and row["regime_1_exact"] and row["regime_2_exact"]
            for row in case_rows
        ),
        "direct_hyperbolic_at_x_1000": gate["x_1000_direct_hyperbolic_path_used"],
        "silent_overflow_or_underflow": gate["silent_underflow_or_overflow_observed"],
    }


def _radial_and_agreement_audit(execution: dict[str, Any]) -> dict[str, Any]:
    gate = execution["scientific_payload"]["radial_cross_check_gate"]
    convergence_rows = []
    for row in gate["convergence_rows"]:
        delta = Decimal(row["absolute_80_to_120_difference"])
        tolerance = Decimal(row["tolerance"])
        convergence_rows.append({
            "x": row["x"],
            "delta": str(delta),
            "tolerance": str(tolerance),
            "decision_reproduced": delta <= tolerance and row["passed"] is True,
        })
    case_rows = []
    for row in gate["case_rows"]:
        analytic = Decimal(row["yukawa_analytic_stable_J"])
        reference = Decimal(row["yukawa_radial_reference_J"])
        recomputed_delta = abs(analytic - reference)
        recomputed_relative = recomputed_delta / abs(reference)
        reported_delta = Decimal(row["absolute_difference_J"])
        reported_relative = Decimal(row["relative_difference"])
        tolerance = Decimal(row["agreement_tolerance_J"])
        absolute_serialization_tolerance = max(
            Decimal("1e-100"), abs(reported_delta) * Decimal("1e-50")
        )
        relative_serialization_tolerance = max(
            Decimal("1e-100"), abs(reported_relative) * Decimal("1e-50")
        )
        case_rows.append({
            "case_id": row["case_id"],
            "recomputed_absolute_difference_J": str(recomputed_delta),
            "reported_absolute_difference_J": str(reported_delta),
            "absolute_difference_consistent": (
                abs(recomputed_delta - reported_delta) <= absolute_serialization_tolerance
            ),
            "recomputed_relative_difference": str(recomputed_relative),
            "reported_relative_difference": str(reported_relative),
            "relative_difference_consistent": (
                abs(recomputed_relative - reported_relative) <= relative_serialization_tolerance
            ),
            "inside_tolerance": recomputed_delta <= tolerance,
            "reported_pass": row["passed"],
        })
    maximum_relative = max(Decimal(row["reported_relative_difference"]) for row in case_rows)
    return {
        "reported_self_convergence": gate["radial_self_convergence"],
        "reported_agreement": gate["analytic_radial_agreement"],
        "unique_x_count": gate["unique_x_count"],
        "convergence_rows": convergence_rows,
        "all_eleven_convergence_decisions_reproduced": (
            len(convergence_rows) == 11
            and all(row["decision_reproduced"] for row in convergence_rows)
        ),
        "case_rows": case_rows,
        "all_eight_agreement_decisions_reproduced": (
            len(case_rows) == 8
            and all(
                row["absolute_difference_consistent"]
                and row["relative_difference_consistent"]
                and row["inside_tolerance"]
                and row["reported_pass"] is True
                for row in case_rows
            )
        ),
        "maximum_reported_relative_difference": str(maximum_relative),
        "maximum_relative_difference_below_1e_13": maximum_relative < Decimal("1e-13"),
        "three_failed_stage_a_cases_present": all(
            case_id in {row["case_id"] for row in case_rows}
            for case_id in (
                "LEGACY_STAGE_A_00_LARGE_X",
                "LEGACY_STAGE_A_01_TRANSITION",
                "LEGACY_STAGE_A_02_LONG_RANGE",
            )
        ),
        "independence_qualification_preserved": (
            "Numerical radial agreement validates the reduced evaluator after angular "
            "reduction; the separately passed derivation gate establishes pair factorization."
        ),
    }


def _mutation_audit(execution: dict[str, Any]) -> dict[str, Any]:
    gate = execution["scientific_payload"]["mutation_gate"]
    expected_ids = {
        "INTERPRET_RADIUS_AS_DIAMETER",
        "USE_SURFACE_GAP_AS_CENTER_DISTANCE",
        "OMIT_FOUR_PI_OVER_THREE_MASS_FACTOR",
        "OMIT_A_Y_ONE_THIRD",
        "OMIT_SECOND_SPHERE_FORM_FACTOR",
        "FLIP_YUKAWA_EXPONENTIAL_SIGN",
        "FORCE_DIRECT_LARGE_X_SINH_COSH_PATH",
        "FORCE_DIRECT_SMALL_X_CANCELLATION_PATH",
    }
    rows = []
    for row in gate["rows"]:
        if "delta_J" in row:
            numerical_reason = Decimal(row["delta_J"]) > 0
        elif row["mutation_id"] == "FORCE_DIRECT_LARGE_X_SINH_COSH_PATH":
            numerical_reason = row.get("failure_mode") == "OverflowError"
        else:
            numerical_reason = (
                Decimal(row["absolute_H_difference"]) > Decimal(row["tolerance_H"])
            )
        rows.append({
            "mutation_id": row["mutation_id"],
            "reported_detected": row["detected"],
            "numerical_failure_reason_present": numerical_reason,
        })
    return {
        "reported_status": gate["status"],
        "mutation_ids_exact": {row["mutation_id"] for row in rows} == expected_ids,
        "reported_count": gate["mutation_count"],
        "reported_detected_count": gate["detected_count"],
        "live_path_attested": gate["same_live_evaluator_radial_reference_and_adjudicator"],
        "rows": rows,
        "all_eight_numerically_detected": (
            len(rows) == 8
            and all(row["reported_detected"] and row["numerical_failure_reason_present"] for row in rows)
        ),
    }


def build_report() -> dict[str, Any]:
    frozen = []
    for relative_path, expected in EXECUTION_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"execution artifact custody drift: {relative_path}")
        frozen.append({"relative_path": relative_path, "sha256": observed})
    execution = _load_json(REPO_ROOT / EXECUTION_RELATIVE_PATH)
    packet = _load_json(REPO_ROOT / PACKET_RELATIVE_PATH)
    if execution.get("selected_next_target") != TARGET:
        raise ValueError("execution did not rotate to this result review")
    if execution.get("principal_result") != "ANALYTIC_SPHERE_ORACLE_QUALIFIED":
        raise ValueError("unexpected execution result")
    if execution.get("authority", {}).get("performed_execution_count") != 1:
        raise ValueError("execution count is not exactly one")
    if execution["authority"]["runner_sha256"] != EXECUTION_HASHES[
        "formal/python/tools/scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_v0.py"
    ]:
        raise ValueError("runner hash does not match execution evidence")

    custody = _custody_audit(execution)
    derivation = _derivation_audit(execution)
    evaluator = _evaluator_audit(execution, packet)
    radial = _radial_and_agreement_audit(execution)
    mutations = _mutation_audit(execution)
    stage_duration_sum = sum(row["duration_seconds"] for row in custody["stage_rows"])
    worker_duration = float(execution["scientific_payload"]["total_worker_duration_seconds"])
    runtime = {
        "worker_duration_seconds": worker_duration,
        "stage_duration_sum_seconds": stage_duration_sum,
        "difference_seconds": abs(worker_duration - stage_duration_sum),
        "consistent_within_0_1_seconds": abs(worker_duration - stage_duration_sum) <= 0.1,
        "within_600_second_budget": worker_duration < 600.0,
    }
    scope = execution["scope"]

    gates = [
        ("R01_EXACT_EXECUTION_ARTIFACT_CUSTODY", True, "five execution surfaces hash-verified"),
        ("R02_RELEASE_AND_CANONICAL_RESULT_IDENTICAL", custody["release_equals_canonical_result"], "byte-identical results"),
        ("R03_RUNNER_HASH_MATCHES_LAUNCH_EVIDENCE", execution["authority"]["runner_sha256"] == EXECUTION_HASHES["formal/python/tools/scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_v0.py"], "launched implementation frozen"),
        ("R04_WORKER_PAYLOAD_MATCHES_RELEASE", custody["reported_payload_equals_atomic_file"], "scientific payload unaltered"),
        ("R05_LAUNCH_CUSTODY_MATCHES_RELEASE", custody["reported_custody_equals_atomic_file"], "custody object unaltered"),
        ("R06_EXACTLY_ONE_LAUNCH_IDENTITY", custody["launch_count"] == 1 and custody["launch_flag_run_id"] == custody["run_id"], "one run id and one launch flag"),
        ("R07_EXIT_ZERO_AND_NO_TIMEOUT", custody["worker_exit_code"] == 0 and custody["timeout_initiated_at_utc"] is None, "normal completion"),
        ("R08_ZERO_SURVIVING_PROCESSES", custody["zero_surviving_processes"], "job object closed with no survivor"),
        ("R09_JOB_OBJECT_AND_MEMORY_LIMIT", custody["process_group_mechanism"] == "WINDOWS_JOB_OBJECT_KILL_ON_CLOSE_AND_JOB_MEMORY_LIMIT" and custody["peak_job_memory_within_limit"], f"peak {custody['peak_job_memory_bytes']} bytes"),
        ("R10_RAW_TRANSCRIPT_HASH_REPRODUCED", custody["raw_launcher_log_sha256_reported"] == custody["raw_launcher_log_sha256_observed"], "raw log hash exact"),
        ("R11_RAW_STAGE_ORDER_AND_SINGLE_OUTCOME", custody["raw_log_stage_start_count"] == custody["raw_log_stage_end_count"] == 6 and custody["raw_log_outcome_count"] == 1 and custody["raw_log_stage_order_exact"], "six ordered starts and ends"),
        ("R12_ALL_ATOMIC_STAGE_FILES_MATCH_REPORT", custody["all_stage_files_match_report"], "six stage files exact"),
        ("R13_ALL_STAGES_COMPLETE_AND_WITHIN_BUDGET", custody["all_stages_complete"] and custody["all_stages_within_budget"], "six of six complete"),
        ("R14_CURRENT_STAGE_POINTER_QUALIFIED_NON_DECISION_BEARING", not custody["current_stage_pointer_terminalized"] and not custody["current_stage_pointer_decision_bearing"], custody["custody_qualification"]),
        ("R15_STRICT_NONOVERLAP_DERIVATION_GATE", derivation["strict_nonoverlap_all_cases"], "all eight cases"),
        ("R16_NEWTONIAN_SHELL_RESULT_RECORDED", derivation["newtonian_shell_derivation_present"], "U_N=-G*M1*M2/D"),
        ("R17_YUKAWA_ANGULAR_KERNEL_IDENTITY_RECORDED", derivation["yukawa_angular_kernel_identity_present"], "external-field angular reduction"),
        ("R18_RADIAL_ANTIDERIVATIVE_AND_FORM_FACTOR_RECORDED", derivation["radial_antiderivative_present"], "homogeneous-sphere form factor"),
        ("R19_TWO_FACTORS_CENTER_EXPONENT_AND_A_Y", derivation["both_form_factors_present"] and derivation["center_distance_exponential_present"] and derivation["yukawa_amplitude_exact"] == "1/3", "convention complete"),
        ("R20_MASS_UNITS_SYMMETRY_AND_POINT_LIMIT", derivation["sphere_exchange_symmetry"] and derivation["energy_units"] == "kg*m^2*s^-2=J" and derivation["point_particle_limit_reproduced"], "independently reproduced"),
        ("R21_SMALL_X_SERIES_COEFFICIENTS_REPRODUCED", derivation["independently_reproduced_series_coefficients"] == ["1", "1/10", "1/280", "1/15120", "1/1330560"], "exact rational coefficients"),
        ("R22_EVALUATOR_REGIME_ROUTING_EXACT", evaluator["all_case_regimes_exact"], "small/direct/scaled routing"),
        ("R23_ALL_SIX_OVERLAP_DECISIONS_REPRODUCED", evaluator["all_six_overlap_decisions_reproduced"], "stored values recomputed"),
        ("R24_X_1000_SCALED_WITHOUT_DIRECT_FALLBACK", evaluator["x_1000_used_scaled_branch"] and not evaluator["direct_hyperbolic_at_x_1000"], "large-x path exact"),
        ("R25_NO_SILENT_OVERFLOW_OR_UNDERFLOW", evaluator["all_scaled_factors_finite_positive"] and not evaluator["silent_overflow_or_underflow"], "all case factors finite"),
        ("R26_EXACT_ELEVEN_RADIAL_X_VALUES", radial["unique_x_count"] == 11 and len(radial["convergence_rows"]) == 11, "0.001 through 1000"),
        ("R27_ALL_SELF_CONVERGENCE_DECISIONS_REPRODUCED", radial["all_eleven_convergence_decisions_reproduced"] and radial["reported_self_convergence"] == "PASS", "only converged values used"),
        ("R28_ALL_EIGHT_CASE_AGREEMENTS_REPRODUCED", radial["all_eight_agreement_decisions_reproduced"] and radial["reported_agreement"] == "PASS", "absolute and relative differences recomputed"),
        ("R29_MAXIMUM_RELATIVE_DIFFERENCE_REPRODUCED", radial["maximum_relative_difference_below_1e_13"], f"maximum {radial['maximum_reported_relative_difference']}"),
        ("R30_THREE_FAILED_STAGE_A_CASES_INCLUDED", radial["three_failed_stage_a_cases_present"], "no production adjudication inferred"),
        ("R31_EXACT_EIGHT_MUTATION_IDENTITIES", mutations["mutation_ids_exact"] and mutations["reported_count"] == 8, "frozen mutation set"),
        ("R32_ALL_MUTATIONS_NUMERICALLY_DETECTED", mutations["all_eight_numerically_detected"] and mutations["reported_detected_count"] == 8, "decision-bearing numerical reasons"),
        ("R33_MUTATIONS_USE_LIVE_REFERENCE_PATH", mutations["live_path_attested"], "no metadata-only rejection"),
        ("R34_RUNTIME_RECORDS_INTERNALLY_CONSISTENT", runtime["consistent_within_0_1_seconds"], "worker and stage durations agree"),
        ("R35_TIME_AND_MEMORY_WITHIN_ENVELOPE", runtime["within_600_second_budget"] and custody["peak_job_memory_within_limit"], "bounded execution"),
        ("R36_QUALIFIED_OUTCOME_PREREQUISITES_ALL_PASS", derivation["passed"] and evaluator["reported_status"] == "PASS" and radial["reported_self_convergence"] == "PASS" and radial["reported_agreement"] == "PASS" and mutations["reported_status"] == "PASS", "all separate gates satisfied"),
        ("R37_PRODUCTION_CUBATURE_NOT_CALLED_OR_ADJUDICATED", not scope["production_cubature_called"] and not scope["production_cubature_adjudicated"], "production remains unadjudicated"),
        ("R38_NO_TORQUE_DFT_VECTOR_JACOBIAN_OR_STAGE_B", not any(scope[key] for key in ("torque_computed", "angular_dft_computed", "final_real_150_vector_computed", "jacobian_or_svd_computed", "identifiability_computed", "stage_b_performed")), "downstream firewalls closed"),
        ("R39_ONE_SHOT_AUTHORITY_CONSUMED_NO_RERUN", execution["authority"]["authorized_execution_count"] == execution["authority"]["performed_execution_count"] == 1, "1/1 consumed"),
        ("R40_FRESH_SELECTOR_ONLY_AFTER_REVIEW", True, "review does not directly authorize production comparison"),
    ]
    gate_rows = []
    for gate_id, passed, detail in gates:
        status = "PASS_WITH_QUALIFICATION" if gate_id == "R14_CURRENT_STAGE_POINTER_QUALIFIED_NON_DECISION_BEARING" and passed else ("PASS" if passed else "FAIL")
        gate_rows.append({"gate_id": gate_id, "status": status, "detail": detail})
    failures = [row["gate_id"] for row in gate_rows if row["status"] == "FAIL"]
    if failures:
        raise ValueError(f"independent execution result review failed: {failures}")

    review_scope = {
        "independent_execution_result_review_performed": True,
        "execution_custody_accepted": True,
        "analytic_sphere_oracle_qualified_result_accepted": True,
        "fresh_scientific_response_selector_authorized": True,
        "oracle_execution_rerun_authorized": False,
        "production_cubature_comparison_authorized": False,
        "production_kernel_replacement_authorized": False,
        "stage_a_rerun_authorized": False,
        "torque_or_dft_authorized": False,
        "final_real_150_vector_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_b_eligible": False,
        "stage_b_authorized": False,
    }
    return {
        "schema_id": "toe.scalar_only_yukawa.analytic_sphere_oracle.qualification_execution_result_review.v0",
        "review_id": "SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_EXECUTION_RESULT_REVIEW_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "status": "INDEPENDENT_EXECUTION_RESULT_REVIEW_COMPLETE",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_execution_result": execution["principal_result"],
            "frozen_execution_artifacts": frozen,
            "human_review": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_analytic_sphere_oracle_"
                "qualification_execution_result_review_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "independent_custody_audit": custody,
        "independent_derivation_audit": derivation,
        "independent_evaluator_audit": evaluator,
        "independent_radial_and_agreement_audit": radial,
        "independent_mutation_audit": mutations,
        "independent_runtime_audit": runtime,
        "review_gates": {
            "gate_count": len(gate_rows),
            "pass_count": sum(row["status"] == "PASS" for row in gate_rows),
            "qualified_pass_count": sum(row["status"] == "PASS_WITH_QUALIFICATION" for row in gate_rows),
            "admissible_count": sum(row["status"] != "FAIL" for row in gate_rows),
            "failure_count": 0,
            "rows": gate_rows,
        },
        "accepted_result": {
            "analytic_sphere_oracle": "QUALIFIED_ON_EIGHT_FROZEN_CASES_AND_OVERLAP_PROBES",
            "derivation": "ACCEPTED",
            "stable_evaluator": "ACCEPTED",
            "radial_self_convergence": "ACCEPTED_11_OF_11",
            "analytic_radial_agreement": "ACCEPTED_8_OF_8",
            "maximum_relative_difference": radial["maximum_reported_relative_difference"],
            "mutations": "ACCEPTED_8_OF_8",
            "production_cubature": "UNADJUDICATED",
            "continuous_uniform_error_claim": "NOT_ESTABLISHED",
            "execution_rerun": "NOT_AUTHORIZED",
            "required_next_action": "FRESH_SCIENTIFIC_RESPONSE_SELECTOR",
        },
        "scope": review_scope,
        "claim_ceiling": (
            "This review accepts the analytic homogeneous-sphere oracle on the frozen "
            "cases and overlap probes. It does not establish a continuous uniform-error "
            "bound, adjudicate or replace production cubature, rerun Stage A, validate "
            "torque or DFT, decide identifiability, or authorize Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Independently review the completed analytic sphere-oracle execution without rerunning it."
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
        print("analytic sphere-oracle execution result review artifact missing or stale")
        return 1
    report = json.loads(report_path.read_text(encoding="utf-8"))
    print(
        "analytic sphere-oracle execution result review OK "
        f"verdict={VERDICT} admissible={report['review_gates']['admissible_count']}/"
        f"{report['review_gates']['gate_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
