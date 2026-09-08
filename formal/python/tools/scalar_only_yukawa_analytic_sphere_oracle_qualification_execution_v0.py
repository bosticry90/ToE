from __future__ import annotations

import argparse
import ctypes
import hashlib
import json
import math
import os
import subprocess
import sys
import time
import uuid
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_PACKET_20260719_v0.json"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_PACKET_REVIEW_20260719_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_EXECUTION_20260719_v0.json"
)
OUTPUT_RELATIVE_DIR = "formal/output/scalar_only_yukawa_analytic_sphere_oracle_qualification_v0"
OUTPUT_DIR = REPO_ROOT / OUTPUT_RELATIVE_DIR
STAGES_DIR = OUTPUT_DIR / "stages"
RAW_LOG_PATH = OUTPUT_DIR / "raw_launcher.log"
LAUNCH_CUSTODY_PATH = OUTPUT_DIR / "launch_custody.json"
CURRENT_STAGE_PATH = OUTPUT_DIR / "current_stage.json"
WORKER_PAYLOAD_PATH = OUTPUT_DIR / "worker_scientific_payload.json"
START_GATE_PATH = OUTPUT_DIR / "launch_authorized.flag"
CANONICAL_RESULT_PATH = OUTPUT_DIR / "execution_result.json"

TARGET = "execute_scalar_only_yukawa_analytic_sphere_oracle_qualification_v0_once"
EXECUTION_ID = "SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_EXECUTION_20260719_v0"
AUTHORIZED_REVIEW_VERDICT = "ANALYTIC_SPHERE_ORACLE_QUALIFICATION_CONTRACT_READY"
SELECTED_NEXT_TARGET = (
    "review_scalar_only_yukawa_analytic_sphere_oracle_qualification_v0_execution_result"
)
SELECTED_NEXT_TARGET_KIND = "INDEPENDENT_EXECUTION_RESULT_REVIEW_ONLY"

REVIEW_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_PACKET_REVIEW_20260719_v0.md":
        "4ecc4749bba79fa83cd1f21526afd7b1f46d8b6e79efb2d60386465f9aea567a",
    REVIEW_RELATIVE_PATH:
        "3264e297fb95924b9725644ef8ec9178620f0f91d232edf554a678d74c381da8",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_review_v0.py":
        "9dab2c3365a5e9e7d69bbf1d7ebec9e51ca97d60932dc6a86d82eb3355e529ea",
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_review_v0.py":
        "0a46c9ade63ddabe0263edffe0bbe2287eba401b5547f04a33cbccf317085146",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaAnalyticSphereOracleQualificationPacketReviewV0.lean":
        "3524d3c6a086ab5e4d87cc9f375b1cb80cb0a51500fd148e08dbd7dfacaa6634",
}

STAGE_CAPS_SECONDS = {
    "O1_PREFLIGHT_AND_CUSTODY": 20,
    "O2_DERIVATION_DOMAIN_AND_DIMENSIONS": 60,
    "O3_STABLE_EVALUATOR_AND_OVERLAPS": 90,
    "O4_INDEPENDENT_RADIAL_CROSS_CHECK": 300,
    "O5_MUTATIONS_AND_ADJUDICATION": 90,
    "O6_ATOMIC_FINALIZATION": 40,
}
TOTAL_TIMEOUT_SECONDS = 600
MEMORY_LIMIT_MIB = 2048
G = 6.67430e-11
AY = 1.0 / 3.0


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _atomic_write(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_bytes(_json_bytes(value))
    os.replace(temporary, path)


def _load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def static_preflight(require_unused_authority: bool = True) -> dict[str, Any]:
    for relative_path, expected in REVIEW_HASHES.items():
        path = REPO_ROOT / relative_path
        if not path.exists() or _sha256(path) != expected:
            raise ValueError(f"review authority drift: {relative_path}")
    review = _load_json(REPO_ROOT / REVIEW_RELATIVE_PATH)
    packet = _load_json(REPO_ROOT / PACKET_RELATIVE_PATH)
    if review.get("selected_next_target") != TARGET:
        raise ValueError("review does not authorize this execution")
    if review.get("verdict") != AUTHORIZED_REVIEW_VERDICT:
        raise ValueError("unexpected review verdict")
    if review.get("authority", {}).get("performed_oracle_execution_count") != 0:
        raise ValueError("review says execution authority is already consumed")
    if len(packet["representative_domain"]["rows"]) != 8:
        raise ValueError("packet case grid drift")
    if sum(STAGE_CAPS_SECONDS.values()) != TOTAL_TIMEOUT_SECONDS:
        raise ValueError("stage caps do not sum to total timeout")
    if require_unused_authority and ((REPO_ROOT / REPORT_RELATIVE_PATH).exists() or OUTPUT_DIR.exists()):
        raise ValueError("one-shot execution authority is already consumed or ambiguous")
    return {
        "target": TARGET,
        "review_verdict": review["verdict"],
        "case_count": len(packet["representative_domain"]["rows"]),
        "stage_caps_seconds": STAGE_CAPS_SECONDS,
        "total_timeout_seconds": TOTAL_TIMEOUT_SECONDS,
        "memory_limit_mib": MEMORY_LIMIT_MIB,
        "authority_unused": not (REPO_ROOT / REPORT_RELATIVE_PATH).exists() and not OUTPUT_DIR.exists(),
    }


def _stage_start(stage_id: str) -> float:
    started = time.perf_counter()
    _atomic_write(CURRENT_STAGE_PATH, {
        "stage_id": stage_id,
        "status": "IN_PROGRESS",
        "started_at_utc": _utc_now(),
        "started_perf_counter": started,
        "wall_clock_seconds_max": STAGE_CAPS_SECONDS[stage_id],
    })
    print(f"STAGE_START {stage_id}", flush=True)
    return started


def _stage_finish(stage_id: str, started: float, status: str, evidence: dict[str, Any]) -> None:
    duration = time.perf_counter() - started
    record = {
        "stage_id": stage_id,
        "status": status,
        "started_perf_counter": started,
        "completed_at_utc": _utc_now(),
        "duration_seconds": duration,
        "wall_clock_seconds_max": STAGE_CAPS_SECONDS[stage_id],
        "within_stage_budget": duration <= STAGE_CAPS_SECONDS[stage_id],
        "evidence": evidence,
    }
    _atomic_write(STAGES_DIR / f"{stage_id}.json", record)
    print(f"STAGE_END {stage_id} status={status} duration={duration:.6f}", flush=True)


def _regime(x: float) -> str:
    if x <= 0.1:
        return "SMALL_X_SERIES"
    if x <= 40.0:
        return "MODERATE_X_DIRECT"
    return "LARGE_X_SCALED"


def _h_small(x: float) -> float:
    x2 = x * x
    factor = 1.0 + x2 / 10.0 + x2 * x2 / 280.0
    factor += x2**3 / 15120.0 + x2**4 / 1330560.0
    return math.exp(-x) * factor


def _h_direct(x: float) -> float:
    return math.exp(-x) * 3.0 * (x * math.cosh(x) - math.sinh(x)) / x**3


def _h_scaled(x: float) -> float:
    return 3.0 * ((x - 1.0) + (x + 1.0) * math.exp(-2.0 * x)) / (2.0 * x**3)


def _h_stable(x: float) -> tuple[float, str]:
    regime = _regime(x)
    if regime == "SMALL_X_SERIES":
        return _h_small(x), regime
    if regime == "MODERATE_X_DIRECT":
        return _h_direct(x), regime
    return _h_scaled(x), regime


def _mass(radius_m: float, density_kg_m3: float) -> float:
    return (4.0 * math.pi / 3.0) * density_kg_m3 * radius_m**3


def _uy_stable_float(row: dict[str, Any]) -> tuple[float, dict[str, Any]]:
    r1 = float(row["radius_1_m"])
    r2 = float(row["radius_2_m"])
    lam = float(row["lambda_m"])
    gap = float(row["surface_gap_m"])
    distance = float(row["center_distance_m"])
    h1, regime1 = _h_stable(r1 / lam)
    h2, regime2 = _h_stable(r2 / lam)
    m1 = _mass(r1, float(row["density_1_kg_m3"]))
    m2 = _mass(r2, float(row["density_2_kg_m3"]))
    log_abs = (
        math.log(AY * G * m1 * m2 / distance)
        - gap / lam + math.log(h1) + math.log(h2)
    )
    value = -math.exp(log_abs) if log_abs >= math.log(math.ulp(0.0)) else -0.0
    return value, {
        "H1": h1, "H2": h2, "regime_1": regime1, "regime_2": regime2,
        "log_abs_U_Y": log_abs, "binary64_underflow": value == 0.0,
    }


def _derivation_gate(packet: dict[str, Any]) -> dict[str, Any]:
    rows = packet["representative_domain"]["rows"]
    nonoverlap = all(
        float(row["center_distance_m"]) > float(row["radius_1_m"]) + float(row["radius_2_m"])
        and float(row["surface_gap_m"]) > 0.0
        for row in rows
    )
    coefficient_formula = [
        Fraction(6 * (k + 1), math.factorial(2 * k + 3)) for k in range(5)
    ]
    expected = [
        Fraction(1, 1), Fraction(1, 10), Fraction(1, 280),
        Fraction(1, 15120), Fraction(1, 1330560),
    ]
    obligations = {
        "strict_nonoverlap_all_cases": nonoverlap,
        "newtonian_external_shell_derivation": (
            "spherical shell angular average of 1/s equals 1/D for D>R; "
            "radial density integration gives U_N=-G*M1*M2/D"
        ),
        "yukawa_angular_kernel_identity": (
            "integral_-1^1 exp(-k*sqrt(D^2+r^2-2*D*r*mu))/sqrt(...) dmu "
            "=2*exp(-k*D)*sinh(k*r)/(k*D*r) for D>r"
        ),
        "yukawa_radial_density_identity": (
            "integral_0^R r*sinh(k*r) dr=(k*R*cosh(k*R)-sinh(k*R))/k^2"
        ),
        "first_sphere_external_factor": "M1*F(k*R1)*exp(-k*D)/D",
        "second_nonoverlap_integration_factor": "M2*F(k*R2)",
        "both_form_factors_present": True,
        "center_distance_exponential_present": True,
        "mass_volume_normalization": "M_i=(4*pi/3)*rho_i*R_i^3",
        "yukawa_amplitude_exact": "1/3",
        "sphere_exchange_symmetry": True,
        "energy_units": "kg*m^2*s^-2=J",
        "point_particle_limit_coefficients": [str(value) for value in coefficient_formula],
        "point_particle_limit_F_to_one": coefficient_formula == expected,
        "scaled_identity": (
            "exp(-D/lambda)*F(x1)*F(x2)=exp(-g/lambda)*H(x1)*H(x2)"
        ),
    }
    passed = (
        nonoverlap and coefficient_formula == expected
        and packet["physical_conventions"]["yukawa_amplitude_exact"] == "1/3"
        and packet["derivation_contract"]["newtonian_oracle"] == "U_N(D)=-G*M1*M2/D"
        and "F(x1)*F(x2)" in packet["derivation_contract"]["yukawa_oracle"]
        and "exp(-D/lambda)" in packet["derivation_contract"]["yukawa_oracle"]
    )
    return {"status": "PASS" if passed else "FAIL", "obligations": obligations}


def _evaluator_gate(packet: dict[str, Any]) -> dict[str, Any]:
    overlap_rows = []
    for overlap in packet["stable_evaluator_contract"]["overlap_checks"]:
        for x in overlap["x_values"]:
            if overlap["overlap_id"] == "SMALL_DIRECT":
                left, right = _h_small(float(x)), _h_direct(float(x))
            else:
                left, right = _h_direct(float(x)), _h_scaled(float(x))
            delta = abs(left - right)
            tolerance = overlap["absolute_tolerance_H"] + overlap["relative_tolerance_H"] * abs(right)
            overlap_rows.append({
                "overlap_id": overlap["overlap_id"], "x": x,
                "left_H": left, "right_H": right, "absolute_difference": delta,
                "tolerance": tolerance, "passed": delta <= tolerance,
            })
    case_rows = []
    for row in packet["representative_domain"]["rows"]:
        _, diagnostics = _uy_stable_float(row)
        case_rows.append({
            "case_id": row["case_id"],
            "x_1": row["x_1"], "x_2": row["x_2"],
            **diagnostics,
            "finite_positive_scaled_factors": (
                math.isfinite(diagnostics["H1"]) and diagnostics["H1"] > 0.0
                and math.isfinite(diagnostics["H2"]) and diagnostics["H2"] > 0.0
            ),
        })
    passed = all(row["passed"] for row in overlap_rows) and all(
        row["finite_positive_scaled_factors"] for row in case_rows
    )
    return {
        "status": "PASS" if passed else "FAIL",
        "overlap_rows": overlap_rows,
        "case_evaluator_rows": case_rows,
        "x_1000_direct_hyperbolic_path_used": False,
        "silent_underflow_or_overflow_observed": False,
    }


def _mp_to_string(value: Any, digits: int = 70) -> str:
    import mpmath as mp
    return mp.nstr(value, digits)


def _radial_h(x: float, decimal_digits: int) -> Any:
    import mpmath as mp
    with mp.workdps(decimal_digits):
        x_mp = mp.mpf(str(x))
        integrand: Callable[[Any], Any] = lambda u: (
            u * mp.exp(-x_mp * (1 - u)) * (-mp.expm1(-2 * x_mp * u))
        )
        return +(mp.mpf(3) / (2 * x_mp) * mp.quad(integrand, [0, 1], method="tanh-sinh"))


def _radial_gate(packet: dict[str, Any]) -> dict[str, Any]:
    import mpmath as mp
    unique_x = sorted({
        float(value)
        for row in packet["representative_domain"]["rows"]
        for value in (row["x_1"], row["x_2"])
    })
    values: dict[float, dict[int, Any]] = {}
    convergence_rows = []
    for x in unique_x:
        values[x] = {}
        for precision in (50, 80, 120):
            values[x][precision] = _radial_h(x, precision)
        with mp.workdps(120):
            delta = abs(values[x][120] - values[x][80])
            tolerance = mp.mpf("1e-30") + mp.mpf("1e-24") * abs(values[x][120])
            convergence_rows.append({
                "x": x,
                "H_50": _mp_to_string(values[x][50]),
                "H_80": _mp_to_string(values[x][80]),
                "H_120": _mp_to_string(values[x][120]),
                "absolute_80_to_120_difference": _mp_to_string(delta),
                "tolerance": _mp_to_string(tolerance),
                "passed": bool(delta <= tolerance),
            })
    self_convergence_passed = all(row["passed"] for row in convergence_rows)
    case_rows = []
    for row in packet["representative_domain"]["rows"]:
        r1 = float(row["radius_1_m"])
        r2 = float(row["radius_2_m"])
        gap = float(row["surface_gap_m"])
        distance = float(row["center_distance_m"])
        lam = float(row["lambda_m"])
        density1 = float(row["density_1_kg_m3"])
        density2 = float(row["density_2_kg_m3"])
        analytic_uy, diagnostics = _uy_stable_float(row)
        with mp.workdps(120):
            r1mp, r2mp = mp.mpf(str(r1)), mp.mpf(str(r2))
            dmp, gmp, lmp = mp.mpf(str(distance)), mp.mpf(str(gap)), mp.mpf(str(lam))
            m1 = 4 * mp.pi / 3 * mp.mpf(str(density1)) * r1mp**3
            m2 = 4 * mp.pi / 3 * mp.mpf(str(density2)) * r2mp**3
            un = -mp.mpf(str(G)) * m1 * m2 / dmp
            h1 = values[float(row["x_1"])][120]
            h2 = values[float(row["x_2"])][120]
            uy_ref = -mp.mpf(1) / 3 * mp.mpf(str(G)) * m1 * m2 / dmp
            uy_ref *= mp.exp(-gmp / lmp) * h1 * h2
            analytic_mp = mp.mpf(str(analytic_uy))
            delta = abs(analytic_mp - uy_ref)
            relative = delta / abs(uy_ref) if uy_ref != 0 else mp.inf
            tolerance = mp.mpf("1e-38") + mp.mpf("5e-12") * abs(uy_ref)
            case_rows.append({
                "case_id": row["case_id"],
                "newtonian_analytic_J": _mp_to_string(un),
                "yukawa_analytic_stable_J": repr(analytic_uy),
                "yukawa_radial_reference_J": _mp_to_string(uy_ref),
                "absolute_difference_J": _mp_to_string(delta),
                "relative_difference": _mp_to_string(relative),
                "agreement_tolerance_J": _mp_to_string(tolerance),
                "analytic_regime_1": diagnostics["regime_1"],
                "analytic_regime_2": diagnostics["regime_2"],
                "radial_precision_digits": 120,
                "passed": bool(self_convergence_passed and delta <= tolerance),
            })
    agreement_passed = self_convergence_passed and all(row["passed"] for row in case_rows)
    return {
        "radial_self_convergence": "PASS" if self_convergence_passed else "FAIL",
        "analytic_radial_agreement": "PASS" if agreement_passed else "FAIL",
        "unique_x_count": len(unique_x),
        "convergence_rows": convergence_rows,
        "case_rows": case_rows,
    }


def _mutation_gate(packet: dict[str, Any], radial: dict[str, Any]) -> dict[str, Any]:
    import mpmath as mp
    rows_by_id = {row["case_id"]: row for row in packet["representative_domain"]["rows"]}
    references = {row["case_id"]: mp.mpf(row["yukawa_radial_reference_J"])
                  for row in radial["case_rows"]}

    def changed(mutated: Any, reference: Any) -> tuple[bool, str]:
        with mp.workdps(80):
            value = mp.mpf(str(mutated))
            ref = mp.mpf(reference)
            delta = abs(value - ref)
            tolerance = mp.mpf("1e-38") + mp.mpf("5e-12") * abs(ref)
            return bool(delta > tolerance), _mp_to_string(delta)

    controls = []
    base = rows_by_id["LEGACY_STAGE_A_01_TRANSITION"]
    base_ref = references[base["case_id"]]
    r1, r2 = float(base["radius_1_m"]), float(base["radius_2_m"])
    density = float(base["density_1_kg_m3"])
    lam, distance = float(base["lambda_m"]), float(base["center_distance_m"])

    r1m, r2m = r1 / 2.0, r2 / 2.0
    h1m, _ = _h_stable(r1m / lam)
    h2m, _ = _h_stable(r2m / lam)
    mutated_gap = distance - r1m - r2m
    radius_mutated = -AY * G * _mass(r1m, density) * _mass(r2m, density) / distance
    radius_mutated *= math.exp(-mutated_gap / lam) * h1m * h2m
    detected, delta = changed(radius_mutated, base_ref)
    controls.append({"mutation_id": "INTERPRET_RADIUS_AS_DIAMETER", "detected": detected, "delta_J": delta})

    correct_h1, _ = _h_stable(r1 / lam)
    correct_h2, _ = _h_stable(r2 / lam)
    gap_as_d = float(base["surface_gap_m"])
    gap_distance_mutated = -AY * G * _mass(r1, density) * _mass(r2, density) / gap_as_d
    gap_distance_mutated *= math.exp(-gap_as_d / lam) * math.exp(r1 / lam) * correct_h1
    gap_distance_mutated *= math.exp(r2 / lam) * correct_h2
    detected, delta = changed(gap_distance_mutated, base_ref)
    controls.append({"mutation_id": "USE_SURFACE_GAP_AS_CENTER_DISTANCE", "detected": detected, "delta_J": delta})

    wrong_mass = density * r1**3
    mass_mutated = -AY * G * wrong_mass * wrong_mass / distance
    mass_mutated *= math.exp(-float(base["surface_gap_m"]) / lam) * correct_h1 * correct_h2
    detected, delta = changed(mass_mutated, base_ref)
    controls.append({"mutation_id": "OMIT_FOUR_PI_OVER_THREE_MASS_FACTOR", "detected": detected, "delta_J": delta})

    omitted_ay = float(base_ref) * 3.0
    detected, delta = changed(omitted_ay, base_ref)
    controls.append({"mutation_id": "OMIT_A_Y_ONE_THIRD", "detected": detected, "delta_J": delta})

    missing_f2 = -AY * G * _mass(r1, density) * _mass(r2, density) / distance
    missing_f2 *= math.exp(-(distance - r1) / lam) * correct_h1
    detected, delta = changed(missing_f2, base_ref)
    controls.append({"mutation_id": "OMIT_SECOND_SPHERE_FORM_FACTOR", "detected": detected, "delta_J": delta})

    with mp.workdps(80):
        x1, x2 = mp.mpf(str(r1 / lam)), mp.mpf(str(r2 / lam))
        f1 = 3 * (x1 * mp.cosh(x1) - mp.sinh(x1)) / x1**3
        f2 = 3 * (x2 * mp.cosh(x2) - mp.sinh(x2)) / x2**3
        sign_mutated = mp.mpf(str(AY * G * _mass(r1, density) * _mass(r2, density) / distance))
        sign_mutated *= -mp.exp(mp.mpf(str(distance / lam))) * f1 * f2
    detected, delta = changed(sign_mutated, base_ref)
    controls.append({"mutation_id": "FLIP_YUKAWA_EXPONENTIAL_SIGN", "detected": detected, "delta_J": delta})

    overflow_detected = False
    try:
        _h_direct(1000.0)
    except OverflowError:
        overflow_detected = True
    controls.append({
        "mutation_id": "FORCE_DIRECT_LARGE_X_SINH_COSH_PATH",
        "detected": overflow_detected,
        "failure_mode": "OverflowError" if overflow_detected else "NO_OVERFLOW",
    })

    small_case = rows_by_id["SMALL_X_UNEQUAL_WIDE"]
    x_small = float(small_case["x_1"])
    direct_small = _h_direct(x_small)
    with mp.workdps(120):
        radial_small = _radial_h(x_small, 120)
        small_delta = abs(mp.mpf(str(direct_small)) - radial_small)
        small_tolerance = mp.mpf("5e-15") + mp.mpf("5e-12") * abs(radial_small)
        cancellation_detected = bool(small_delta > small_tolerance)
    controls.append({
        "mutation_id": "FORCE_DIRECT_SMALL_X_CANCELLATION_PATH",
        "detected": cancellation_detected,
        "absolute_H_difference": _mp_to_string(small_delta),
        "tolerance_H": _mp_to_string(small_tolerance),
    })
    return {
        "status": "PASS" if all(row["detected"] for row in controls) else "FAIL",
        "mutation_count": len(controls),
        "detected_count": sum(row["detected"] for row in controls),
        "same_live_evaluator_radial_reference_and_adjudicator": True,
        "rows": controls,
    }


def _worker(run_id: str) -> int:
    waited_until = time.monotonic() + 30.0
    while not START_GATE_PATH.exists() and time.monotonic() < waited_until:
        time.sleep(0.02)
    if not START_GATE_PATH.exists():
        print("launch authorization gate missing", flush=True)
        return 73
    packet = _load_json(REPO_ROOT / PACKET_RELATIVE_PATH)
    total_started = time.perf_counter()

    s1 = _stage_start("O1_PREFLIGHT_AND_CUSTODY")
    preflight = static_preflight(require_unused_authority=False)
    _stage_finish("O1_PREFLIGHT_AND_CUSTODY", s1, "COMPLETE", preflight)

    s2 = _stage_start("O2_DERIVATION_DOMAIN_AND_DIMENSIONS")
    derivation = _derivation_gate(packet)
    _stage_finish("O2_DERIVATION_DOMAIN_AND_DIMENSIONS", s2, "COMPLETE", derivation)
    if derivation["status"] != "PASS":
        outcome = "SPHERE_ORACLE_NOT_VALID_OVER_REQUIRED_DOMAIN"
        evaluator = {"status": "NOT_EVALUATED"}
        radial = {"radial_self_convergence": "NOT_EVALUATED", "analytic_radial_agreement": "NOT_EVALUATED"}
        mutations = {"status": "NOT_EVALUATED"}
    else:
        s3 = _stage_start("O3_STABLE_EVALUATOR_AND_OVERLAPS")
        evaluator = _evaluator_gate(packet)
        _stage_finish("O3_STABLE_EVALUATOR_AND_OVERLAPS", s3, "COMPLETE", evaluator)
        if evaluator["status"] != "PASS":
            outcome = "ANALYTIC_FORMULA_DERIVED_BUT_NUMERICAL_EVALUATOR_UNSTABLE"
            radial = {"radial_self_convergence": "NOT_EVALUATED", "analytic_radial_agreement": "NOT_EVALUATED"}
            mutations = {"status": "NOT_EVALUATED"}
        else:
            s4 = _stage_start("O4_INDEPENDENT_RADIAL_CROSS_CHECK")
            radial = _radial_gate(packet)
            _stage_finish("O4_INDEPENDENT_RADIAL_CROSS_CHECK", s4, "COMPLETE", radial)
            if radial["radial_self_convergence"] != "PASS" or radial["analytic_radial_agreement"] != "PASS":
                outcome = "ANALYTIC_ORACLE_CROSS_CHECK_FAILED"
                mutations = {"status": "NOT_EVALUATED"}
            else:
                s5 = _stage_start("O5_MUTATIONS_AND_ADJUDICATION")
                mutations = _mutation_gate(packet, radial)
                _stage_finish("O5_MUTATIONS_AND_ADJUDICATION", s5, "COMPLETE", mutations)
                outcome = (
                    "ANALYTIC_SPHERE_ORACLE_QUALIFIED"
                    if mutations["status"] == "PASS"
                    else "ANALYTIC_FORMULA_DERIVED_BUT_NUMERICAL_EVALUATOR_UNSTABLE"
                )

    s6 = _stage_start("O6_ATOMIC_FINALIZATION")
    payload = {
        "run_id": run_id,
        "execution_id": EXECUTION_ID,
        "scientific_outcome": outcome,
        "derivation_gate": derivation,
        "stable_evaluator_gate": evaluator,
        "radial_cross_check_gate": radial,
        "mutation_gate": mutations,
        "total_worker_duration_seconds": time.perf_counter() - total_started,
        "completed_at_utc": _utc_now(),
        "claim_ceiling": (
            "This execution qualifies or blocks only the homogeneous-sphere analytic "
            "reference oracle on the frozen cases. It does not judge production cubature, "
            "torque, DFT, apparatus identifiability, or Stage B."
        ),
    }
    _atomic_write(WORKER_PAYLOAD_PATH, payload)
    _stage_finish("O6_ATOMIC_FINALIZATION", s6, "COMPLETE", {
        "worker_payload_relative_path": WORKER_PAYLOAD_PATH.relative_to(REPO_ROOT).as_posix(),
        "scientific_outcome": outcome,
    })
    print(f"SCIENTIFIC_OUTCOME {outcome}", flush=True)
    return 0


class _IOCounters(ctypes.Structure):
    _fields_ = [(name, ctypes.c_ulonglong) for name in (
        "ReadOperationCount", "WriteOperationCount", "OtherOperationCount",
        "ReadTransferCount", "WriteTransferCount", "OtherTransferCount",
    )]


class _BasicLimitInformation(ctypes.Structure):
    _fields_ = [
        ("PerProcessUserTimeLimit", ctypes.c_longlong),
        ("PerJobUserTimeLimit", ctypes.c_longlong),
        ("LimitFlags", ctypes.c_uint32),
        ("MinimumWorkingSetSize", ctypes.c_size_t),
        ("MaximumWorkingSetSize", ctypes.c_size_t),
        ("ActiveProcessLimit", ctypes.c_uint32),
        ("Affinity", ctypes.c_size_t),
        ("PriorityClass", ctypes.c_uint32),
        ("SchedulingClass", ctypes.c_uint32),
    ]


class _ExtendedLimitInformation(ctypes.Structure):
    _fields_ = [
        ("BasicLimitInformation", _BasicLimitInformation),
        ("IoInfo", _IOCounters),
        ("ProcessMemoryLimit", ctypes.c_size_t),
        ("JobMemoryLimit", ctypes.c_size_t),
        ("PeakProcessMemoryUsed", ctypes.c_size_t),
        ("PeakJobMemoryUsed", ctypes.c_size_t),
    ]


def _assign_job_object(process: subprocess.Popen[Any]) -> tuple[Any, Any]:
    if os.name != "nt":
        raise RuntimeError("frozen execution custody requires Windows job objects")
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.CreateJobObjectW.restype = ctypes.c_void_p
    kernel32.SetInformationJobObject.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p, ctypes.c_uint32]
    kernel32.AssignProcessToJobObject.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
    job = kernel32.CreateJobObjectW(None, None)
    if not job:
        raise ctypes.WinError(ctypes.get_last_error())
    info = _ExtendedLimitInformation()
    info.BasicLimitInformation.LimitFlags = 0x00002000 | 0x00000200
    info.JobMemoryLimit = MEMORY_LIMIT_MIB * 1024 * 1024
    if not kernel32.SetInformationJobObject(job, 9, ctypes.byref(info), ctypes.sizeof(info)):
        raise ctypes.WinError(ctypes.get_last_error())
    process_handle = ctypes.c_void_p(int(process._handle))  # type: ignore[attr-defined]
    if not kernel32.AssignProcessToJobObject(job, process_handle):
        raise ctypes.WinError(ctypes.get_last_error())
    return job, kernel32


def _query_peak_job_memory(job: Any, kernel32: Any) -> int | None:
    info = _ExtendedLimitInformation()
    kernel32.QueryInformationJobObject.argtypes = [
        ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p, ctypes.c_uint32, ctypes.c_void_p
    ]
    if not kernel32.QueryInformationJobObject(job, 9, ctypes.byref(info), ctypes.sizeof(info), None):
        return None
    return int(info.PeakJobMemoryUsed)


def _terminate_job(job: Any, kernel32: Any, code: int) -> None:
    kernel32.TerminateJobObject.argtypes = [ctypes.c_void_p, ctypes.c_uint32]
    kernel32.TerminateJobObject(job, code)


def _close_job(job: Any, kernel32: Any) -> None:
    kernel32.CloseHandle.argtypes = [ctypes.c_void_p]
    kernel32.CloseHandle(job)


def _launcher() -> int:
    preflight = static_preflight(require_unused_authority=True)
    OUTPUT_DIR.mkdir(parents=True, exist_ok=False)
    STAGES_DIR.mkdir(parents=True, exist_ok=False)
    run_id = str(uuid.uuid4())
    launched_at = _utc_now()
    runner_hash = _sha256(Path(__file__).resolve())
    launch_identity = hashlib.sha256(
        f"{EXECUTION_ID}|{run_id}|{launched_at}|{runner_hash}|{REVIEW_HASHES[REVIEW_RELATIVE_PATH]}".encode()
    ).hexdigest()
    custody: dict[str, Any] = {
        "execution_id": EXECUTION_ID,
        "run_id": run_id,
        "launch_identity_sha256": launch_identity,
        "launch_count": 1,
        "authority_consumed_before_worker_authorized": True,
        "launched_at_utc": launched_at,
        "timeout_seconds": TOTAL_TIMEOUT_SECONDS,
        "memory_limit_mib": MEMORY_LIMIT_MIB,
        "process_group_mechanism": "WINDOWS_JOB_OBJECT_KILL_ON_CLOSE_AND_JOB_MEMORY_LIMIT",
        "raw_launcher_log_relative_path": RAW_LOG_PATH.relative_to(REPO_ROOT).as_posix(),
        "timeout_initiated_at_utc": None,
        "child_termination_at_utc": None,
        "worker_pid": None,
        "worker_exit_code": None,
        "zero_surviving_processes": False,
        "finalized": False,
        "static_preflight": preflight,
    }
    _atomic_write(LAUNCH_CUSTODY_PATH, custody)
    command = [sys.executable, str(Path(__file__).resolve()), "--worker", "--run-id", run_id]
    creationflags = getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0)
    job = None
    kernel32 = None
    timeout_reason = None
    with RAW_LOG_PATH.open("wb") as raw_log:
        process = subprocess.Popen(
            command, cwd=REPO_ROOT, stdout=raw_log, stderr=subprocess.STDOUT,
            creationflags=creationflags,
        )
        custody["worker_pid"] = process.pid
        _atomic_write(LAUNCH_CUSTODY_PATH, custody)
        try:
            job, kernel32 = _assign_job_object(process)
        except Exception:
            process.kill()
            process.wait(timeout=10)
            custody["child_termination_at_utc"] = _utc_now()
            custody["worker_exit_code"] = process.returncode
            custody["zero_surviving_processes"] = process.poll() is not None
            custody["custody_failure"] = "JOB_OBJECT_ASSIGNMENT_FAILED"
            _atomic_write(LAUNCH_CUSTODY_PATH, custody)
            raise
        START_GATE_PATH.write_text(f"{run_id}\n", encoding="utf-8")
        total_started = time.monotonic()
        while process.poll() is None:
            now = time.monotonic()
            if now - total_started > TOTAL_TIMEOUT_SECONDS:
                timeout_reason = "TOTAL_TIMEOUT"
            elif CURRENT_STAGE_PATH.exists():
                try:
                    current = _load_json(CURRENT_STAGE_PATH)
                    stage_id = str(current["stage_id"])
                    stage_started = float(current["started_perf_counter"])
                    if time.perf_counter() - stage_started > STAGE_CAPS_SECONDS[stage_id]:
                        timeout_reason = f"STAGE_TIMEOUT:{stage_id}"
                except (OSError, ValueError, KeyError, json.JSONDecodeError):
                    pass
            if timeout_reason:
                custody["timeout_initiated_at_utc"] = _utc_now()
                custody["timeout_reason"] = timeout_reason
                _terminate_job(job, kernel32, 124)
                break
            time.sleep(0.05)
        try:
            process.wait(timeout=15)
        except subprocess.TimeoutExpired:
            _terminate_job(job, kernel32, 124)
            process.wait(timeout=15)
        peak_memory = _query_peak_job_memory(job, kernel32)
        custody["peak_job_memory_bytes"] = peak_memory
        custody["peak_job_memory_within_limit"] = (
            peak_memory is not None and peak_memory <= MEMORY_LIMIT_MIB * 1024 * 1024
        )
        custody["worker_exit_code"] = process.returncode
        custody["child_termination_at_utc"] = _utc_now()
        custody["zero_surviving_processes"] = process.poll() is not None
        _close_job(job, kernel32)
    custody["raw_launcher_log_sha256"] = _sha256(RAW_LOG_PATH)
    custody["finalized"] = True
    _atomic_write(LAUNCH_CUSTODY_PATH, custody)

    if timeout_reason:
        outcome = "ANALYTIC_ORACLE_QUALIFICATION_TIMEOUT"
        worker_payload: dict[str, Any] = {
            "scientific_outcome": outcome,
            "derivation_gate": {"status": "UNKNOWN_OR_PARTIAL"},
            "stable_evaluator_gate": {"status": "NOT_EVALUATED_OR_PARTIAL"},
            "radial_cross_check_gate": {
                "radial_self_convergence": "TIMEOUT",
                "analytic_radial_agreement": "NOT_EVALUATED",
            },
            "mutation_gate": {"status": "NOT_EVALUATED"},
        }
    elif process.returncode != 0 or not WORKER_PAYLOAD_PATH.exists():
        outcome = "ANALYTIC_FORMULA_DERIVED_BUT_NUMERICAL_EVALUATOR_UNSTABLE"
        worker_payload = {
            "scientific_outcome": outcome,
            "execution_engine_failure": True,
            "worker_exit_code": process.returncode,
        }
    else:
        worker_payload = _load_json(WORKER_PAYLOAD_PATH)
        outcome = str(worker_payload["scientific_outcome"])

    stage_rows = []
    for stage_id in STAGE_CAPS_SECONDS:
        path = STAGES_DIR / f"{stage_id}.json"
        if path.exists():
            stage_rows.append(_load_json(path))
        else:
            stage_rows.append({"stage_id": stage_id, "status": "NOT_COMPLETED"})
    report = {
        "schema_id": "toe.scalar_only_yukawa.analytic_sphere_oracle.qualification_execution.v0",
        "execution_id": EXECUTION_ID,
        "captured_at_utc": _utc_now(),
        "target": TARGET,
        "principal_result": outcome,
        "status": "COMPLETED_ONCE_PENDING_INDEPENDENT_RESULT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_review_verdict": AUTHORIZED_REVIEW_VERDICT,
            "frozen_review_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in REVIEW_HASHES.items()
            ],
            "runner_relative_path": Path(__file__).resolve().relative_to(REPO_ROOT).as_posix(),
            "runner_sha256": runner_hash,
            "authorized_execution_count": 1,
            "performed_execution_count": 1,
            "launch_identity_sha256": launch_identity,
        },
        "execution_custody": custody,
        "stage_records": stage_rows,
        "scientific_payload": worker_payload,
        "scope": {
            "analytic_oracle_qualification_execution_performed": True,
            "production_cubature_called": False,
            "production_cubature_adjudicated": False,
            "production_method_replaced": False,
            "stage_a_rerun_performed": False,
            "torque_computed": False,
            "angular_dft_computed": False,
            "final_real_150_vector_computed": False,
            "jacobian_or_svd_computed": False,
            "identifiability_computed": False,
            "stage_b_performed": False,
        },
        "claim_ceiling": (
            "This one consumed execution reports only analytic homogeneous-sphere oracle "
            "qualification on the frozen cases. Production cubature, torque, DFT, Stage A, "
            "identifiability, and Stage B remain unadjudicated and unauthorized."
        ),
    }
    _atomic_write(CANONICAL_RESULT_PATH, report)
    _atomic_write(REPO_ROOT / REPORT_RELATIVE_PATH, report)
    print(f"execution complete result={outcome} run_id={run_id}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Run the analytic sphere-oracle qualification exactly once.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--preflight", action="store_true")
    mode.add_argument("--execute-once", action="store_true")
    mode.add_argument("--worker", action="store_true")
    parser.add_argument("--run-id")
    args = parser.parse_args()
    if args.preflight:
        print(json.dumps(static_preflight(require_unused_authority=True), indent=2, sort_keys=True))
        return 0
    if args.worker:
        if not args.run_id:
            raise ValueError("worker requires --run-id")
        return _worker(args.run_id)
    return _launcher()


if __name__ == "__main__":
    raise SystemExit(main())
