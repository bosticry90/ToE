from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CALCULATION_ID = "CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-MINKOWSKI-v0"
CAPTURED_AT_UTC = "2026-07-09T00:00:00Z"
GUARDRAIL_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_QFT_GR_SOURCE_CONTRACT_FLAT_LIMIT_PRETEST_"
    "GUARDRAIL_PACKET_20260709_v0.json"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/toe/calculations/"
    "calc_scalar_stress_energy_divergence_identity_minkowski.py"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/calculations/"
    "test_calc_scalar_stress_energy_divergence_identity_minkowski.py"
)
OUTPUT_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-"
    "MINKOWSKI-v0.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-"
    "MINKOWSKI-MANIFEST-v0.json"
)
RESULT_REVIEW_TARGET = (
    "review_calc_scalar_stress_energy_divergence_identity_minkowski_v0_result"
)
THRESHOLD_REPAIR_TARGET = (
    "repair_calc_scalar_stress_energy_divergence_identity_minkowski_v0_"
    "threshold_failure"
)
EXECUTION_COMMAND = (
    "python -m formal.python.toe.calculations."
    "calc_scalar_stress_energy_divergence_identity_minkowski"
)

AMPLITUDE = 0.2
WAVE_NUMBER = 2.0
MASS = 1.0
TIME_SLICES = (0.0, 0.37, 0.91)
RESOLUTIONS = (64, 128, 256, 512)
OMEGA_ON = math.sqrt(5.0)
OMEGA_OFF = 1.1 * OMEGA_ON
EXACT_OFF_SHELL_COEFFICIENT = 1.05
RELATIVE_ERROR_FLOOR = 1e-14

MINIMUM_CONVERGENCE_ORDER = 1.8
MAXIMUM_FINEST_OFF_SHELL_RELATIVE_ERROR = 0.02
MAXIMUM_COEFFICIENT_ERROR = 1e-12
MINIMUM_OFF_TO_ON_DIVERGENCE_RATIO = 100.0

EQUATION_IDS_PENDING_REVIEW = (
    "EQ-QFT-SCALAR-STRESS-ENERGY-v0",
    "EQ-QFT-SCALAR-STRESS-DIVERGENCE-IDENTITY-v0",
)


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def centered_periodic_difference(values: np.ndarray, dx: float) -> np.ndarray:
    return (np.roll(values, -1) - np.roll(values, 1)) / (2.0 * dx)


def rms(values: np.ndarray) -> float:
    return float(np.sqrt(np.mean(np.square(values))))


def combined_rms(component_0: np.ndarray, component_1: np.ndarray) -> float:
    return float(np.sqrt(np.mean(np.square(component_0) + np.square(component_1))))


def _plane_wave_fields(
    x: np.ndarray,
    *,
    time: float,
    omega: float,
) -> dict[str, np.ndarray]:
    theta = WAVE_NUMBER * x - omega * time
    phi = AMPLITUDE * np.cos(theta)
    phi_t = AMPLITUDE * omega * np.sin(theta)
    phi_x = -AMPLITUDE * WAVE_NUMBER * np.sin(theta)
    phi_tt = -(omega**2) * phi
    phi_xt = AMPLITUDE * WAVE_NUMBER * omega * np.cos(theta)
    return {
        "phi": phi,
        "phi_t": phi_t,
        "phi_x": phi_x,
        "phi_tt": phi_tt,
        "phi_xt": phi_xt,
    }


def evaluate_time_slice(
    *,
    resolution: int,
    time: float,
    omega: float,
) -> dict[str, Any]:
    dx = 2.0 * math.pi / resolution
    x = np.arange(resolution, dtype=np.float64) * dx
    fields = _plane_wave_fields(x, time=time, omega=omega)
    phi = fields["phi"]
    phi_t = fields["phi_t"]
    phi_x = fields["phi_x"]
    phi_tt = fields["phi_tt"]
    phi_xt = fields["phi_xt"]

    bracket = 0.5 * (-phi_t**2 + phi_x**2 + MASS**2 * phi**2)
    t00 = phi_t**2 + bracket
    t01 = -phi_t * phi_x
    t10 = t01
    t11 = phi_x**2 - bracket

    # Time derivatives are analytic; only the spatial flux derivatives are
    # discretized, isolating the intended second-order periodic error.
    dt_t00 = phi_t * phi_tt + phi_x * phi_xt + MASS**2 * phi * phi_t
    dt_t01 = -(phi_tt * phi_x + phi_t * phi_xt)
    divergence_0 = dt_t00 + centered_periodic_difference(t10, dx)
    divergence_1 = dt_t01 + centered_periodic_difference(t11, dx)

    coefficient = omega**2 - WAVE_NUMBER**2 - MASS**2
    e_phi = coefficient * phi
    rhs_0 = e_phi * (-phi_t)
    rhs_1 = e_phi * phi_x
    identity_error_0 = divergence_0 - rhs_0
    identity_error_1 = divergence_1 - rhs_1

    rhs_norm_0 = rms(rhs_0)
    rhs_norm_1 = rms(rhs_1)
    rhs_combined_norm = combined_rms(rhs_0, rhs_1)
    identity_norm_0 = rms(identity_error_0)
    identity_norm_1 = rms(identity_error_1)
    identity_combined_norm = combined_rms(identity_error_0, identity_error_1)

    return {
        "resolution_N": resolution,
        "time": time,
        "dx": dx,
        "equation_residual_coefficient": coefficient,
        "divergence_norms": {
            "nu_0": rms(divergence_0),
            "nu_1": rms(divergence_1),
            "combined": combined_rms(divergence_0, divergence_1),
        },
        "rhs_norms": {
            "nu_0": rhs_norm_0,
            "nu_1": rhs_norm_1,
            "combined": rhs_combined_norm,
        },
        "identity_absolute_error_norms": {
            "nu_0": identity_norm_0,
            "nu_1": identity_norm_1,
            "combined": identity_combined_norm,
        },
        "identity_relative_error_norms": {
            "nu_0": identity_norm_0 / max(rhs_norm_0, RELATIVE_ERROR_FLOOR),
            "nu_1": identity_norm_1 / max(rhs_norm_1, RELATIVE_ERROR_FLOOR),
            "combined": identity_combined_norm
            / max(rhs_combined_norm, RELATIVE_ERROR_FLOOR),
        },
        "_arrays": {
            "divergence_0": divergence_0,
            "divergence_1": divergence_1,
            "rhs_0": rhs_0,
            "rhs_1": rhs_1,
            "identity_error_0": identity_error_0,
            "identity_error_1": identity_error_1,
            "e_phi": e_phi,
            "exact_off_shell_reference": EXACT_OFF_SHELL_COEFFICIENT * phi,
        },
    }


def _aggregate_resolution(
    *,
    resolution: int,
    omega: float,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    raw_rows = [
        evaluate_time_slice(resolution=resolution, time=time, omega=omega)
        for time in TIME_SLICES
    ]
    public_rows = [{key: value for key, value in row.items() if key != "_arrays"} for row in raw_rows]

    def concatenate(name: str) -> np.ndarray:
        return np.concatenate([row["_arrays"][name] for row in raw_rows])

    div_0 = concatenate("divergence_0")
    div_1 = concatenate("divergence_1")
    rhs_0 = concatenate("rhs_0")
    rhs_1 = concatenate("rhs_1")
    err_0 = concatenate("identity_error_0")
    err_1 = concatenate("identity_error_1")
    e_phi = concatenate("e_phi")
    exact_reference = concatenate("exact_off_shell_reference")

    rhs_0_norm = rms(rhs_0)
    rhs_1_norm = rms(rhs_1)
    rhs_combined_norm = combined_rms(rhs_0, rhs_1)
    error_0_norm = rms(err_0)
    error_1_norm = rms(err_1)
    error_combined_norm = combined_rms(err_0, err_1)
    reference_difference = e_phi - exact_reference

    aggregate = {
        "resolution_N": resolution,
        "time_slice_count": len(TIME_SLICES),
        "divergence_norms": {
            "nu_0": rms(div_0),
            "nu_1": rms(div_1),
            "combined": combined_rms(div_0, div_1),
        },
        "rhs_norms": {
            "nu_0": rhs_0_norm,
            "nu_1": rhs_1_norm,
            "combined": rhs_combined_norm,
        },
        "identity_absolute_error_norms": {
            "nu_0": error_0_norm,
            "nu_1": error_1_norm,
            "combined": error_combined_norm,
        },
        "identity_relative_error_norms": {
            "nu_0": error_0_norm / max(rhs_0_norm, RELATIVE_ERROR_FLOOR),
            "nu_1": error_1_norm / max(rhs_1_norm, RELATIVE_ERROR_FLOOR),
            "combined": error_combined_norm
            / max(rhs_combined_norm, RELATIVE_ERROR_FLOOR),
        },
        "exact_residual_reference": {
            "expected_coefficient": EXACT_OFF_SHELL_COEFFICIENT,
            "computed_coefficient": omega**2 - WAVE_NUMBER**2 - MASS**2,
            "coefficient_absolute_error": abs(
                omega**2
                - WAVE_NUMBER**2
                - MASS**2
                - EXACT_OFF_SHELL_COEFFICIENT
            ),
            "field_residual_absolute_error_norm": rms(reference_difference),
            "field_residual_relative_error_norm": rms(reference_difference)
            / max(rms(exact_reference), RELATIVE_ERROR_FLOOR),
        },
    }
    return aggregate, public_rows


def _convergence_orders(values: list[float]) -> list[dict[str, float | int]]:
    return [
        {
            "coarse_N": RESOLUTIONS[index],
            "fine_N": RESOLUTIONS[index + 1],
            "order": math.log(values[index] / values[index + 1], 2.0),
        }
        for index in range(len(values) - 1)
    ]


def build_result(*, captured_at_utc: str = CAPTURED_AT_UTC) -> dict[str, Any]:
    on_aggregates: list[dict[str, Any]] = []
    on_rows: list[dict[str, Any]] = []
    off_aggregates: list[dict[str, Any]] = []
    off_rows: list[dict[str, Any]] = []
    for resolution in RESOLUTIONS:
        aggregate, rows = _aggregate_resolution(
            resolution=resolution,
            omega=OMEGA_ON,
        )
        on_aggregates.append(aggregate)
        on_rows.extend(rows)
        aggregate, rows = _aggregate_resolution(
            resolution=resolution,
            omega=OMEGA_OFF,
        )
        off_aggregates.append(aggregate)
        off_rows.extend(rows)

    on_errors = [row["divergence_norms"]["combined"] for row in on_aggregates]
    off_errors = [
        row["identity_absolute_error_norms"]["combined"] for row in off_aggregates
    ]
    on_orders = _convergence_orders(on_errors)
    off_orders = _convergence_orders(off_errors)
    two_finest_orders = [
        row["order"] for row in [*on_orders[-2:], *off_orders[-2:]]
    ]
    minimum_two_finest_order = min(two_finest_orders)

    finest_on = on_aggregates[-1]
    finest_off = off_aggregates[-1]
    finest_off_relative_error = finest_off["identity_relative_error_norms"][
        "combined"
    ]
    coefficient_error = finest_off["exact_residual_reference"][
        "coefficient_absolute_error"
    ]
    off_to_on_ratio = (
        finest_off["divergence_norms"]["combined"]
        / finest_on["divergence_norms"]["combined"]
    )
    checks = {
        "two_finest_convergence_order_at_least_1_8": (
            minimum_two_finest_order >= MINIMUM_CONVERGENCE_ORDER
        ),
        "finest_combined_off_shell_relative_error_at_most_2_percent": (
            finest_off_relative_error <= MAXIMUM_FINEST_OFF_SHELL_RELATIVE_ERROR
        ),
        "exact_coefficient_error_at_most_1e_12": (
            coefficient_error <= MAXIMUM_COEFFICIENT_ERROR
        ),
        "finest_off_shell_divergence_over_100_times_on_shell": (
            off_to_on_ratio > MINIMUM_OFF_TO_ON_DIVERGENCE_RATIO
        ),
    }
    passed = all(checks.values())
    claim_label = "E-REPRO" if passed else "B-BLOCKED"
    next_target = RESULT_REVIEW_TARGET if passed else THRESHOLD_REPAIR_TARGET

    return {
        "schema_id": f"{CALCULATION_ID}-RESULT",
        "calculation_id": CALCULATION_ID,
        "calculation_status": (
            "executed_pending_result_review" if passed else "executed_blocked"
        ),
        "captured_at_utc": captured_at_utc,
        "question": (
            "Numerically pretest the 1+1-dimensional Minkowski scalar "
            "stress-energy divergence identity with positive and negative controls."
        ),
        "mathematical_convention": {
            "metric_signature": "eta_mu_nu = diag(-1,+1)",
            "action": (
                "S[phi] = integral dtdx [-1/2 partial_mu phi partial^mu phi "
                "- 1/2 m^2 phi^2]"
            ),
            "stress_energy": (
                "T^{mu nu} = partial^mu phi partial^nu phi - eta^{mu nu} "
                "[1/2 partial_alpha phi partial^alpha phi + 1/2 m^2 phi^2]"
            ),
            "field_residual": "E_phi = box phi - m^2 phi",
            "identity": "partial_mu T^{mu nu} = E_phi partial^nu phi",
        },
        "parameters": {
            "amplitude_A": AMPLITUDE,
            "wave_number_k": WAVE_NUMBER,
            "mass_m": MASS,
            "spatial_domain": "[0,2*pi), periodic",
            "time_slices": list(TIME_SLICES),
            "resolutions_N": list(RESOLUTIONS),
            "omega_on": OMEGA_ON,
            "omega_off": OMEGA_OFF,
            "exact_off_shell_coefficient": EXACT_OFF_SHELL_COEFFICIENT,
        },
        "method": {
            "temporal_derivatives": "analytic",
            "spatial_derivatives": (
                "second-order centered periodic finite differences"
            ),
            "component_norm": "RMS sqrt(mean(v_nu^2))",
            "combined_norm": "RMS sqrt(mean(v_0^2 + v_1^2))",
            "relative_error_floor": RELATIVE_ERROR_FLOOR,
        },
        "on_shell": {
            "control_role": "positive conservation control",
            "relative_error_against_zero_formed": False,
            "resolution_aggregates": on_aggregates,
            "time_slice_results": on_rows,
            "combined_absolute_divergence_convergence_orders": on_orders,
        },
        "off_shell": {
            "control_role": "negative nonconservation control",
            "exact_reference": "E_phi = 1.05 * phi",
            "resolution_aggregates": off_aggregates,
            "time_slice_results": off_rows,
            "combined_identity_error_convergence_orders": off_orders,
        },
        "thresholds": {
            "minimum_convergence_order_two_finest_pairs": MINIMUM_CONVERGENCE_ORDER,
            "maximum_finest_combined_off_shell_relative_error": (
                MAXIMUM_FINEST_OFF_SHELL_RELATIVE_ERROR
            ),
            "maximum_exact_coefficient_absolute_error": MAXIMUM_COEFFICIENT_ERROR,
            "minimum_finest_off_to_on_divergence_norm_ratio": (
                MINIMUM_OFF_TO_ON_DIVERGENCE_RATIO
            ),
        },
        "threshold_evidence": {
            "minimum_observed_two_finest_convergence_order": (
                minimum_two_finest_order
            ),
            "finest_combined_off_shell_relative_error": finest_off_relative_error,
            "exact_coefficient_absolute_error": coefficient_error,
            "finest_off_to_on_divergence_norm_ratio": off_to_on_ratio,
        },
        "threshold_checks": checks,
        "all_thresholds_passed": passed,
        "claim": {
            "primary_label": claim_label,
            "claim_status": (
                "generated_pending_result_review"
                if passed
                else "blocked_threshold_failure"
            ),
            "claim_scope": (
                "Level 3 flat-Minkowski scalar divergence-identity toy-model "
                "calculation only"
            ),
            "claim_ceiling_level": 3,
            "next_work_status": next_target,
        },
        "proposed_equation_ids_pending_review": list(
            EQUATION_IDS_PENDING_REVIEW
        ),
        "equation_compendium_edited": False,
        "boundary": {
            "calculation_executed": True,
            "gravity_dynamics_executed": False,
            "einstein_equation_solved": False,
            "curved_spacetime_dynamics_executed": False,
            "source_admissibility_claimed": False,
            "bianchi_compatibility_claimed": False,
            "qft_gr_seam_admissibility_claimed": False,
            "qft_gr_seam_closure_claimed": False,
            "pillar_completion_claimed": False,
            "ccft_resumed": False,
            "ccft_validated": False,
            "master_action_promoted": False,
        },
        "result_review": {"status": "pending", "target": next_target},
    }


def build_manifest(
    *,
    output_path: Path,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> dict[str, Any]:
    guardrail_path = REPO_ROOT / GUARDRAIL_RELATIVE_PATH
    script_path = REPO_ROOT / SCRIPT_RELATIVE_PATH
    return {
        "schema_id": f"{CALCULATION_ID}-MANIFEST",
        "calculation_id": CALCULATION_ID,
        "captured_at_utc": captured_at_utc,
        "guardrail_path": GUARDRAIL_RELATIVE_PATH,
        "guardrail_sha256": sha256_file(guardrail_path),
        "script_path": SCRIPT_RELATIVE_PATH,
        "script_sha256": sha256_file(script_path),
        "test_path": TEST_RELATIVE_PATH,
        "execution_command": EXECUTION_COMMAND,
        "python_version": platform.python_version(),
        "numpy_version": np.__version__,
        "output_path": OUTPUT_RELATIVE_PATH,
        "output_sha256": sha256_file(output_path),
        "canonical_json_contract": {
            "encoding": "UTF-8 without BOM",
            "newline": "LF",
            "object_keys": "sorted",
            "separators": [",", ":"],
            "ensure_ascii": True,
            "allow_nan": False,
            "array_order": "preserved",
            "trailing_newline": "exactly one LF",
        },
        "claim_label": "E-REPRO",
        "claim_scope": "Level 3 Minkowski scalar divergence-identity counts only",
        "result_review_status": "pending",
        "result_review_target": RESULT_REVIEW_TARGET,
        "equation_compendium_status": "proposed_pending_result_review",
    }


def write_artifacts(
    *,
    output_path: Path,
    manifest_path: Path,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> tuple[dict[str, Any], dict[str, Any]]:
    result = build_result(captured_at_utc=captured_at_utc)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes(canonical_json_bytes(result))
    manifest = build_manifest(
        output_path=output_path,
        captured_at_utc=captured_at_utc,
    )
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_bytes(canonical_json_bytes(manifest))
    return result, manifest


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else REPO_ROOT / path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Execute the bounded Minkowski scalar divergence pretest."
    )
    parser.add_argument("--output", type=Path, default=Path(OUTPUT_RELATIVE_PATH))
    parser.add_argument(
        "--manifest", type=Path, default=Path(MANIFEST_RELATIVE_PATH)
    )
    parser.add_argument("--captured-at-utc", default=CAPTURED_AT_UTC)
    args = parser.parse_args(argv)
    output_path = _resolve(args.output)
    manifest_path = _resolve(args.manifest)
    result, manifest = write_artifacts(
        output_path=output_path,
        manifest_path=manifest_path,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        json.dumps(
            {
                "calculation_id": CALCULATION_ID,
                "all_thresholds_passed": result["all_thresholds_passed"],
                "claim_label": result["claim"]["primary_label"],
                "output": OUTPUT_RELATIVE_PATH,
                "output_sha256": manifest["output_sha256"],
                "manifest": MANIFEST_RELATIVE_PATH,
                "result_review_target": result["result_review"]["target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if result["all_thresholds_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
