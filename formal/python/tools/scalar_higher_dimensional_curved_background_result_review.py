from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import subprocess
import sys
import tempfile
from functools import lru_cache
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-09T00:00:00Z"
CALCULATION_ID = (
    "CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-HIGHER-"
    "DIMENSIONAL-CURVED-BACKGROUND-v0"
)
REVIEW_TARGET = (
    "review_calc_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background_v0_result"
)
REVIEW_TARGET_KIND = (
    "scalar_stress_energy_covariant_divergence_identity_higher_dimensional_"
    "curved_background_calculation_result_review"
)
SUCCESS_TARGET = (
    "prepare_scalar_stress_energy_covariant_divergence_identity_multi_"
    "background_robustness_guardrail_packet"
)
FAILURE_TARGET = (
    "diagnose_calc_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background_v0_reproducibility_mismatch"
)
REVIEW_SCHEMA_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_CALCULATION_RESULT_REVIEW_20260709_v0"
)
REVIEW_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_CALCULATION_RESULT_REVIEW_v0"
)
REVIEW_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_RESULT_REVIEW_ACCEPTS_REPRODUCIBLE_FIXED_2PLUS1_"
    "WARPED_BACKGROUND_LEVEL3_SCOPED_E_REPRO_ONLY"
)
REVIEW_STRICT_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_RESULT_REVIEW_ACCEPTS_FIXED_BACKGROUND_FIXED_"
    "COORDINATE_LEVEL3_MATTER_IDENTITY_E_REPRO_NO_GRAVITY_EVOLUTION_NO_"
    "EINSTEIN_SOURCE_NO_BIANCHI_NO_QFT_GR_SEAM_NO_LEVEL4_OR_5_PROMOTION"
)

GUARDRAIL_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
    "HIGHER_DIMENSIONAL_CURVED_BACKGROUND_GUARDRAIL_PACKET_20260709_v1.json"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/toe/calculations/"
    "calc_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background.py"
)
OUTPUT_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "HIGHER-DIMENSIONAL-CURVED-BACKGROUND-v0.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "HIGHER-DIMENSIONAL-CURVED-BACKGROUND-MANIFEST-v0.json"
)
EXECUTION_REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
    "HIGHER_DIMENSIONAL_CURVED_BACKGROUND_CALCULATION_EXECUTION_20260709_v0.json"
)
REVIEW_REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
    "HIGHER_DIMENSIONAL_CURVED_BACKGROUND_CALCULATION_RESULT_REVIEW_"
    "20260709_v0.json"
)
GUARDRAIL_PATH = REPO_ROOT / GUARDRAIL_RELATIVE_PATH
SCRIPT_PATH = REPO_ROOT / SCRIPT_RELATIVE_PATH
OUTPUT_PATH = REPO_ROOT / OUTPUT_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
EXECUTION_REPORT_PATH = REPO_ROOT / EXECUTION_REPORT_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

GUARDRAIL_SCHEMA_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_GUARDRAIL_PACKET_20260709_v1"
)
RESULT_SCHEMA_ID = f"{CALCULATION_ID}-RESULT"
MANIFEST_SCHEMA_ID = f"{CALCULATION_ID}-MANIFEST"
EXECUTION_SCHEMA_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_CALCULATION_EXECUTION_20260709_v0"
)

# Keeping an explicit sentinel check is a fail-safe for future execution
# tranches: review can never accept evidence against an unfrozen chain.
UNFROZEN_HASH_SENTINEL = "__FREEZE_AFTER_EXECUTION_COMMIT__"
EXPECTED_EXECUTION_HASHES = {
    "guardrail_sha256": (
        "e6ce9dfb08364e3fa3a0a3895a3d1b16635348ab2fc7b0490f0b3b6e04db6b96"
    ),
    "script_sha256": (
        "5d43b770a47ec86ccf8a0e09a68d4c1aebf454daea9c471434d288700f57de53"
    ),
    "output_sha256": (
        "755e39e4672ad68e2fbf142d0e2bc9140abb80988e4a330ec3a5fd4ddca859ce"
    ),
    "manifest_sha256": (
        "12791f7844d1c48ea81c647e5d8ee65e32b264592b0101eed875afc7a9d8e5f3"
    ),
    "execution_report_sha256": (
        "e502995f084bb9d7cdcce8141f7c54fce60026660a3c94f393cf2633f0f22dd2"
    ),
}

RESOLUTIONS = (32, 64, 128, 256)
TIMES = (0.0, 0.37, 0.91)
PROFILES = ("on_shell_temporal_mode", "off_shell_x_mode", "off_shell_y_mode")
COMPONENTS = ("nu_t", "nu_x", "nu_y")
A = 0.2
M = 1.0
EPS = 0.2
K = 2.0
ELL = 2.0
OMEGA_X = 1.7
OMEGA_Y = 1.5
EPSILON_R = 1e-12
EPSILON_NORM = 1e-14
EPSILON_CONTROL = 1e-14
NORM_NAME = "coordinate_grid_euclidean_component_rms"

THRESHOLDS = {
    "minimum_two_finest_x_mode_convergence_order": 1.8,
    "minimum_two_finest_y_mode_convergence_order": 1.8,
    "maximum_finest_x_mode_combined_relative_identity_error": 0.02,
    "maximum_finest_y_mode_combined_relative_identity_error": 0.02,
    "maximum_finest_on_shell_combined_absolute_divergence_error": 1e-11,
    "maximum_analytic_profile_residual_reference_error": 1e-12,
    "maximum_metric_compatibility_absolute_error": 1e-12,
    "maximum_curvature_route_absolute_discrepancy": 1e-12,
    "minimum_curvature_peak_absolute_value": 0.49,
    "minimum_curvature_peak_to_peak_variation": 0.8,
    "maximum_flat_limit_absolute_discrepancy": 1e-11,
    "minimum_naive_partial_divergence_error_ratio": 10.0,
    "minimum_omitted_tensor_index_term_error_ratio": 10.0,
    "minimum_omitted_volume_trace_term_error_ratio": 10.0,
    "minimum_flat_geometry_substitution_normalized_discrepancy": 0.02,
    "minimum_incorrect_y_inverse_metric_normalized_discrepancy": 0.02,
    "all_thresholds_required": True,
}

GUARDRAIL_KEYS = {
    "accepted_predecessor", "allowed_operations", "assumptions",
    "background_geometry", "boundary", "calculation_executed",
    "calculation_id", "canonical_json_contract", "captured_at_utc",
    "ccft_lane_status", "claim_ceiling",
    "connection_and_curvature_conventions", "consumed_target",
    "consumed_target_kind", "curvature_verification",
    "e_repro_claimed_by_guardrail", "equation_compendium_row_added",
    "equation_surfaces", "failure_criteria", "flat_limit_control",
    "forbidden_claims", "inputs", "lean_status_wording",
    "negative_controls", "numerical_method", "outputs", "packet_id",
    "packet_result", "question", "readiness_authority",
    "reproduction_command", "required_controls", "revised_at_utc",
    "schema_id", "selected_next_target", "selected_next_target_kind",
    "solution_controls", "status", "strict_packet_result",
    "success_criteria", "success_criteria_definitions", "supersession",
    "threshold_decisions", "units",
}

RESULT_KEYS = {
    "schema_id", "calculation_id", "calculation_status", "captured_at_utc",
    "guardrail", "question", "background_geometry_classification",
    "spacetime_dimension", "background_geometry", "mathematical_convention",
    "analytic_profile_references", "parameters", "method",
    "geometry_safety_verification", "geometry_verification",
    "profile_time_resolution_row_count", "profile_time_resolution_rows",
    "profile_resolution_aggregate_count", "profile_resolution_aggregates",
    "convergence_diagnostics", "flat_limit_control", "negative_controls",
    "thresholds", "threshold_evidence", "threshold_checks",
    "threshold_decisions", "frozen_threshold_count", "all_thresholds_passed",
    "selected_next_target", "claim", "existing_equation_id_reused",
    "equation_compendium_edited", "boundary", "result_review",
}
MANIFEST_KEYS = {
    "schema_id", "calculation_id", "captured_at_utc", "guardrail_path",
    "guardrail_schema_id", "guardrail_sha256", "script_path",
    "script_sha256", "test_path", "execution_command", "environment",
    "output_path", "output_sha256", "execution_report_path",
    "canonical_json_contract", "temporary_output_paths_serialized",
    "wall_clock_timestamp_serialized", "background_geometry_classification",
    "spacetime_dimension", "claim_label", "claim_scope",
    "claim_ceiling_level", "all_thresholds_passed", "result_review_status",
    "result_review_target", "selected_next_target", "boundary",
}
EXECUTION_KEYS = {
    "schema_id", "report_id", "calculation_id", "status", "captured_at_utc",
    "guardrail_revised_at_utc", "consumed_target", "consumed_target_kind",
    "selected_next_target", "selected_next_target_kind", "packet_result",
    "strict_packet_result", "guardrail_path", "guardrail_sha256",
    "calculation_script_path", "calculation_script_sha256",
    "calculation_output_path", "calculation_output_sha256",
    "calculation_manifest_path", "calculation_manifest_sha256",
    "execution_report_path", "five_artifact_chain_prepared_for_independent_review",
    "canonical_json_contract", "execution_command", "environment",
    "background_geometry_classification", "spacetime_dimension", "control_counts",
    "geometry_safety_verification", "geometry_verification",
    "convergence_diagnostics", "flat_limit_control", "negative_controls",
    "thresholds", "threshold_evidence", "threshold_checks",
    "threshold_decisions", "all_thresholds_passed", "claim",
    "existing_equation_id_reused", "equation_compendium_edited", "boundary",
    "full_ToeFormal_aggregate_run_or_upgraded", "ccft_lane_status",
    "lean_status_wording",
}
EXECUTION_CONTROL_COUNTS = {
    "profile_count": 3,
    "time_slice_count": 3,
    "resolution_count": 4,
    "divergence_component_count": 3,
    "profile_time_resolution_row_count": 36,
    "profile_resolution_aggregate_count": 12,
    "curvature_route_count": 2,
    "flat_limit_row_count": 36,
    "negative_control_type_count": 5,
    "negative_control_record_count": 20,
    "frozen_threshold_decision_count": 16,
}


class DuplicateKeyError(ValueError):
    pass


class NonFiniteJSONError(ValueError):
    pass


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


def report_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            payload,
            indent=2,
            sort_keys=True,
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def _reject_constant(token: str) -> None:
    raise NonFiniteJSONError(f"nonfinite JSON token: {token}")


def _object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKeyError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_strict_json_object(path: Path, *, style: str) -> dict[str, Any]:
    raw = path.read_bytes()
    if raw.startswith(b"\xef\xbb\xbf"):
        raise ValueError("UTF-8 BOM is forbidden")
    text = raw.decode("utf-8", errors="strict")
    payload = json.loads(
        text,
        object_pairs_hook=_object_pairs,
        parse_constant=_reject_constant,
    )
    if not isinstance(payload, dict):
        raise ValueError("top-level JSON value must be an object")
    if not _all_finite(payload):
        raise NonFiniteJSONError("decoded JSON contains a nonfinite number")
    expected = canonical_json_bytes(payload) if style == "compact" else report_json_bytes(payload)
    if raw != expected:
        raise ValueError("JSON bytes are not canonical")
    return payload


def _all_finite(value: Any) -> bool:
    if isinstance(value, float):
        return math.isfinite(value)
    if isinstance(value, dict):
        return all(_all_finite(item) for item in value.values())
    if isinstance(value, list):
        return all(_all_finite(item) for item in value)
    return True


def _rms(values: np.ndarray) -> float:
    return float(np.sqrt(np.mean(np.square(values))))


def _combined_rms(values: np.ndarray) -> float:
    return float(np.sqrt(np.mean(np.sum(np.square(values), axis=0))))


def _difference(values: np.ndarray, spacing: float, axis: int) -> np.ndarray:
    return (np.roll(values, -1, axis=axis) - np.roll(values, 1, axis=axis)) / (
        2.0 * spacing
    )


def _geometry(n: int, epsilon: float = EPS) -> dict[str, Any]:
    spacing = 2.0 * math.pi / n
    x = np.arange(n, dtype=np.float64) * spacing
    f = 1.0 + epsilon * np.cos(x)
    fp = -epsilon * np.sin(x)
    fpp = -epsilon * np.cos(x)
    metric = np.zeros((3, 3, n), dtype=np.float64)
    inverse = np.zeros_like(metric)
    metric[0, 0], metric[1, 1], metric[2, 2] = -1.0, 1.0, f * f
    inverse[0, 0], inverse[1, 1], inverse[2, 2] = -1.0, 1.0, f ** -2
    dg = np.zeros((3, 3, 3, n), dtype=np.float64)
    ddg = np.zeros((3, 3, 3, 3, n), dtype=np.float64)
    dg[1, 2, 2] = 2.0 * f * fp
    ddg[1, 1, 2, 2] = 2.0 * (fp * fp + f * fpp)
    return {
        "spacing": spacing, "x": x, "f": f, "fp": fp, "fpp": fpp,
        "metric": metric, "inverse": inverse, "dg": dg, "ddg": ddg,
    }


def _connection_and_derivative(geometry: dict[str, Any]) -> tuple[np.ndarray, np.ndarray]:
    inverse, dg, ddg = geometry["inverse"], geometry["dg"], geometry["ddg"]
    n = inverse.shape[-1]
    gamma = np.zeros((3, 3, 3, n), dtype=np.float64)
    for rho in range(3):
        for mu in range(3):
            for nu in range(3):
                for sigma in range(3):
                    gamma[rho, mu, nu] += 0.5 * inverse[rho, sigma] * (
                        dg[mu, sigma, nu] + dg[nu, sigma, mu] - dg[sigma, mu, nu]
                    )
    dinverse = np.zeros((3, 3, 3, n), dtype=np.float64)
    for kappa in range(3):
        for rho in range(3):
            for sigma in range(3):
                for alpha in range(3):
                    for beta in range(3):
                        dinverse[kappa, rho, sigma] -= (
                            inverse[rho, alpha] * dg[kappa, alpha, beta] * inverse[beta, sigma]
                        )
    dgamma = np.zeros((3, 3, 3, 3, n), dtype=np.float64)
    for kappa in range(3):
        for rho in range(3):
            for mu in range(3):
                for nu in range(3):
                    for sigma in range(3):
                        first = dg[mu, sigma, nu] + dg[nu, sigma, mu] - dg[sigma, mu, nu]
                        second = (
                            ddg[kappa, mu, sigma, nu]
                            + ddg[kappa, nu, sigma, mu]
                            - ddg[kappa, sigma, mu, nu]
                        )
                        dgamma[kappa, rho, mu, nu] += 0.5 * (
                            dinverse[kappa, rho, sigma] * first
                            + inverse[rho, sigma] * second
                        )
    return gamma, dgamma


def _generic_curvature(n: int) -> dict[str, Any]:
    geometry = _geometry(n)
    gamma, dgamma = _connection_and_derivative(geometry)
    riemann = np.zeros((3, 3, 3, 3, n), dtype=np.float64)
    for rho in range(3):
        for sigma in range(3):
            for mu in range(3):
                for nu in range(3):
                    value = dgamma[mu, rho, nu, sigma] - dgamma[nu, rho, mu, sigma]
                    for lam in range(3):
                        value += (
                            gamma[rho, mu, lam] * gamma[lam, nu, sigma]
                            - gamma[rho, nu, lam] * gamma[lam, mu, sigma]
                        )
                    riemann[rho, sigma, mu, nu] = value
    ricci = np.zeros((3, 3, n), dtype=np.float64)
    for sigma in range(3):
        for nu in range(3):
            for rho in range(3):
                ricci[sigma, nu] += riemann[rho, sigma, rho, nu]
    scalar = np.zeros(n, dtype=np.float64)
    for sigma in range(3):
        for nu in range(3):
            scalar += geometry["inverse"][sigma, nu] * ricci[sigma, nu]
    covariant_metric = np.array(geometry["dg"], copy=True)
    for kappa in range(3):
        for mu in range(3):
            for nu in range(3):
                for rho in range(3):
                    covariant_metric[kappa, mu, nu] -= (
                        gamma[rho, kappa, mu] * geometry["metric"][rho, nu]
                        + gamma[rho, kappa, nu] * geometry["metric"][mu, rho]
                    )
    return {
        "geometry": geometry,
        "connection": gamma,
        "ricci": ricci,
        "scalar": scalar,
        "metric_error": float(np.max(np.abs(covariant_metric))),
    }


def _fields(profile: str, x: np.ndarray, y: np.ndarray, time: float) -> dict[str, np.ndarray]:
    zero = np.zeros_like(x)
    if profile == "on_shell_temporal_mode":
        phi = np.full_like(x, A * math.cos(M * time))
        return {
            "phi": phi,
            "t": np.full_like(x, -A * M * math.sin(M * time)),
            "x": zero,
            "y": zero,
            "tt": -(M**2) * phi,
            "tx": zero,
            "ty": zero,
            "xx": zero,
            "yy": zero,
        }
    if profile == "off_shell_x_mode":
        ct, st = math.cos(OMEGA_X * time), math.sin(OMEGA_X * time)
        cx, sx = np.cos(K * x), np.sin(K * x)
        phi = A * ct * cx
        return {
            "phi": phi,
            "t": -A * OMEGA_X * st * cx,
            "x": -A * K * ct * sx,
            "y": zero,
            "tt": -(OMEGA_X**2) * phi,
            "tx": A * OMEGA_X * K * st * sx,
            "ty": zero,
            "xx": -(K**2) * phi,
            "yy": zero,
        }
    if profile == "off_shell_y_mode":
        ct, st = math.cos(OMEGA_Y * time), math.sin(OMEGA_Y * time)
        cy, sy = np.cos(ELL * y), np.sin(ELL * y)
        phi = A * ct * cy
        return {
            "phi": phi,
            "t": -A * OMEGA_Y * st * cy,
            "x": zero,
            "y": -A * ELL * ct * sy,
            "tt": -(OMEGA_Y**2) * phi,
            "tx": zero,
            "ty": A * OMEGA_Y * ELL * st * sy,
            "xx": zero,
            "yy": -(ELL**2) * phi,
        }
    raise ValueError(f"unknown profile: {profile}")


def _explicit_residual(
    profile: str,
    fields: dict[str, np.ndarray],
    f: np.ndarray,
    fp: np.ndarray,
    time: float,
    *,
    wrong_y_factor: bool = False,
) -> np.ndarray:
    if profile == "on_shell_temporal_mode":
        return np.zeros_like(fields["phi"])
    if profile == "off_shell_x_mode":
        n = fields["phi"].shape[0]
        x = np.arange(n, dtype=np.float64)[:, None] * (2.0 * math.pi / n)
        return (
            (OMEGA_X**2 - M**2 - K**2) * fields["phi"]
            - A * K * (fp / f)[:, None] * math.cos(OMEGA_X * time) * np.sin(K * x)
        )
    inverse_y = 1.0 if wrong_y_factor else f[:, None] ** -2
    return (OMEGA_Y**2 - M**2 - ELL**2 * inverse_y) * fields["phi"]


def _assembled_residual(
    fields: dict[str, np.ndarray], f: np.ndarray, fp: np.ndarray
) -> np.ndarray:
    return (
        -fields["tt"]
        + fields["xx"]
        + (fp / f)[:, None] * fields["x"]
        + f[:, None] ** -2 * fields["yy"]
        - M**2 * fields["phi"]
    )


def _slice(n: int, time: float, profile: str, epsilon: float = EPS) -> dict[str, Any]:
    geometry = _geometry(n, epsilon)
    coordinates = geometry["x"]
    x, y = np.meshgrid(coordinates, coordinates, indexing="ij")
    fields = _fields(profile, x, y, time)
    lower = np.stack([fields["t"], fields["x"], fields["y"]])
    lower_t = np.stack([fields["tt"], fields["tx"], fields["ty"]])
    raised = np.array(lower, copy=True)
    raised_t = np.array(lower_t, copy=True)
    raised[0], raised_t[0] = -lower[0], -lower_t[0]
    raised[2] = geometry["f"][:, None] ** -2 * lower[2]
    raised_t[2] = geometry["f"][:, None] ** -2 * lower_t[2]
    contraction = np.sum(lower * raised, axis=0)
    bracket = 0.5 * (contraction + M**2 * fields["phi"] ** 2)
    bracket_t = np.sum(lower_t * raised, axis=0) + M**2 * fields["phi"] * fields["t"]
    stress = np.empty((3, 3, n, n), dtype=np.float64)
    for mu in range(3):
        for nu in range(3):
            stress[mu, nu] = raised[mu] * raised[nu]
    stress[0, 0] += bracket
    stress[1, 1] -= bracket
    stress[2, 2] -= geometry["f"][:, None] ** -2 * bracket
    partial = np.empty((3, n, n), dtype=np.float64)
    for nu in range(3):
        partial[nu] = raised_t[0] * raised[nu] + raised[0] * raised_t[nu]
    partial[0] += bracket_t
    for nu in range(3):
        partial[nu] += _difference(stress[1, nu], geometry["spacing"], 0)
        partial[nu] += _difference(stress[2, nu], geometry["spacing"], 1)
    gamma = _connection_and_derivative(geometry)[0]
    volume = np.zeros_like(partial)
    tensor = np.zeros_like(partial)
    for nu in range(3):
        for mu in range(3):
            for lam in range(3):
                volume[nu] += gamma[mu, mu, lam, :, None] * stress[lam, nu]
                tensor[nu] += gamma[nu, mu, lam, :, None] * stress[mu, lam]
    residual = _explicit_residual(
        profile, fields, geometry["f"], geometry["fp"], time
    )
    assembled = _assembled_residual(fields, geometry["f"], geometry["fp"])
    rhs = residual[None, :, :] * raised
    divergence = partial + volume + tensor
    return {
        "fields": fields,
        "f": geometry["f"],
        "fp": geometry["fp"],
        "raised": raised,
        "divergence": divergence,
        "partial": partial,
        "volume": volume,
        "tensor": tensor,
        "rhs": rhs,
        "identity_error": divergence - rhs,
        "reference_error": float(np.max(np.abs(residual - assembled))),
    }


def _metric_bundle(values: np.ndarray, reference: np.ndarray, *, exact_zero: bool) -> dict[str, Any]:
    error = values - reference
    components: dict[str, Any] = {}
    for index, label in enumerate(COMPONENTS):
        component_zero = exact_zero or not bool(np.any(reference[index] != 0.0))
        absolute = _rms(error[index])
        reference_norm = _rms(reference[index])
        components[label] = {
            "value_rms": _rms(values[index]),
            "reference_rms": reference_norm,
            "absolute_error_rms": absolute,
            "relative_error": None if component_zero else absolute / max(reference_norm, EPSILON_NORM),
            "relative_error_applicable": not component_zero,
            "convergence_status": (
                "not_applicable_exact_zero" if component_zero else "reported_separately"
            ),
        }
    absolute = _combined_rms(error)
    reference_norm = _combined_rms(reference)
    return {
        "components": components,
        "combined": {
            "value_rms": _combined_rms(values),
            "reference_rms": reference_norm,
            "absolute_error_rms": absolute,
            "relative_error": None if exact_zero else absolute / max(reference_norm, EPSILON_NORM),
            "relative_error_applicable": not exact_zero,
            "convergence_status": (
                "not_applicable_exact_zero" if exact_zero else "reported_separately"
            ),
        },
    }


def _row_and_aggregate_recomputation() -> tuple[list[dict[str, Any]], list[dict[str, Any]], dict[tuple[str, int], dict[str, Any]]]:
    rows: list[dict[str, Any]] = []
    aggregates: list[dict[str, Any]] = []
    raw: dict[tuple[str, int], dict[str, Any]] = {}
    for profile in PROFILES:
        for n in RESOLUTIONS:
            slices: list[dict[str, Any]] = []
            for time in TIMES:
                values = _slice(n, time, profile)
                slices.append(values)
                rows.append(
                    {
                        "profile_id": profile,
                        "resolution_N": n,
                        "grid_shape": [n, n],
                        "time_t": time,
                        "delta_x": 2.0 * math.pi / n,
                        "delta_y": 2.0 * math.pi / n,
                        "norm_name": NORM_NAME,
                        "identity_metrics": _metric_bundle(
                            values["divergence"],
                            values["rhs"],
                            exact_zero=profile == "on_shell_temporal_mode",
                        ),
                        "analytic_residual_reference_max_absolute_error": values["reference_error"],
                    }
                )
            stacked = {
                key: np.stack([entry[key] for entry in slices], axis=1)
                for key in ("divergence", "partial", "volume", "tensor", "rhs", "identity_error")
            }
            metrics = _metric_bundle(
                stacked["divergence"],
                stacked["rhs"],
                exact_zero=profile == "on_shell_temporal_mode",
            )
            aggregate = {
                "profile_id": profile,
                "resolution_N": n,
                "grid_shape": [n, n],
                "time_slice_count": len(TIMES),
                "time_slices": list(TIMES),
                "norm_name": NORM_NAME,
                "aggregation": "uniform mean over time,x,y before square root",
                "identity_metrics": metrics,
                "maximum_analytic_residual_reference_absolute_error": max(
                    entry["reference_error"] for entry in slices
                ),
            }
            aggregates.append(aggregate)
            raw[(profile, n)] = {"aggregate": aggregate, **stacked, "slices": slices}
    return rows, aggregates, raw


def _orders(errors: list[float]) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    for index in range(3):
        value = math.log2(errors[index] / errors[index + 1]) if min(errors[index:index + 2]) > 0 else None
        result.append(
            {
                "coarse_N": RESOLUTIONS[index],
                "fine_N": RESOLUTIONS[index + 1],
                "order": value,
                "status": "reported" if value is not None else "not_computable_nonpositive_error",
            }
        )
    return result


def _convergence(raw: dict[tuple[str, int], dict[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for profile in PROFILES:
        profile_result: dict[str, Any] = {}
        for label in (*COMPONENTS, "combined"):
            metrics = [raw[(profile, n)]["aggregate"]["identity_metrics"] for n in RESOLUTIONS]
            selected = [
                item["combined"] if label == "combined" else item["components"][label]
                for item in metrics
            ]
            errors = [item["absolute_error_rms"] for item in selected]
            if not selected[0]["relative_error_applicable"]:
                profile_result[label] = {
                    "errors": errors, "orders": [],
                    "convergence_status": "not_applicable_exact_zero",
                    "minimum_two_finest_order": None,
                    "p_64_128": None, "p_128_256": None, "p_min": None,
                }
            else:
                order_rows = _orders(errors)
                p1, p2 = order_rows[1]["order"], order_rows[2]["order"]
                profile_result[label] = {
                    "errors": errors, "orders": order_rows,
                    "convergence_status": "reported",
                    "minimum_two_finest_order": min(p1, p2),
                    "p_64_128": p1, "p_128_256": p2, "p_min": min(p1, p2),
                }
        result[profile] = profile_result
    return result


def _geometry_recomputation() -> tuple[dict[str, Any], dict[str, Any]]:
    safety_rows: list[dict[str, Any]] = []
    diagnostics: list[dict[str, Any]] = []
    maximum_route = maximum_metric = maximum_connection = maximum_ricci = 0.0
    finest_analytic: np.ndarray | None = None
    for n in RESOLUTIONS:
        generic = _generic_curvature(n)
        geometry = generic["geometry"]
        f, fp, fpp = geometry["f"], geometry["fp"], geometry["fpp"]
        safety_rows.append(
            {
                "resolution_N": n,
                "minimum_warp_factor": float(np.min(f)),
                "maximum_warp_factor": float(np.max(f)),
                "maximum_inverse_y_metric_factor": float(np.max(f ** -2)),
                "minimum_absolute_determinant": float(np.min(f * f)),
                "nonsingular": bool(np.all(f > 0.0)),
            }
        )
        analytic = -2.0 * fpp / f
        finest_analytic = analytic
        absolute = np.abs(generic["scalar"] - analytic)
        included = np.abs(analytic) > EPSILON_R
        excluded = np.flatnonzero(~included).astype(int).tolist()
        expected_gamma = np.zeros_like(generic["connection"])
        expected_gamma[1, 2, 2] = -f * fp
        expected_gamma[2, 1, 2] = fp / f
        expected_gamma[2, 2, 1] = fp / f
        expected_ricci = np.zeros_like(generic["ricci"])
        expected_ricci[1, 1] = -fpp / f
        expected_ricci[2, 2] = -f * fpp
        connection_error = float(np.max(np.abs(generic["connection"] - expected_gamma)))
        ricci_error = float(np.max(np.abs(generic["ricci"] - expected_ricci)))
        maximum_route = max(maximum_route, float(np.max(absolute)))
        maximum_metric = max(maximum_metric, generic["metric_error"])
        maximum_connection = max(maximum_connection, connection_error)
        maximum_ricci = max(maximum_ricci, ricci_error)
        point_rows = []
        for index in range(n):
            is_excluded = index in excluded
            point_rows.append(
                {
                    "x_index": index,
                    "absolute_error": float(absolute[index]),
                    "relative_error": (
                        None if is_excluded else float(absolute[index] / abs(analytic[index]))
                    ),
                    "status": "excluded_near_zero" if is_excluded else "reported",
                }
            )
        diagnostics.append(
            {
                "resolution_N": n,
                "grid_shape": [n, n],
                "maximum_absolute_error": float(np.max(absolute)),
                "maximum_relative_error_away_from_zero": float(
                    np.max(absolute[included] / np.abs(analytic[included]))
                ),
                "relative_error_cutoff_epsilon_R": EPSILON_R,
                "excluded_x_index_count": len(excluded),
                "excluded_x_indices": excluded,
                "excluded_spatial_gridpoint_count": len(excluded) * n,
                "crossing_locations": [math.pi / 2.0, 3.0 * math.pi / 2.0],
                "excluded_crossing_absolute_errors": [float(absolute[index]) for index in excluded],
                "excluded_crossing_relative_errors": [
                    {"x_index": index, "relative_error": None, "status": "excluded_near_zero"}
                    for index in excluded
                ],
                "x_index_error_rows": point_rows,
                "metric_compatibility_max_absolute_error": generic["metric_error"],
                "connection_formula_max_absolute_error": connection_error,
                "ricci_formula_max_absolute_error": ricci_error,
            }
        )
    assert finest_analytic is not None
    safety = {
        "rows": safety_rows,
        "minimum_warp_factor": min(row["minimum_warp_factor"] for row in safety_rows),
        "maximum_warp_factor": max(row["maximum_warp_factor"] for row in safety_rows),
        "maximum_inverse_y_metric_factor": max(
            row["maximum_inverse_y_metric_factor"] for row in safety_rows
        ),
        "minimum_absolute_determinant": min(
            row["minimum_absolute_determinant"] for row in safety_rows
        ),
        "all_frozen_grids_nonsingular": all(row["nonsingular"] for row in safety_rows),
    }
    verification = {
        "analytic_route": {
            "formula": "R(x) = -2*f''(x)/f(x)",
            "substituted_formula": "R(x) = 0.4*cos(x)/(1+0.2*cos(x))",
        },
        "generic_route": {
            "method": (
                "metric,dg,ddg -> Christoffel,dChristoffel -> Riemann -> "
                "Ricci -> scalar index loops"
            ),
            "analytic_curvature_helper_called": False,
        },
        "resolution_diagnostics": diagnostics,
        "maximum_curvature_route_absolute_discrepancy": maximum_route,
        "maximum_metric_compatibility_absolute_error": maximum_metric,
        "maximum_connection_formula_absolute_error": maximum_connection,
        "maximum_ricci_formula_absolute_error": maximum_ricci,
        "nonzero_christoffel_component_formulas": {
            "Gamma^x_yy": "-f*f'", "Gamma^y_xy": "f'/f", "Gamma^y_yx": "f'/f",
        },
        "structurally_allowed_nonzero_christoffel_component_count": 3,
        "scalar_curvature_minimum": float(np.min(finest_analytic)),
        "scalar_curvature_maximum": float(np.max(finest_analytic)),
        "peak_absolute_scalar_curvature": float(np.max(np.abs(finest_analytic))),
        "peak_to_peak_scalar_curvature": float(np.ptp(finest_analytic)),
        "curvature_zero_reporting_is_non_gating": True,
    }
    return safety, verification


def _cartesian_slice(n: int, time: float, profile: str) -> dict[str, np.ndarray]:
    spacing = 2.0 * math.pi / n
    coordinates = np.arange(n, dtype=np.float64) * spacing
    x, y = np.meshgrid(coordinates, coordinates, indexing="ij")
    fields = _fields(profile, x, y, time)
    lower = np.stack([fields["t"], fields["x"], fields["y"]])
    lower_t = np.stack([fields["tt"], fields["tx"], fields["ty"]])
    raised = np.stack([-fields["t"], fields["x"], fields["y"]])
    raised_t = np.stack([-fields["tt"], fields["tx"], fields["ty"]])
    bracket = 0.5 * (np.sum(lower * raised, axis=0) + M**2 * fields["phi"] ** 2)
    bracket_t = np.sum(lower_t * raised, axis=0) + M**2 * fields["phi"] * fields["t"]
    stress = np.empty((3, 3, n, n), dtype=np.float64)
    for mu in range(3):
        for nu in range(3):
            stress[mu, nu] = raised[mu] * raised[nu]
    stress[0, 0] += bracket
    stress[1, 1] -= bracket
    stress[2, 2] -= bracket
    divergence = np.empty((3, n, n), dtype=np.float64)
    for nu in range(3):
        divergence[nu] = raised_t[0] * raised[nu] + raised[0] * raised_t[nu]
    divergence[0] += bracket_t
    for nu in range(3):
        divergence[nu] += _difference(stress[1, nu], spacing, 0)
        divergence[nu] += _difference(stress[2, nu], spacing, 1)
    residual = -fields["tt"] + fields["xx"] + fields["yy"] - M**2 * fields["phi"]
    return {"divergence": divergence, "rhs": residual[None, :, :] * raised}


def _flat_limit_recomputation() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    maximum = 0.0
    for n in RESOLUTIONS:
        for profile in PROFILES:
            for time in TIMES:
                generic = _slice(n, time, profile, epsilon=0.0)
                cartesian = _cartesian_slice(n, time, profile)
                divergence_error = float(np.max(np.abs(generic["divergence"] - cartesian["divergence"])))
                rhs_error = float(np.max(np.abs(generic["rhs"] - cartesian["rhs"])))
                row_max = max(divergence_error, rhs_error)
                maximum = max(maximum, row_max)
                rows.append(
                    {
                        "resolution_N": n,
                        "profile_id": profile,
                        "time_t": time,
                        "divergence_max_absolute_discrepancy": divergence_error,
                        "rhs_max_absolute_discrepancy": rhs_error,
                        "maximum_absolute_discrepancy": row_max,
                    }
                )
    return {
        "method": (
            "generic metric route at epsilon=0 compared with separately coded "
            "Cartesian 2+1 stress-divergence route"
        ),
        "maximum_flat_limit_absolute_discrepancy": maximum,
        "operator_metadata": {
            "coordinate_order": ["t", "x", "y"],
            "operator_coefficients": [-1, 1, 1],
            "connection": 0,
            "curvature": 0,
            "symbolic_metadata_exact": True,
        },
        "rows": rows,
    }


CONTROL_OPERATIONS = {
    "naive_partial_divergence": (
        "omit both Gamma^mu_mu_lambda T^lambda_nu and "
        "Gamma^nu_mu_lambda T^mu_lambda"
    ),
    "omitted_tensor_index_connection_term": (
        "omit only Gamma^nu_mu_lambda T^mu_lambda"
    ),
    "omitted_volume_trace_connection_term": (
        "omit only Gamma^mu_mu_lambda T^lambda_nu"
    ),
    "curved_case_flat_geometry_substitution": (
        "set epsilon=0 in metric,inverse metric,connection,stress,and "
        "divergence while retaining the epsilon=0.2 curved RHS"
    ),
    "incorrect_y_inverse_metric_factor": (
        "replace g^yy=f^-2 by g^yy=1 in the defective y residual and "
        "raised y-gradient while retaining the correct curved references"
    ),
}
CONTROL_MECHANISMS = {
    "naive_partial_divergence": "connection terms are required off shell",
    "omitted_tensor_index_connection_term": (
        "the two connection contributions cancel for the temporal mode"
    ),
    "omitted_volume_trace_connection_term": (
        "the two connection contributions cancel for the temporal mode"
    ),
    "curved_case_flat_geometry_substitution": (
        "flat geometry cannot reproduce the curved analytic reference"
    ),
    "incorrect_y_inverse_metric_factor": (
        "the warped y inverse metric is required by both residual and gradient"
    ),
}


def _controls(raw: dict[tuple[str, int], dict[str, Any]]) -> dict[str, Any]:
    records: list[dict[str, Any]] = []
    by_id: dict[str, list[dict[str, Any]]] = {key: [] for key in CONTROL_OPERATIONS}
    for n in RESOLUTIONS:
        evidence = []
        for profile in ("off_shell_x_mode", "off_shell_y_mode"):
            arrays = raw[(profile, n)]
            defective = _combined_rms(arrays["partial"] - arrays["rhs"])
            correct = _combined_rms(arrays["identity_error"])
            evidence.append(
                {
                    "profile_id": profile,
                    "defective_error": defective,
                    "correct_error": correct,
                    "comparison_value": defective / max(correct, EPSILON_CONTROL),
                }
            )
        value = min(row["comparison_value"] for row in evidence)
        record = {
            "control_id": "naive_partial_divergence", "resolution_N": n,
            "exact_defective_operation": CONTROL_OPERATIONS["naive_partial_divergence"],
            "expected_mechanism": CONTROL_MECHANISMS["naive_partial_divergence"],
            "profile_evidence": evidence,
            "adjudication": "minimum profile-specific error ratio",
            "comparison_value": value, "threshold": 10.0, "comparison": ">=",
            "pass": value >= 10.0,
        }
        records.append(record); by_id[record["control_id"]].append(record)

        temporal = raw[("on_shell_temporal_mode", n)]
        omitted = {
            "omitted_tensor_index_connection_term": temporal["partial"] + temporal["volume"] - temporal["rhs"],
            "omitted_volume_trace_connection_term": temporal["partial"] + temporal["tensor"] - temporal["rhs"],
        }
        for control_id, defect in omitted.items():
            defective = _combined_rms(defect)
            correct = _combined_rms(temporal["identity_error"])
            value = defective / max(correct, EPSILON_CONTROL)
            record = {
                "control_id": control_id, "resolution_N": n,
                "exact_defective_operation": CONTROL_OPERATIONS[control_id],
                "expected_mechanism": CONTROL_MECHANISMS[control_id],
                "profile_evidence": [{
                    "profile_id": "on_shell_temporal_mode",
                    "defective_error": defective, "correct_error": correct,
                    "comparison_value": value,
                }],
                "adjudication": "temporal profile error ratio",
                "comparison_value": value, "threshold": 10.0, "comparison": ">=",
                "pass": value >= 10.0,
            }
            records.append(record); by_id[control_id].append(record)

        evidence = []
        for profile in ("off_shell_x_mode", "off_shell_y_mode"):
            curved = raw[(profile, n)]
            flat = np.stack([_slice(n, time, profile, epsilon=0.0)["divergence"] for time in TIMES], axis=1)
            defective = _combined_rms(flat - curved["rhs"])
            normalization = _combined_rms(curved["rhs"])
            evidence.append({
                "profile_id": profile, "defective_error": defective,
                "normalization_norm": normalization,
                "comparison_value": defective / max(normalization, EPSILON_CONTROL),
            })
        value = min(row["comparison_value"] for row in evidence)
        control_id = "curved_case_flat_geometry_substitution"
        record = {
            "control_id": control_id, "resolution_N": n,
            "exact_defective_operation": CONTROL_OPERATIONS[control_id],
            "expected_mechanism": CONTROL_MECHANISMS[control_id],
            "profile_evidence": evidence,
            "adjudication": "minimum profile-specific normalized discrepancy",
            "comparison_value": value, "threshold": 0.02, "comparison": ">=",
            "pass": value >= 0.02,
        }
        records.append(record); by_id[control_id].append(record)

        curved = raw[("off_shell_y_mode", n)]
        wrong_rows = []
        for time in TIMES:
            item = _slice(n, time, "off_shell_y_mode")
            residual = _explicit_residual(
                "off_shell_y_mode", item["fields"], item["f"], item["fp"], time,
                wrong_y_factor=True,
            )
            wrong_raised = np.array(item["raised"], copy=True)
            wrong_raised[2] = item["fields"]["y"]
            wrong_rows.append(residual[None, :, :] * wrong_raised)
        wrong_rhs = np.stack(wrong_rows, axis=1)
        defective = _combined_rms(wrong_rhs - curved["rhs"])
        identity_error = _combined_rms(curved["divergence"] - wrong_rhs)
        correct = _combined_rms(curved["identity_error"])
        normalization = _combined_rms(curved["rhs"])
        value = defective / max(normalization, EPSILON_CONTROL)
        control_id = "incorrect_y_inverse_metric_factor"
        record = {
            "control_id": control_id, "resolution_N": n,
            "exact_defective_operation": CONTROL_OPERATIONS[control_id],
            "expected_mechanism": CONTROL_MECHANISMS[control_id],
            "profile_evidence": [{
                "profile_id": "off_shell_y_mode", "defective_error": defective,
                "defective_identity_error_against_correct_divergence": identity_error,
                "correct_error": correct, "normalization_norm": normalization,
                "comparison_value": value,
            }],
            "adjudication": "y-profile normalized discrepancy",
            "comparison_value": value, "threshold": 0.02, "comparison": ">=",
            "pass": value >= 0.02,
        }
        records.append(record); by_id[control_id].append(record)
    adjudication: dict[str, Any] = {}
    for control_id, values in by_id.items():
        finest = next(row for row in values if row["resolution_N"] == 256)
        adjudication[control_id] = {
            "resolution_N": 256, "comparison_value": finest["comparison_value"],
            "threshold": finest["threshold"], "pass": finest["pass"],
        }
    adjudication["all_five_negative_controls_passed"] = all(
        value["pass"] for value in adjudication.values()
    )
    return {"record_count": len(records), "records": records, "finest_resolution_adjudication": adjudication}


def _threshold_recomputation(
    aggregates: list[dict[str, Any]],
    convergence: dict[str, Any],
    geometry: dict[str, Any],
    flat: dict[str, Any],
    controls: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, bool]]:
    by_key = {(row["profile_id"], row["resolution_N"]): row for row in aggregates}
    adjudication = controls["finest_resolution_adjudication"]
    evidence = {
        "minimum_two_finest_x_mode_convergence_order": convergence["off_shell_x_mode"]["combined"]["p_min"],
        "minimum_two_finest_y_mode_convergence_order": convergence["off_shell_y_mode"]["combined"]["p_min"],
        "finest_x_mode_combined_relative_identity_error": by_key[("off_shell_x_mode", 256)]["identity_metrics"]["combined"]["relative_error"],
        "finest_y_mode_combined_relative_identity_error": by_key[("off_shell_y_mode", 256)]["identity_metrics"]["combined"]["relative_error"],
        "finest_on_shell_combined_absolute_divergence_error": by_key[("on_shell_temporal_mode", 256)]["identity_metrics"]["combined"]["absolute_error_rms"],
        "maximum_analytic_profile_residual_reference_error": max(
            row["maximum_analytic_residual_reference_absolute_error"] for row in aggregates
        ),
        "maximum_metric_compatibility_absolute_error": geometry["maximum_metric_compatibility_absolute_error"],
        "maximum_curvature_route_absolute_discrepancy": geometry["maximum_curvature_route_absolute_discrepancy"],
        "peak_absolute_scalar_curvature": geometry["peak_absolute_scalar_curvature"],
        "curvature_peak_to_peak_variation": geometry["peak_to_peak_scalar_curvature"],
        "maximum_flat_limit_absolute_discrepancy": flat["maximum_flat_limit_absolute_discrepancy"],
        "naive_partial_divergence_minimum_profile_ratio": adjudication["naive_partial_divergence"]["comparison_value"],
        "omitted_tensor_index_term_error_ratio": adjudication["omitted_tensor_index_connection_term"]["comparison_value"],
        "omitted_volume_trace_term_error_ratio": adjudication["omitted_volume_trace_connection_term"]["comparison_value"],
        "flat_geometry_substitution_minimum_profile_normalized_discrepancy": adjudication["curved_case_flat_geometry_substitution"]["comparison_value"],
        "incorrect_y_inverse_metric_normalized_discrepancy": adjudication["incorrect_y_inverse_metric_factor"]["comparison_value"],
    }
    checks = {
        "minimum_two_finest_x_mode_convergence_order": evidence["minimum_two_finest_x_mode_convergence_order"] >= THRESHOLDS["minimum_two_finest_x_mode_convergence_order"],
        "minimum_two_finest_y_mode_convergence_order": evidence["minimum_two_finest_y_mode_convergence_order"] >= THRESHOLDS["minimum_two_finest_y_mode_convergence_order"],
        "maximum_finest_x_mode_combined_relative_identity_error": evidence["finest_x_mode_combined_relative_identity_error"] <= THRESHOLDS["maximum_finest_x_mode_combined_relative_identity_error"],
        "maximum_finest_y_mode_combined_relative_identity_error": evidence["finest_y_mode_combined_relative_identity_error"] <= THRESHOLDS["maximum_finest_y_mode_combined_relative_identity_error"],
        "maximum_finest_on_shell_combined_absolute_divergence_error": evidence["finest_on_shell_combined_absolute_divergence_error"] <= THRESHOLDS["maximum_finest_on_shell_combined_absolute_divergence_error"],
        "maximum_analytic_profile_residual_reference_error": evidence["maximum_analytic_profile_residual_reference_error"] <= THRESHOLDS["maximum_analytic_profile_residual_reference_error"],
        "maximum_metric_compatibility_absolute_error": evidence["maximum_metric_compatibility_absolute_error"] <= THRESHOLDS["maximum_metric_compatibility_absolute_error"],
        "maximum_curvature_route_absolute_discrepancy": evidence["maximum_curvature_route_absolute_discrepancy"] <= THRESHOLDS["maximum_curvature_route_absolute_discrepancy"],
        "minimum_curvature_peak_absolute_value": evidence["peak_absolute_scalar_curvature"] >= THRESHOLDS["minimum_curvature_peak_absolute_value"],
        "minimum_curvature_peak_to_peak_variation": evidence["curvature_peak_to_peak_variation"] >= THRESHOLDS["minimum_curvature_peak_to_peak_variation"],
        "maximum_flat_limit_absolute_discrepancy": evidence["maximum_flat_limit_absolute_discrepancy"] <= THRESHOLDS["maximum_flat_limit_absolute_discrepancy"],
        "minimum_naive_partial_divergence_error_ratio": evidence["naive_partial_divergence_minimum_profile_ratio"] >= THRESHOLDS["minimum_naive_partial_divergence_error_ratio"],
        "minimum_omitted_tensor_index_term_error_ratio": evidence["omitted_tensor_index_term_error_ratio"] >= THRESHOLDS["minimum_omitted_tensor_index_term_error_ratio"],
        "minimum_omitted_volume_trace_term_error_ratio": evidence["omitted_volume_trace_term_error_ratio"] >= THRESHOLDS["minimum_omitted_volume_trace_term_error_ratio"],
        "minimum_flat_geometry_substitution_normalized_discrepancy": evidence["flat_geometry_substitution_minimum_profile_normalized_discrepancy"] >= THRESHOLDS["minimum_flat_geometry_substitution_normalized_discrepancy"],
        "minimum_incorrect_y_inverse_metric_normalized_discrepancy": evidence["incorrect_y_inverse_metric_normalized_discrepancy"] >= THRESHOLDS["minimum_incorrect_y_inverse_metric_normalized_discrepancy"],
    }
    return evidence, checks


@lru_cache(maxsize=1)
def independent_recompute() -> dict[str, Any]:
    safety, geometry = _geometry_recomputation()
    rows, aggregates, raw = _row_and_aggregate_recomputation()
    convergence = _convergence(raw)
    flat = _flat_limit_recomputation()
    controls = _controls(raw)
    evidence, checks = _threshold_recomputation(
        aggregates, convergence, geometry, flat, controls
    )
    return {
        "geometry_safety_verification": safety,
        "geometry_verification": geometry,
        "profile_time_resolution_rows": rows,
        "profile_resolution_aggregates": aggregates,
        "convergence_diagnostics": convergence,
        "flat_limit_control": flat,
        "negative_controls": controls,
        "threshold_evidence": evidence,
        "threshold_checks": checks,
    }


def _same(observed: Any, expected: Any, *, tolerance: float = 5e-13) -> bool:
    if isinstance(expected, bool) or expected is None or isinstance(expected, str):
        return observed == expected
    if isinstance(expected, (int, float)) and isinstance(observed, (int, float)):
        if not math.isfinite(float(observed)) or not math.isfinite(float(expected)):
            return False
        return math.isclose(float(observed), float(expected), rel_tol=tolerance, abs_tol=tolerance)
    if isinstance(expected, list) and isinstance(observed, list):
        return len(observed) == len(expected) and all(
            _same(left, right, tolerance=tolerance)
            for left, right in zip(observed, expected)
        )
    if isinstance(expected, dict) and isinstance(observed, dict):
        return set(observed) == set(expected) and all(
            _same(observed[key], expected[key], tolerance=tolerance)
            for key in expected
        )
    return observed == expected


def _fragment_hash(value: Any) -> str:
    return sha256_bytes(canonical_json_bytes(value))


def _contains_key(value: Any, forbidden: set[str]) -> bool:
    if isinstance(value, dict):
        return any(key.lower() in forbidden for key in value) or any(
            _contains_key(item, forbidden) for item in value.values()
        )
    if isinstance(value, list):
        return any(_contains_key(item, forbidden) for item in value)
    return False


def _fixed_subprocess_environment() -> dict[str, str]:
    env = dict(os.environ)
    env.update(
        {
            "PYTHONUTF8": "1",
            "PYTHONHASHSEED": "0",
            "TZ": "UTC",
            "LC_ALL": "C.UTF-8",
            "LANG": "C.UTF-8",
        }
    )
    return env


def _run_fresh_execution(directory: Path) -> dict[str, bytes]:
    result = directory / "result.json"
    manifest = directory / "manifest.json"
    report = directory / "execution-report.json"
    environment = _fixed_subprocess_environment()
    calculation = subprocess.run(
        [
            sys.executable,
            "-m",
            (
                "formal.python.toe.calculations."
                "calc_scalar_stress_energy_covariant_divergence_identity_"
                "higher_dimensional_curved_background"
            ),
            "--output", str(result), "--manifest", str(manifest),
        ],
        cwd=REPO_ROOT,
        env=environment,
        check=False,
        capture_output=True,
        text=True,
    )
    if calculation.returncode != 0:
        raise RuntimeError(f"fresh calculation failed: {calculation.stderr}")
    execution = subprocess.run(
        [
            sys.executable,
            "-m",
            (
                "formal.python.tools.scalar_stress_energy_covariant_"
                "divergence_identity_higher_dimensional_curved_background_"
                "calculation_execution_report"
            ),
            "--output", str(result), "--manifest", str(manifest),
            "--guardrail", str(GUARDRAIL_PATH), "--script", str(SCRIPT_PATH),
            "--out", str(report),
        ],
        cwd=REPO_ROOT,
        env=environment,
        check=False,
        capture_output=True,
        text=True,
    )
    if execution.returncode != 0:
        raise RuntimeError(f"fresh execution report failed: {execution.stderr}")
    return {
        "result": result.read_bytes(),
        "manifest": manifest.read_bytes(),
        "execution_report": report.read_bytes(),
    }


def _fresh_subprocess_verification(
    output_path: Path, manifest_path: Path, execution_report_path: Path
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="toe-2plus1-review-a-") as first_name:
        with tempfile.TemporaryDirectory(prefix="toe-2plus1-review-b-") as second_name:
            first = _run_fresh_execution(Path(first_name))
            second = _run_fresh_execution(Path(second_name))
    repository = {
        "result": output_path.read_bytes(),
        "manifest": manifest_path.read_bytes(),
        "execution_report": execution_report_path.read_bytes(),
    }
    keys = ("result", "manifest", "execution_report")
    return {
        "run_count": 2,
        "distinct_temporary_directories": True,
        "fixed_environment": {
            "PYTHONUTF8": "1", "PYTHONHASHSEED": "0", "TZ": "UTC",
            "LC_ALL": "C.UTF-8", "LANG": "C.UTF-8",
        },
        "run_one_sha256": {key: sha256_bytes(first[key]) for key in keys},
        "run_two_sha256": {key: sha256_bytes(second[key]) for key in keys},
        "both_runs_byte_identical": all(first[key] == second[key] for key in keys),
        "fresh_runs_match_repository_artifacts": all(
            first[key] == repository[key] and second[key] == repository[key]
            for key in keys
        ),
    }


def verify_calculation_result(
    *,
    guardrail_path: Path = GUARDRAIL_PATH,
    script_path: Path = SCRIPT_PATH,
    output_path: Path = OUTPUT_PATH,
    manifest_path: Path = MANIFEST_PATH,
    execution_report_path: Path = EXECUTION_REPORT_PATH,
    expected_hashes: dict[str, str] | None = None,
    run_subprocesses: bool = True,
) -> dict[str, Any]:
    """Review the five immutable artifacts without trusting execution flags."""

    mismatch_codes: list[str] = []
    expected = dict(EXPECTED_EXECUTION_HASHES if expected_hashes is None else expected_hashes)
    path_by_hash = {
        "guardrail_sha256": guardrail_path,
        "script_sha256": script_path,
        "output_sha256": output_path,
        "manifest_sha256": manifest_path,
        "execution_report_sha256": execution_report_path,
    }
    actual: dict[str, str | None] = {}
    hash_codes = {
        "guardrail_sha256": "guardrail_hash_mismatch",
        "script_sha256": "calculation_script_hash_mismatch",
        "output_sha256": "calculation_output_hash_mismatch",
        "manifest_sha256": "calculation_manifest_hash_mismatch",
        "execution_report_sha256": "execution_report_hash_mismatch",
    }
    for key, path in path_by_hash.items():
        try:
            actual[key] = sha256_path(path)
        except OSError:
            actual[key] = None
            mismatch_codes.append("artifact_missing")
        if expected.get(key) == UNFROZEN_HASH_SENTINEL or key not in expected:
            mismatch_codes.append("expected_execution_hash_not_frozen")
        elif actual[key] != expected.get(key):
            mismatch_codes.append(hash_codes[key])

    artifacts: dict[str, dict[str, Any] | None] = {
        "guardrail": None, "result": None, "manifest": None, "execution_report": None,
    }
    specifications = {
        "guardrail": (guardrail_path, "report"),
        "result": (output_path, "compact"),
        "manifest": (manifest_path, "compact"),
        "execution_report": (execution_report_path, "report"),
    }
    canonical_checks: dict[str, bool] = {}
    for name, (path, style) in specifications.items():
        try:
            artifacts[name] = load_strict_json_object(path, style=style)
            canonical_checks[name] = True
        except DuplicateKeyError:
            canonical_checks[name] = False
            mismatch_codes.append("duplicate_json_key")
        except NonFiniteJSONError:
            canonical_checks[name] = False
            mismatch_codes.append("nonfinite_json_value")
        except (UnicodeDecodeError, json.JSONDecodeError):
            canonical_checks[name] = False
            mismatch_codes.append("invalid_json_encoding_or_syntax")
        except (OSError, ValueError):
            canonical_checks[name] = False
            mismatch_codes.append("canonicalization_mismatch")

    guardrail = artifacts["guardrail"]
    result = artifacts["result"]
    manifest = artifacts["manifest"]
    execution = artifacts["execution_report"]

    schema_match = False
    if all(item is not None for item in artifacts.values()):
        assert guardrail is not None and result is not None
        assert manifest is not None and execution is not None
        schema_match = (
            guardrail.get("schema_id") == GUARDRAIL_SCHEMA_ID
            and guardrail.get("calculation_id") == CALCULATION_ID
            and set(guardrail) == GUARDRAIL_KEYS
            and guardrail.get("selected_next_target")
            == (
                "execute_calc_scalar_stress_energy_covariant_divergence_identity_"
                "higher_dimensional_curved_background_v0"
            )
            and result.get("schema_id") == RESULT_SCHEMA_ID
            and result.get("calculation_id") == CALCULATION_ID
            and set(result) == RESULT_KEYS
            and manifest.get("schema_id") == MANIFEST_SCHEMA_ID
            and manifest.get("calculation_id") == CALCULATION_ID
            and set(manifest) == MANIFEST_KEYS
            and execution.get("schema_id") == EXECUTION_SCHEMA_ID
            and execution.get("calculation_id") == CALCULATION_ID
            and set(execution) == EXECUTION_KEYS
            and execution.get("control_counts") == EXECUTION_CONTROL_COUNTS
        )
    if not schema_match:
        mismatch_codes.append("schema_or_required_field_mismatch")

    manifest_links = False
    execution_links = False
    if manifest is not None:
        manifest_links = (
            manifest.get("guardrail_sha256") == actual["guardrail_sha256"]
            and manifest.get("script_sha256") == actual["script_sha256"]
            and manifest.get("output_sha256") == actual["output_sha256"]
            and manifest.get("guardrail_path") == GUARDRAIL_RELATIVE_PATH
            and manifest.get("script_path") == SCRIPT_RELATIVE_PATH
            and manifest.get("output_path") == OUTPUT_RELATIVE_PATH
            and manifest.get("execution_report_path") == EXECUTION_REPORT_RELATIVE_PATH
        )
    if not manifest_links:
        mismatch_codes.append("manifest_hash_or_identity_link_mismatch")
    if execution is not None:
        execution_links = (
            execution.get("guardrail_sha256") == actual["guardrail_sha256"]
            and execution.get("calculation_script_sha256") == actual["script_sha256"]
            and execution.get("calculation_output_sha256") == actual["output_sha256"]
            and execution.get("calculation_manifest_sha256") == actual["manifest_sha256"]
            and execution.get("guardrail_path") == GUARDRAIL_RELATIVE_PATH
            and execution.get("calculation_script_path") == SCRIPT_RELATIVE_PATH
            and execution.get("calculation_output_path") == OUTPUT_RELATIVE_PATH
            and execution.get("calculation_manifest_path") == MANIFEST_RELATIVE_PATH
            and execution.get("execution_report_path") == EXECUTION_REPORT_RELATIVE_PATH
        )
    if not execution_links:
        mismatch_codes.append("execution_report_hash_or_identity_link_mismatch")

    independent: dict[str, Any] | None = None
    independent_hashes: dict[str, str] = {}
    try:
        independent = independent_recompute()
        independent_hashes = {
            key: _fragment_hash(value) for key, value in independent.items()
        }
    except Exception:
        mismatch_codes.append("independent_recomputation_failed")

    section_matches: dict[str, bool] = {
        "geometry_safety": False,
        "curvature_and_zero_exclusions": False,
        "profile_time_rows": False,
        "space_time_aggregates": False,
        "convergence": False,
        "flat_limit": False,
        "negative_controls": False,
        "thresholds": False,
    }
    if result is not None and execution is not None and guardrail is not None and independent is not None:
        section_matches["geometry_safety"] = _same(
            result.get("geometry_safety_verification"), independent["geometry_safety_verification"]
        ) and _same(
            execution.get("geometry_safety_verification"), independent["geometry_safety_verification"]
        )
        section_matches["curvature_and_zero_exclusions"] = _same(
            result.get("geometry_verification"), independent["geometry_verification"]
        ) and _same(execution.get("geometry_verification"), independent["geometry_verification"])
        section_matches["profile_time_rows"] = (
            result.get("profile_time_resolution_row_count") == 36
            and _same(result.get("profile_time_resolution_rows"), independent["profile_time_resolution_rows"])
        )
        section_matches["space_time_aggregates"] = (
            result.get("profile_resolution_aggregate_count") == 12
            and _same(result.get("profile_resolution_aggregates"), independent["profile_resolution_aggregates"])
        )
        section_matches["convergence"] = _same(
            result.get("convergence_diagnostics"), independent["convergence_diagnostics"]
        ) and _same(execution.get("convergence_diagnostics"), independent["convergence_diagnostics"])
        section_matches["flat_limit"] = _same(
            result.get("flat_limit_control"), independent["flat_limit_control"]
        ) and _same(execution.get("flat_limit_control"), independent["flat_limit_control"])
        controls_match = _same(
            result.get("negative_controls"), independent["negative_controls"]
        ) and _same(execution.get("negative_controls"), independent["negative_controls"])
        if controls_match:
            adjudication = result["negative_controls"]["finest_resolution_adjudication"]
            control_passes = [adjudication[key]["pass"] for key in CONTROL_OPERATIONS]
            controls_match = (
                adjudication["all_five_negative_controls_passed"] is all(control_passes)
                and all(control_passes)
            )
        section_matches["negative_controls"] = controls_match
        section_matches["thresholds"] = (
            result.get("thresholds") == THRESHOLDS
            and guardrail.get("success_criteria") == THRESHOLDS
            and _same(result.get("threshold_evidence"), independent["threshold_evidence"])
            and result.get("threshold_checks") == independent["threshold_checks"]
            and execution.get("thresholds") == result.get("thresholds")
            and _same(execution.get("threshold_evidence"), independent["threshold_evidence"])
            and execution.get("threshold_checks") == independent["threshold_checks"]
            and len(result.get("threshold_decisions", [])) == 16
            and execution.get("threshold_decisions") == result.get("threshold_decisions")
            and result.get("frozen_threshold_count") == 16
            and result.get("all_thresholds_passed") is True
            and execution.get("all_thresholds_passed") is True
            and len(independent["threshold_checks"]) == 16
            and all(independent["threshold_checks"].values())
        )

    code_by_section = {
        "geometry_safety": "geometry_safety_mismatch",
        "curvature_and_zero_exclusions": "curvature_or_zero_exclusion_mismatch",
        "profile_time_rows": "profile_time_row_mismatch",
        "space_time_aggregates": "space_time_aggregate_mismatch",
        "convergence": "convergence_or_exact_zero_policy_mismatch",
        "flat_limit": "flat_limit_evidence_mismatch",
        "negative_controls": "negative_control_or_combined_masking_mismatch",
        "thresholds": "sixteen_threshold_decision_mismatch",
    }
    for key, matches in section_matches.items():
        if not matches:
            mismatch_codes.append(code_by_section[key])

    analytic_metadata_match = False
    if result is not None:
        analytic_metadata_match = result.get("analytic_profile_references") == {
            "on_shell_temporal_mode": "E_phi=0",
            "off_shell_x_mode": (
                "E_phi=(omega_x^2-m^2-k^2)*phi_x-"
                "A*k*(f'/f)*cos(omega_x*t)*sin(k*x)"
            ),
            "off_shell_y_mode": (
                "E_phi=(omega_y^2-m^2-ell^2/f^2)*phi_y="
                "(1.25-4/f^2)*phi_y"
            ),
        }
    if not analytic_metadata_match:
        mismatch_codes.append("analytic_residual_sign_or_formula_mismatch")

    boundary_match = False
    if result is not None and manifest is not None and execution is not None:
        forbidden_keys = {
            "two_dimensional_einstein_gravity_degenerate",
            "einstein_tensor_identically_zero_in_two_dimensions",
        }
        required_true = {
            "calculation_executed", "two_dimensional_Einstein_degeneracy_not_applicable",
            "einstein_tensor_can_be_nonzero", "background_fixed",
        }
        required_false = {
            "gravity_evolved", "background_metric_evolved", "einstein_equation_solved",
            "Einstein_source_tested", "source_admissibility_claimed",
            "bianchi_compatibility_claimed", "qft_gr_seam_admissibility_claimed",
            "qft_gr_seam_closure_claimed", "quantum_or_renormalized_stress_energy_claimed",
            "multi_background_robustness_claimed", "level_4_or_level_5_claimed",
            "ccft_resumed", "master_action_promoted",
        }
        boundary = result.get("boundary", {})
        boundary_match = (
            boundary == manifest.get("boundary") == execution.get("boundary")
            and boundary.get("spacetime_dimension") == 3
            and all(boundary.get(key) is True for key in required_true)
            and all(boundary.get(key) is False for key in required_false)
            and not any(_contains_key(item, forbidden_keys) for item in (result, manifest, execution))
            and result.get("spacetime_dimension") == manifest.get("spacetime_dimension") == execution.get("spacetime_dimension") == 3
            and result.get("claim", {}).get("claim_ceiling_level") == 3
            and execution.get("claim", {}).get("claim_ceiling_level") == 3
            and execution.get("claim", {}).get("review_accepted") is False
            and execution.get("full_ToeFormal_aggregate_run_or_upgraded") is False
            and result.get("equation_compendium_edited") is False
            and execution.get("equation_compendium_edited") is False
        )
    if not boundary_match:
        mismatch_codes.append("claim_boundary_or_1plus1_degeneracy_mismatch")

    lifecycle_match = False
    if result is not None and manifest is not None and execution is not None:
        lifecycle_match = (
            result.get("calculation_status") == "executed_pending_result_review"
            and result.get("selected_next_target") == REVIEW_TARGET
            and result.get("result_review") == {"status": "pending", "target": REVIEW_TARGET}
            and manifest.get("result_review_target") == REVIEW_TARGET
            and manifest.get("selected_next_target") == REVIEW_TARGET
            and execution.get("status") == "executed_candidate_e_repro_pending_independent_review"
            and execution.get("selected_next_target") == REVIEW_TARGET
            and result.get("claim", {}).get("primary_label") == "E-REPRO"
            and execution.get("claim", {}).get("primary_label") == "E-REPRO"
        )
    if not lifecycle_match:
        mismatch_codes.append("execution_lifecycle_mismatch")

    subprocess_evidence: dict[str, Any] = {
        "run_count": 0,
        "both_runs_byte_identical": False,
        "fresh_runs_match_repository_artifacts": False,
    }
    if run_subprocesses:
        try:
            subprocess_evidence = _fresh_subprocess_verification(
                output_path, manifest_path, execution_report_path
            )
        except (OSError, RuntimeError, subprocess.SubprocessError):
            mismatch_codes.append("fresh_subprocess_execution_failed")
        else:
            if not subprocess_evidence["both_runs_byte_identical"]:
                mismatch_codes.append("fresh_subprocess_byte_mismatch")
            if not subprocess_evidence["fresh_runs_match_repository_artifacts"]:
                mismatch_codes.append("fresh_subprocess_repository_mismatch")
    else:
        mismatch_codes.append("fresh_subprocess_verification_not_run")

    mismatch_codes = list(dict.fromkeys(mismatch_codes))
    accepted = not mismatch_codes
    return {
        "accepted": accepted,
        "primary_claim_label": "E-REPRO" if accepted else "B-BLOCKED",
        "claim_status": (
            "accepted_level_3_scoped_e_repro_fixed_2plus1_warped_background_matter_identity_only"
            if accepted else "blocked_reproducibility_mismatch"
        ),
        "mismatch_codes": mismatch_codes,
        "expected_hashes": expected,
        "actual_hashes": actual,
        "all_five_artifact_hashes_match": actual == expected,
        "canonical_byte_checks": canonical_checks,
        "all_canonical_bytes_match": all(canonical_checks.values()),
        "schema_and_required_fields_match": schema_match,
        "manifest_hash_and_identity_links_match": manifest_links,
        "execution_report_hash_and_identity_links_match": execution_links,
        "independent_recomputation_implementation": (
            "review-local metric/index loops, analytic derivatives, stress divergence, RMS, controls, and gates"
        ),
        "execution_self_adjudication_trusted": False,
        "independent_section_hashes": independent_hashes,
        "independent_section_matches": section_matches,
        "analytic_residual_metadata_match": analytic_metadata_match,
        "all_sixteen_independently_recomputed_thresholds_pass": (
            independent is not None
            and len(independent["threshold_checks"]) == 16
            and all(independent["threshold_checks"].values())
        ),
        "all_five_independently_recomputed_negative_controls_pass": (
            independent is not None
            and independent["negative_controls"]["finest_resolution_adjudication"]["all_five_negative_controls_passed"]
        ),
        "claim_boundary_and_2plus1_language_match": boundary_match,
        "execution_lifecycle_match": lifecycle_match,
        "fresh_subprocess_reproduction": subprocess_evidence,
        "selected_next_target": SUCCESS_TARGET if accepted else FAILURE_TARGET,
    }


def build_review_report(**verification_arguments: Any) -> dict[str, Any]:
    verification = verify_calculation_result(**verification_arguments)
    accepted = verification["accepted"]
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": (
            "accepted_level_3_scoped_e_repro"
            if accepted
            else "blocked_reproducibility_mismatch"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": REVIEW_TARGET,
        "consumed_target_kind": REVIEW_TARGET_KIND,
        "selected_next_target": verification["selected_next_target"],
        "selected_next_target_kind": (
            "scalar_stress_energy_covariant_divergence_identity_multi_"
            "background_robustness_guardrail_packet"
            if accepted
            else "scientific_reproducibility_mismatch_diagnosis"
        ),
        "packet_result": REVIEW_OUTCOME if accepted else "B-BLOCKED",
        "strict_packet_result": REVIEW_STRICT_OUTCOME if accepted else "B-BLOCKED",
        "review_result": REVIEW_OUTCOME if accepted else "B-BLOCKED",
        "strict_review_result": REVIEW_STRICT_OUTCOME if accepted else "B-BLOCKED",
        "calculation_id": CALCULATION_ID,
        "five_artifact_chain": {
            "guardrail_path": GUARDRAIL_RELATIVE_PATH,
            "calculation_script_path": SCRIPT_RELATIVE_PATH,
            "calculation_output_path": OUTPUT_RELATIVE_PATH,
            "calculation_manifest_path": MANIFEST_RELATIVE_PATH,
            "execution_report_path": EXECUTION_REPORT_RELATIVE_PATH,
            "expected_hashes": verification["expected_hashes"],
            "all_hashes_match": verification["all_five_artifact_hashes_match"],
        },
        "verification": verification,
        "claim": {
            "primary_label": "E-REPRO" if accepted else "B-BLOCKED",
            "claim_status": verification["claim_status"],
            "claim_ceiling_level": 3,
            "claim_scope": (
                "one fixed-background fixed-coordinate 2+1 scalar matter identity calculation only"
            ),
            "review_accepted": accepted,
            "equation_surface_status_unchanged": True,
            "additional_scoped_evidence_pointer_authorized": accepted,
        },
        "boundary": {
            "spacetime_dimension": 3,
            "two_dimensional_Einstein_degeneracy_not_applicable": True,
            "einstein_tensor_can_be_nonzero": True,
            "background_fixed": True,
            "gravity_evolved": False,
            "Einstein_source_tested": False,
            "bianchi_compatibility_claimed": False,
            "qft_gr_seam_admissibility_claimed": False,
            "qft_gr_seam_closure_claimed": False,
            "multi_background_robustness_claimed": False,
            "level_4_or_level_5_claimed": False,
            "ccft_resumed": False,
            "master_action_promoted": False,
            "full_ToeFormal_aggregate_run_or_upgraded": False,
        },
        "determinism": {
            "wall_clock_time_serialized": False,
            "temporary_paths_serialized": False,
            "fresh_subprocess_count": verification[
                "fresh_subprocess_reproduction"
            ]["run_count"],
            "fixed_capture_time": CAPTURED_AT_UTC,
            "report_encoding": "UTF-8 without BOM; sorted indented JSON; exactly one LF",
        },
    }


def write_review_report(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(report_json_bytes(payload))


def review_report_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Independently review the fixed 2+1 warped-background scalar "
            "covariant stress-divergence identity execution."
        )
    )
    parser.add_argument("--guardrail", type=Path, default=GUARDRAIL_PATH)
    parser.add_argument("--script", type=Path, default=SCRIPT_PATH)
    parser.add_argument("--output", type=Path, default=OUTPUT_PATH)
    parser.add_argument("--manifest", type=Path, default=MANIFEST_PATH)
    parser.add_argument("--execution-report", type=Path, default=EXECUTION_REPORT_PATH)
    parser.add_argument("--out", type=Path, default=REVIEW_REPORT_PATH)
    args = parser.parse_args(argv)
    payload = build_review_report(
        guardrail_path=args.guardrail,
        script_path=args.script,
        output_path=args.output,
        manifest_path=args.manifest,
        execution_report_path=args.execution_report,
    )
    write_review_report(args.out, payload)
    print(
        json.dumps(
            {
                "accepted": payload["verification"]["accepted"],
                "claim_label": payload["claim"]["primary_label"],
                "mismatch_codes": payload["verification"]["mismatch_codes"],
                "selected_next_target": payload["selected_next_target"],
                "review_report": REVIEW_REPORT_RELATIVE_PATH,
            },
            sort_keys=True,
        )
    )
    return 0 if payload["verification"]["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(review_report_main())
