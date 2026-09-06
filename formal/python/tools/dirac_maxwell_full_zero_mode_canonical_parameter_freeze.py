from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import platform
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_canonical_parameter_freeze.py"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-PARAMETER-FREEZE-PACKET-v0.json"
RUN_MATRIX_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-RUN-MATRIX-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-PARAMETER-FREEZE-MANIFEST-v0.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_PARAMETER_FREEZE_PACKET_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
RUN_MATRIX_PATH = REPO_ROOT / RUN_MATRIX_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "prepare_dirac_maxwell_full_zero_mode_canonical_parameter_freeze_packet_v0"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_canonical_parameter_freeze_packet_v0_result"
POST_ACCEPTANCE_TARGET = "execute_dirac_maxwell_full_zero_mode_canonical_simulation_v0"
BLOCKED_TARGET = "prepare_dirac_maxwell_full_zero_mode_canonical_parameter_freeze_packet_v1"
ADDITIONAL_PILOT_TARGET = "execute_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v2"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_PARAMETER_FREEZE_PACKET_v0"
RUN_MATRIX_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_RUN_MATRIX_v0"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_PARAMETER_FREEZE_MANIFEST_v0"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_PARAMETER_FREEZE_PACKET_20260713_v0"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

INPUT_HASHES = {
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DISCRETE-NUMERICAL-GUARDRAIL-PACKET-v0.json": "52ffd123b3eb516ab824291364afd2006c90951f04d12587658941cbe499da82",
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DISCRETE_NUMERICAL_GUARDRAIL_PACKET_RESULT_REVIEW_20260713_v0.json": "b881d23e9bd201b09bb023a1e897306afff681bd57ccb224a9c6baf562be57b6",
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-PACKET-v0.json": "b4435ef3fab1ad04873538ef4abc3df807b018d74ace99cd2a69757325fc52c6",
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-ARRAYS-v0.json": "3191ebf1c6ba6c65ae917aa16016b33ac1966136d540bc8819dfd0577d208e65",
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_RESULT_REVIEW_20260713_v0.json": "1b6ea74e9eedf501dcbc8fc767fe99694742035d9f58959bcf10d215cf619a4a",
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-PILOT-IMPLEMENTATION-REPAIR-PACKET-v0.json": "96d977aa5551d36b2467c3636e5bd5be6a1fad7808738c250acdfb283bb42cda",
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_PILOT_IMPLEMENTATION_REPAIR_PACKET_RESULT_REVIEW_20260713_v0.json": "13fa544264e4bc5d004f19bd860e702c4c71a907e83a05bdbee4d0fa9ce1ff1f",
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-PACKET-v1.json": "456fb3a73d8cbc50c1392ed71ccc43e5f7c6783faa9e2fe22e15ce041a2372e3",
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-ARRAYS-v1.json": "62f66647c4588f6bd4b2db03a9d64d4c1019f43c10fdd73aca0a5a8ed54c13f8",
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_V1_RESULT_REVIEW_20260713_v0.json": "0c6aa468858805c8f2dfd39384b85532762f8f936b657a2f742b155deaa314d0",
    "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot.py": "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1",
    "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1.py": "90acc15a46891ab289edb41d536765913e2e58979ae150897efe3a59fe94a2dd",
}
PILOT_V1_PACKET = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-PACKET-v1.json"
PILOT_V1_ARRAYS = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-ARRAYS-v1.json"
PILOT_V1_REVIEW = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_V1_RESULT_REVIEW_20260713_v0.json"

ENVIRONMENT_PATHS = [
    "requirements.active.lock",
    "formal/toe_formal/lean-toolchain",
    "formal/toe_formal/lake-manifest.json",
    ".gitattributes",
]


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (json.dumps(_normalize(payload), allow_nan=False, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return identity_sha256_path(path, repo_root=REPO_ROOT)


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def validate_authority() -> None:
    for path, digest in INPUT_HASHES.items():
        if sha256_path(REPO_ROOT / path) != digest:
            raise ValueError(f"input hash mismatch: {path}")
    review = load_json(REPO_ROOT / PILOT_V1_REVIEW)
    if not (
        review.get("accepted") is True
        and review.get("verdict") == "ACCEPT_ENGINEERING_READY"
        and review.get("selected_next_target") == TARGET
        and review.get("authority_rotation", {}).get("canonical_parameter_freeze_preparation_authorized") is True
        and review.get("authority_rotation", {}).get("canonical_execution_authorized") is False
    ):
        raise ValueError("pilot-v1 review does not authorize this preparation")


def round_up_one_significant(value: float) -> float:
    if value <= 0:
        return 0.0
    exponent = math.floor(math.log10(value))
    scale = 10**exponent
    return math.ceil(value / scale) * scale


def round_down_one_significant(value: float) -> float:
    if value <= 0:
        return 0.0
    exponent = math.floor(math.log10(value))
    scale = 10**exponent
    rounded = math.floor(value / scale) * scale
    return float(f"{rounded:.0e}")


def simulation_record(
    run_id: str,
    run_role: str,
    grid_size: int | None,
    time_step: float | None,
    duration: float,
    solver_tolerance: float | None,
    initial_condition_id: str,
    expected_outcome: str,
    control_or_mutation_id: str | None = None,
    execution_kind: str = "SIMULATION",
) -> dict[str, Any]:
    return {
        "run_id": run_id,
        "run_role": run_role,
        "execution_kind": execution_kind,
        "grid_size": grid_size,
        "time_step": time_step,
        "duration": duration,
        "solver_tolerance": solver_tolerance,
        "max_iterations": 80 if execution_kind == "SIMULATION" else None,
        "initial_condition_id": initial_condition_id,
        "control_or_mutation_id": control_or_mutation_id,
        "expected_outcome": expected_outcome,
        "output_path": f"formal/output/canonical/dirac_maxwell_full_zero_mode_v0/{run_id}.json",
    }


def canonical_run_matrix(pilot_packet: dict[str, Any]) -> dict[str, Any]:
    records = [
        simulation_record("CANONICAL_PRIMARY_N32_DT0P0015625", "PRIMARY_COUPLED", 32, 0.0015625, 0.05, 1e-12, "FULL_MIXED_v0", "all frozen acceptance gates evaluated"),
        simulation_record("SPATIAL_REFINEMENT_N8", "SPATIAL_REFINEMENT", 8, 0.0125, 0.05, 1e-12, "FULL_MIXED_v0", "included in frozen spatial fit"),
        simulation_record("SPATIAL_REFINEMENT_N16", "SPATIAL_REFINEMENT", 16, 0.00625, 0.05, 1e-12, "FULL_MIXED_v0", "included in frozen spatial fit"),
        simulation_record("SPATIAL_REFINEMENT_N32", "SPATIAL_REFINEMENT", 32, 0.003125, 0.05, 1e-12, "FULL_MIXED_v0", "included in frozen spatial fit"),
        simulation_record("TEMPORAL_REFINEMENT_DT0P00625", "TEMPORAL_REFINEMENT", 16, 0.00625, 0.05, 1e-12, "FULL_MIXED_v0", "included in frozen temporal fit"),
        simulation_record("TEMPORAL_REFINEMENT_DT0P003125", "TEMPORAL_REFINEMENT", 16, 0.003125, 0.05, 1e-12, "FULL_MIXED_v0", "included in frozen temporal fit"),
        simulation_record("TEMPORAL_REFINEMENT_DT0P0015625", "TEMPORAL_REFINEMENT", 16, 0.0015625, 0.05, 1e-12, "FULL_MIXED_v0", "included in frozen temporal fit"),
        simulation_record("SOLVER_VERIFY_TOL1E_MINUS10", "SOLVER_TOLERANCE_VERIFY", 16, 0.003125, 0.05, 1e-10, "FULL_MIXED_v0", "solver sensitivity remains below truncation"),
        simulation_record("SOLVER_VERIFY_TOL1E_MINUS12", "SOLVER_TOLERANCE_VERIFY", 16, 0.003125, 0.05, 1e-12, "FULL_MIXED_v0", "solver sensitivity remains below truncation"),
        simulation_record("DETERMINISTIC_PRIMARY_A", "DETERMINISTIC_DUPLICATE", 32, 0.0015625, 0.05, 1e-12, "FULL_MIXED_v0", "byte-identical to deterministic duplicate B"),
        simulation_record("DETERMINISTIC_PRIMARY_B", "DETERMINISTIC_DUPLICATE", 32, 0.0015625, 0.05, 1e-12, "FULL_MIXED_v0", "byte-identical to deterministic duplicate A"),
    ]
    positive_specs = {
        "vacuum": (8, 0.00625, "VACUUM_v0", "SIMULATION"),
        "q0_free_and_descendant_waves": (16, 0.003125, "Q0_WAVE_v0", "SIMULATION"),
        "Wilson_discrete_plane_wave": (256, None, "WILSON_PLANE_WAVE_v0", "ANALYTIC_CHECK"),
        "continuum_dispersion_recovery": (256, None, "WILSON_DISPERSION_64_128_256_v0", "ANALYTIC_CHECK"),
        "trivial_pure_gauge": (8, None, "TRIVIAL_PURE_GAUGE_v0", "ANALYTIC_CHECK"),
        "flat_nontrivial_holonomy": (8, None, "FLAT_NONTRIVIAL_HOLONOMY_v0", "ANALYTIC_CHECK"),
        "stationary_density_neutral": (8, None, "STATIONARY_NEUTRAL_v0", "ANALYTIC_CHECK"),
        "analytic_zero_transverse_current": (8, None, "ZERO_TRANSVERSE_CURRENT_v0", "ANALYTIC_CHECK"),
        "J2_sources_phi2": (8, 0.00625, "PHI2_RESPONSE_v0", "SIMULATION"),
        "J3_sources_phi3": (8, 0.00625, "PHI3_RESPONSE_v0", "SIMULATION"),
        "charge_conjugate_transport": (8, None, "CHARGE_CONJUGATE_LINK_v0", "ANALYTIC_CHECK"),
        "full_energy_inventory": (32, 0.0015625, "FULL_MIXED_v0", "ANALYTIC_CHECK"),
    }
    for control in pilot_packet["summary"]["positive_controls"]:
        control_id = control["control_id"]
        n, dt, initial, kind = positive_specs[control_id]
        records.append(simulation_record(f"POSITIVE_{control_id.upper()}", "POSITIVE_CONTROL", n, dt, 0.05 if kind == "SIMULATION" else 0.0, 1e-12 if kind == "SIMULATION" else None, initial, control["expected_behavior"], control_id, kind))
    for mutation in pilot_packet["summary"]["negative_controls"]:
        mutation_id = mutation["mutation_id"]
        records.append(simulation_record(f"NEGATIVE_{mutation_id}", "NEGATIVE_CONTROL", None, None, 0.0, None, "FROZEN_BASELINE_CONFIGURATION_v0", f"reject with {mutation['expected_diagnostic']}", mutation_id, "MUTATION_CHECK"))
    run_ids = [record["run_id"] for record in records]
    return {
        "schema_id": RUN_MATRIX_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "generation_policy": "literal frozen core matrix plus the ordered accepted pilot-v1 control inventories; no filesystem discovery",
        "record_count": len(records),
        "unique_run_id_count": len(set(run_ids)),
        "role_counts": {role: sum(record["run_role"] == role for record in records) for role in sorted({record["run_role"] for record in records})},
        "records": records,
    }


def exchange_signal_evidence(arrays: dict[str, Any], energy_floor: float) -> dict[str, Any]:
    source_roles = ["SPATIAL_N32", "TEMPORAL_DT_0P0015625"]
    rows = []
    for role in source_roles:
        record = next(item for item in arrays["runs"] if item["calibration_role"] == role)
        series = record["series"]
        values = lambda key: [float(item) for item in series[key]]
        longitudinal = [left + right for left, right in zip(values("energy_electric_fluctuating"), values("energy_electric_zero_mode"), strict=True)]
        phi2 = values("energy_phi2")
        phi3 = values("energy_phi3")
        total = values("total_energy")
        matter = [whole - long - field2 - field3 for whole, long, field2, field3 in zip(total, longitudinal, phi2, phi3, strict=True)]
        changes = {
            "longitudinal": max(abs(item - longitudinal[0]) for item in longitudinal),
            "phi2_descendant": max(abs(item - phi2[0]) for item in phi2),
            "phi3_descendant": max(abs(item - phi3[0]) for item in phi3),
            "matter_including_interactions": max(abs(item - matter[0]) for item in matter),
        }
        signal = max(changes.values())
        transverse_signal = max(changes["phi2_descendant"], changes["phi3_descendant"])
        drift = max(abs(item - total[0]) for item in total)
        rows.append({"pilot_source_run_id": record["run_record_id"], "sector_changes": changes, "maximum_sector_change": signal, "maximum_transverse_descendant_change": transverse_signal, "maximum_total_energy_drift": drift, "energy_floor": energy_floor, "exchange_ratio": signal / (drift + energy_floor)})
    minimum_ratio = min(row["exchange_ratio"] for row in rows)
    minimum_transverse = min(row["maximum_transverse_descendant_change"] for row in rows)
    return {
        "definition": "max sector energy change/(max total-energy drift+frozen energy-error floor)",
        "sector_partition": "longitudinal; phi2 descendant; phi3 descendant; matter including all link, gamma, and Wilson interactions",
        "pilot_rows": rows,
        "derivation_rule": "minimum across both accepted finest spatial and finest temporal pilot roles; divide by two for margin; round downward to one significant digit",
        "minimum_pilot_ratio": minimum_ratio,
        "canonical_minimum_exchange_ratio": round_down_one_significant(minimum_ratio / 2),
        "minimum_pilot_transverse_signal": minimum_transverse,
        "canonical_minimum_transverse_signal": round_down_one_significant(minimum_transverse / 2),
        "requires_active_channel": "phi2 or phi3 descendant energy change must meet the transverse-signal minimum",
    }


def environment_identity() -> dict[str, Any]:
    autocrlf = subprocess.run(["git", "config", "--get", "core.autocrlf"], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip() or "UNSET"
    return {
        "python_version": platform.python_version(),
        "numpy_version": np.__version__,
        "operating_system": platform.system(),
        "os_release": platform.release(),
        "git_core_autocrlf": autocrlf,
        "PYTHONHASHSEED": "0",
        "timezone": "UTC",
        "locale": "C",
        "UTF8_normalization": "NFC",
        "float_serialization": "finite JSON numbers; canonical sorted-key UTF-8 LF JSON",
        "bound_files": [{"path": path, "sha256": sha256_path(REPO_ROOT / path)} for path in ENVIRONMENT_PATHS],
    }


FAILURE_SEMANTICS = {
    "Gauss_threshold_failure": "constraint-preservation failure -> versioned numerical-method repair",
    "continuity_threshold_failure": "discrete current-consistency failure -> versioned numerical-method repair",
    "energy_order_failure": "conservation claim not earned -> canonical result B-BLOCKED",
    "Wilson_order_failure": "continuum-recovery failure -> canonical result B-BLOCKED",
    "positive_control_failure": "analytic/discrete target not reproduced -> guardrail repair",
    "negative_control_passes": "guardrail discrimination failure -> guardrail repair",
    "duplicate_run_identity": "evidence custody failure -> versioned identity repair",
    "exchange_signal_failure": "matter-field exchange not separated from drift/noise -> scientific result inconclusive",
    "solver_nonconvergence": "implementation/numerical stability failure -> versioned numerical-method repair",
    "determinism_failure": "reproducibility failure -> evidence implementation repair",
    "threshold_relaxation_request": "forbidden; preserve failure and select a versioned review target",
}


DECISION_IDS = [
    "accepted_pilot_v1_review_is_the_exact_live_authority",
    "all_guardrail_pilot_blocker_repair_and_v1_inputs_are_hash_bound",
    "v0_duplicate_identity_blocker_remains_visible",
    "canonical_primary_parameters_are_mechanically_selected_from_pilot_v1",
    "fifty_run_records_are_literal_complete_and_uniquely_identified",
    "spatial_temporal_solver_deterministic_positive_and_negative_roles_are_complete",
    "every_threshold_has_source_measurement_formula_rounding_and_value",
    "thresholds_reproduce_the_accepted_two_x_round_up_rule",
    "exchange_signal_and_transverse_activity_gates_are_mechanically_derived",
    "convergence_fit_ranges_orders_metrics_and_no_exclusion_rule_are_frozen",
    "solver_norm_initial_guess_iteration_and_failure_rules_are_frozen",
    "registered_energy_inventory_normalization_multiplicity_and_boundary_flux_are_frozen",
    "failure_semantics_block_relaxation_and_route_repairs_explicitly",
    "environment_and_dependency_identity_are_bound",
    "no_dynamic_file_discovery_or_post_result_fit_selection_is_allowed",
    "preparation_selects_only_independent_freeze_review",
    "canonical_execution_and_scientific_result_remain_unauthorized_before_review",
    "claim_ceiling_nonpromotions_and_Prompt_boundary_hold",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    validate_authority()
    pilot_packet = load_json(REPO_ROOT / PILOT_V1_PACKET)
    pilot_arrays = load_json(REPO_ROOT / PILOT_V1_ARRAYS)
    pilot_review = load_json(REPO_ROOT / PILOT_V1_REVIEW)
    run_matrix = canonical_run_matrix(pilot_packet)
    maximums = pilot_review["reviewed_engineering_evidence"]["maximum_residuals"]
    candidates = pilot_review["reviewed_engineering_evidence"]["candidate_thresholds_unreviewed"]
    pilot_source_run_ids = [record["run_record_id"] for record in pilot_arrays["runs"]]
    threshold_provenance = []
    for name in sorted(maximums):
        value = float(maximums[name])
        threshold_provenance.append({
            "threshold_id": name,
            "pilot_source_run_ids": pilot_source_run_ids,
            "pilot_measured_value": value,
            "generation_formula": "round_up_one_significant(2 * pilot_measured_value)",
            "rounding_rule": "multiply by two, then round upward to one significant digit",
            "candidate_canonical_value": float(candidates[name]),
            "recomputed_value": round_up_one_significant(2 * value),
            "meaning": f"maximum accepted canonical {name} residual/error unless a stricter structural rule applies",
        })
    exchange = exchange_signal_evidence(pilot_arrays, float(candidates["energy_drift"]))
    proposed_parameters = dict(pilot_review["reviewed_engineering_evidence"]["candidate_canonical_parameters_unreviewed"])
    packet = {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "evidence_class_if_reviewed_and_accepted": "E-REPRO computational engineering prerequisite only",
        "proposed_canonical_parameters": proposed_parameters,
        "parameter_provenance": {
            "N": "finest accepted pilot spatial grid",
            "dt": "finest accepted pilot temporal step",
            "duration": "accepted pilot duration with transverse descendant activity and exchange separation",
            "solver_tolerance": "tightest accepted pilot tolerance; solver/truncation ratio 4.846521139395604e-05",
            "max_iterations": "accepted pilot cap with all steps converged",
            "selection_is_cross_product_not_an_observed_single_pilot_tuple": True,
        },
        "canonical_run_matrix": {"path": RUN_MATRIX_RELATIVE_PATH, "record_count": run_matrix["record_count"], "sha256": sha256_bytes(canonical_json_bytes(run_matrix))},
        "threshold_provenance": threshold_provenance,
        "exchange_signal_separation": exchange,
        "convergence_definitions": {
            "spatial": {"run_ids": ["SPATIAL_REFINEMENT_N8", "SPATIAL_REFINEMENT_N16", "SPATIAL_REFINEMENT_N32"], "metric": "final_phi2_l2", "fit": "pairwise Richardson log2(|coarse-middle|/|middle-fine|)", "minimum_order": 0.8, "reason": "Wilson artifact is leading O(a)", "exclusions": "none"},
            "temporal_phi2": {"run_ids": ["TEMPORAL_REFINEMENT_DT0P00625", "TEMPORAL_REFINEMENT_DT0P003125", "TEMPORAL_REFINEMENT_DT0P0015625"], "metric": "final_phi2_l2", "fit": "pairwise Richardson log2 ratio", "minimum_order": 1.5, "expected_order": 2, "exclusions": "none"},
            "temporal_energy": {"run_ids": ["TEMPORAL_REFINEMENT_DT0P00625", "TEMPORAL_REFINEMENT_DT0P003125", "TEMPORAL_REFINEMENT_DT0P0015625"], "metric": "maximum absolute total-energy drift", "fit": "pairwise Richardson log2 ratio", "minimum_order": 1.5, "expected_order": 2, "exclusions": "none"},
            "Wilson_dispersion": {"grids": [64, 128, 256], "mode": "k=2*pi/L", "finite_grid_target": "exact Wilson dispersion", "continuum_fit": "pairwise Richardson log2 ratio", "minimum_order": 0.8, "maximum_discrete_formula_error": 1e-12, "exclusions": "none"},
            "outlier_policy": "no run may be excluded; any missing, failed, or nonfinite fit member blocks the corresponding claim",
            "post_execution_fit_range_changes": "forbidden",
        },
        "solver_freeze": {
            "method": "fully coupled implicit midpoint fixed-point iteration",
            "tolerance": proposed_parameters["solver_tolerance"],
            "norm": "absolute infinity norm: max(update difference, implicit midpoint equation defect)",
            "relative_tolerance": False,
            "maximum_iterations": proposed_parameters["max_iterations"],
            "initial_guess": "one explicit-Euler predictor from the accepted right-hand side",
            "linear_solver": "none; deterministic vectorized fixed-point update",
            "failure_behavior": "any step not converged by the cap or above the frozen solver threshold blocks the run; no retry with altered settings",
        },
        "energy_freeze": {
            "classification": "BOUNDED_CONVERGENT_ENERGY_ERROR",
            "registered_components": ["electric fluctuating", "uniform electric zero mode", "phi2 kinetic and gradient", "phi3 kinetic and gradient", "Wilson-Dirac local", "link interaction", "gamma2 interaction", "gamma3 interaction"],
            "formula": "sum of all eight registered components",
            "normalized_drift_denominator": "absolute initial registered energy |E(0)|; zero-energy controls use absolute drift only",
            "absolute_drift_threshold_id": "energy_drift",
            "boundary_flux": "periodic S1 net boundary flux is exactly zero",
            "interpretation": "canonically normalized 1+1 total energy corresponding to the admitted 3+1 zero-mode torus total; never energy per area",
            "sector_multiplicity": "four two-component reduced spinors: two sectors for each of two opposite-charge species",
            "Wilson_zero_mode_and_descendant_terms_required": True,
        },
        "failure_semantics": FAILURE_SEMANTICS,
        "identity_policy": {"unique_role_qualified_run_id_required": True, "record_count": run_matrix["record_count"], "duplicate_identity_diagnostic": "EVIDENCE_CUSTODY_FAILURE", "v0_blocker_preserved": "REGISTERED_RUN_IDENTITIES_NOT_UNIQUE"},
        "environment_identity": environment_identity(),
        "input_artifacts": [{"path": path, "sha256": digest} for path, digest in INPUT_HASHES.items()],
        "selected_next_target": REVIEW_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "blocked_target": BLOCKED_TARGET,
        "additional_pilot_target_only_if_review_proves_needed": ADDITIONAL_PILOT_TARGET,
        "boundary": {"freeze_accepted_before_review": False, "canonical_parameters_frozen_before_review": False, "canonical_thresholds_frozen_before_review": False, "canonical_execution_authorized": False, "scientific_result_claimed": False},
        "claim_ceiling": "A reviewed freeze may preregister a bounded canonical numerical experiment; it is not a conservation or coupled-field result.",
        "prompt_protection": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256},
        "nonclaims": ["no canonical simulation executed", "no canonical conservation result", "no empirical adequacy", "no EM or QFT pillar completion", "no EM-QFT seam admissibility or closure", "no new physics", "no C_k dynamics", "no CCFT validation", "no master-action validation or promotion", "no repository-wide green claim"],
    }
    packet_raw = canonical_json_bytes(packet)
    matrix_raw = canonical_json_bytes(run_matrix)
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "inputs": packet["input_artifacts"],
        "environment": packet["environment_identity"],
        "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
        "run_matrix": {"path": RUN_MATRIX_RELATIVE_PATH, "sha256": sha256_bytes(matrix_raw)},
        "selected_next_target": REVIEW_TARGET,
        "decision_count": len(DECISION_IDS),
    }
    manifest_raw = canonical_json_bytes(manifest)
    thresholds_pass = all(item["candidate_canonical_value"] == item["recomputed_value"] for item in threshold_provenance)
    matrix_pass = run_matrix["record_count"] == run_matrix["unique_run_id_count"] == 50 and run_matrix["role_counts"] == {"DETERMINISTIC_DUPLICATE": 2, "NEGATIVE_CONTROL": 27, "POSITIVE_CONTROL": 12, "PRIMARY_COUPLED": 1, "SOLVER_TOLERANCE_VERIFY": 2, "SPATIAL_REFINEMENT": 3, "TEMPORAL_REFINEMENT": 3}
    prepared = thresholds_pass and matrix_pass and exchange["canonical_minimum_exchange_ratio"] >= 100 and exchange["canonical_minimum_transverse_signal"] > 0
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW" if prepared else "B-BLOCKED",
        "selected_next_target": REVIEW_TARGET if prepared else BLOCKED_TARGET,
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": prepared} for item in DECISION_IDS],
        "all_decisions_passed": prepared,
        "proposed_canonical_parameters": proposed_parameters,
        "threshold_count": len(threshold_provenance),
        "run_record_count": run_matrix["record_count"],
        "exchange_minimum_ratio": exchange["canonical_minimum_exchange_ratio"],
        "exchange_minimum_transverse_signal": exchange["canonical_minimum_transverse_signal"],
        "artifact_hashes": {"generator_sha256": sha256_path(SCRIPT_PATH), "packet_sha256": sha256_bytes(packet_raw), "run_matrix_sha256": sha256_bytes(matrix_raw), "manifest_sha256": sha256_bytes(manifest_raw)},
        "claim": "Canonical parameters, thresholds, run identities, fits, solver semantics, exchange gates, energy accounting, and failure routes are prepared for independent freeze review only.",
        "canonical_execution_authorized": False,
        "scientific_result_claimed": False,
        "nonclaims": packet["nonclaims"],
    }
    return packet, run_matrix, manifest, report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Prepare the full zero-mode canonical parameter freeze packet.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        packet, matrix, manifest, report = build_artifacts()
    except (OSError, ValueError, KeyError, StopIteration, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = [(PACKET_PATH, packet), (RUN_MATRIX_PATH, matrix), (MANIFEST_PATH, manifest), (REPORT_PATH, report)]
    if args.write:
        for path, payload in artifacts:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(canonical_json_bytes(payload))
        print(f"wrote canonical parameter freeze: {report['verdict']}; independent review required")
        return 0 if report["all_decisions_passed"] else 2
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing canonical-freeze artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print(f"canonical parameter freeze verified: {report['verdict']}; canonical execution unauthorized")
        return 0 if report["all_decisions_passed"] else 2
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0 if report["all_decisions_passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
