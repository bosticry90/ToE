from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.toe.calculations.calc_scalar_stress_energy_divergence_identity_minkowski import (
    CALCULATION_ID,
    RESOLUTIONS,
    TIME_SLICES,
    build_result as rebuild_calculation_result,
    canonical_json_bytes as calculation_canonical_json_bytes,
)


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-09T00:00:00Z"

GUARDRAIL_TARGET = (
    "prepare_scalar_qft_gr_source_contract_flat_limit_pretest_guardrail_packet"
)
EXECUTION_TARGET = (
    "execute_calc_scalar_stress_energy_divergence_identity_minkowski_v0"
)
REVIEW_TARGET = (
    "review_calc_scalar_stress_energy_divergence_identity_minkowski_v0_result"
)
THRESHOLD_REPAIR_TARGET = (
    "repair_calc_scalar_stress_energy_divergence_identity_minkowski_v0_"
    "threshold_failure"
)

GUARDRAIL_OUTCOME = (
    "SCALAR_QFT_GR_SOURCE_CONTRACT_FLAT_LIMIT_PRETEST_GUARDRAIL_PACKET_"
    "PREPARED_AUTHORIZES_MINKOWSKI_STRESS_ENERGY_DIVERGENCE_IDENTITY_"
    "CALCULATION_ONLY"
)
GUARDRAIL_STRICT_OUTCOME = (
    "SCALAR_QFT_GR_SOURCE_CONTRACT_FLAT_LIMIT_PRETEST_GUARDRAIL_PACKET_"
    "PREPARED_LEVEL_3_PRETEST_ONLY_NO_GRAVITY_DYNAMICS_NO_SOURCE_"
    "ADMISSIBILITY_NO_SEAM_ADMISSIBILITY_OR_MASTER_ACTION_PROMOTION"
)
EXECUTION_OUTCOME = (
    "SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_MINKOWSKI_CALCULATION_EXECUTED_"
    "PASSES_LEVEL_3_ON_SHELL_OFF_SHELL_AND_CONVERGENCE_THRESHOLDS_PENDING_"
    "RESULT_REVIEW"
)
EXECUTION_STRICT_OUTCOME = (
    "SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_MINKOWSKI_CALCULATION_EXECUTED_"
    "SCOPED_E_REPRO_PENDING_REVIEW_NO_GRAVITY_DYNAMICS_NO_SOURCE_"
    "ADMISSIBILITY_NO_SEAM_ADMISSIBILITY_OR_MASTER_ACTION_PROMOTION"
)
REVIEW_OUTCOME = (
    "SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_MINKOWSKI_CALCULATION_RESULT_"
    "REVIEW_ACCEPTS_LEVEL_3_REPRODUCIBLE_DIVERGENCE_IDENTITY_PRETEST_ONLY"
)
REVIEW_STRICT_OUTCOME = (
    "SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_MINKOWSKI_CALCULATION_RESULT_"
    "REVIEW_ACCEPTS_SCOPED_E_REPRO_NO_GRAVITY_DYNAMICS_NO_SOURCE_"
    "ADMISSIBILITY_NO_QFT_GR_SEAM_ADMISSIBILITY_OR_MASTER_ACTION_PROMOTION"
)
CURVED_RETEST_GUARDRAIL_TARGET = (
    "prepare_bounded_curved_space_scalar_qft_gr_source_contract_retest_"
    "guardrail_packet"
)
REPRODUCIBILITY_REPAIR_TARGET = (
    "repair_calc_scalar_stress_energy_divergence_identity_minkowski_"
    "reproducibility_mismatch"
)

GUARDRAIL_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_QFT_GR_SOURCE_CONTRACT_FLAT_LIMIT_PRETEST_GUARDRAIL_PACKET_"
    "20260709_v0.json"
)
READINESS_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
)
CALCULATION_OUTPUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-MINKOWSKI-v0.json"
)
CALCULATION_MANIFEST_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-MINKOWSKI-MANIFEST-v0.json"
)
EXECUTION_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_MINKOWSKI_CALCULATION_"
    "EXECUTION_20260709_v0.json"
)
CALCULATION_SCRIPT_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "toe"
    / "calculations"
    / "calc_scalar_stress_energy_divergence_identity_minkowski.py"
)
REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_MINKOWSKI_CALCULATION_"
    "RESULT_REVIEW_20260709_v0.json"
)

EXPECTED_EXECUTION_HASHES = {
    "guardrail_sha256": (
        "a1f29ff370431de8ca1d4e977e00d659a70353ae142472121ea9f44128f07da5"
    ),
    "script_sha256": (
        "0eaa19affa8a74084444247c9a04b6997b632490b5411bf436fc3461028547eb"
    ),
    "output_sha256": (
        "c93f2324c735bf2a06ba9a83c3fc022be87b7d00fb5bf2010b8010c2715f480e"
    ),
    "manifest_sha256": (
        "7e2eee401b84c4a8c8dd20c8d54eb6bbba9f16b4e832d53bff6bd7612cd53605"
    ),
    "execution_report_sha256": (
        "f1a6b0de45a830b9146cc06b3dbf086ab9bf95f53ae55a5bb80e969df9d53f3f"
    ),
}

EQUATION_IDS = (
    "EQ-QFT-SCALAR-STRESS-ENERGY-v0",
    "EQ-QFT-SCALAR-STRESS-DIVERGENCE-IDENTITY-v0",
)


def canonical_json_bytes(payload: Any) -> bytes:
    """Platform-independent byte contract for new calculation artifacts."""

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


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def build_guardrail_payload() -> dict[str, Any]:
    readiness_hash = sha256_path(READINESS_PATH)
    return {
        "schema_id": (
            "SCALAR_QFT_GR_SOURCE_CONTRACT_FLAT_LIMIT_PRETEST_GUARDRAIL_"
            "PACKET_20260709_v0"
        ),
        "packet_id": (
            "SCALAR_QFT_GR_SOURCE_CONTRACT_FLAT_LIMIT_PRETEST_GUARDRAIL_"
            "PACKET_v0"
        ),
        "status": "prepared_authorizes_execution_only",
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": GUARDRAIL_TARGET,
        "consumed_target_kind": (
            "scalar_qft_gr_source_contract_flat_limit_pretest_guardrail_packet"
        ),
        "selected_next_target": EXECUTION_TARGET,
        "selected_next_target_kind": (
            "scalar_stress_energy_divergence_identity_minkowski_calculation_"
            "execution"
        ),
        "packet_result": GUARDRAIL_OUTCOME,
        "strict_packet_result": GUARDRAIL_STRICT_OUTCOME,
        "readiness_authority": {
            "artifact_id": "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0",
            "path": (
                "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
            ),
            "sha256": readiness_hash,
            "status": "accepted_current_science_sprint_readiness_authority",
        },
        "question": (
            "Does a second-order periodic spatial discretization reproduce the "
            "flat 1+1-dimensional scalar stress-energy divergence identity for "
            "on-shell and deliberately off-shell plane waves?"
        ),
        "inputs": {
            "field": "phi(t,x) = A cos(k x - omega t)",
            "amplitude_A": 0.2,
            "wave_number_k": 2.0,
            "mass_m": 1.0,
            "spatial_domain": "x in [0, 2*pi), periodic",
            "time_slices": [0.0, 0.37, 0.91],
            "spatial_resolutions_N": [64, 128, 256, 512],
            "omega_on_definition": "sqrt(k^2 + m^2) = sqrt(5)",
            "omega_off_definition": "1.1 * sqrt(5)",
            "off_shell_exact_coefficient": 1.05,
            "off_shell_exact_residual": "E_phi = 1.05 * phi",
        },
        "equation_surfaces": {
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
            "divergence_identity": (
                "partial_mu T^{mu nu} = E_phi partial^nu phi"
            ),
            "proposed_equation_ids_pending_review": list(EQUATION_IDS),
            "equation_compendium_edited": False,
        },
        "assumptions": [
            "fixed 1+1-dimensional Minkowski spacetime",
            "real scalar field",
            "periodic spatial boundary",
            "analytic plane-wave temporal derivatives",
            "smooth field evaluated at fixed time slices",
            "no Einstein-equation solve and no curved-spacetime dynamics",
        ],
        "units": {
            "convention": "dimensionless numerical test units with c = hbar = 1",
            "coordinate_and_parameter_consistency": (
                "k, m, omega, x, and t use one internally consistent natural-unit "
                "normalization"
            ),
            "physical_parameter_inference_allowed": False,
        },
        "allowed_operations": [
            "evaluate the analytic plane-wave field and temporal derivatives",
            "apply second-order centered periodic spatial differences",
            "evaluate both nu=0 and nu=1 divergence components",
            "compute component and combined RMS norms",
            "estimate convergence orders over the two finest refinement pairs",
            "compare the off-shell residual coefficient with the exact value 1.05",
            "write deterministic result, manifest, and execution-report artifacts",
        ],
        "forbidden_claims": [
            "gravity dynamics",
            "GR source admissibility",
            "Bianchi compatibility",
            "QFT-GR seam admissibility or closure",
            "pillar completion",
            "CCFT validation or resumption",
            "master-action canonicalization, promotion, or closure",
        ],
        "numerical_method": {
            "temporal_derivatives": "analytic",
            "spatial_derivatives": (
                "second-order centered periodic finite differences"
            ),
            "component_rms_norm": "sqrt(mean(v_nu^2))",
            "combined_rms_norm": "sqrt(mean(v_0^2 + v_1^2))",
            "on_shell_error_policy": (
                "report absolute divergence norms; no relative error against zero"
            ),
            "off_shell_identity_relative_error": (
                "norm(divergence - E_phi * partial^nu phi) / "
                "max(norm(E_phi * partial^nu phi), 1e-14)"
            ),
        },
        "success_criteria": {
            "minimum_convergence_order_two_finest_pairs": 1.8,
            "maximum_finest_combined_off_shell_relative_error": 0.02,
            "maximum_exact_coefficient_absolute_error": 1e-12,
            "minimum_finest_off_to_on_divergence_norm_ratio": 100.0,
            "all_thresholds_required": True,
        },
        "failure_criteria": {
            "any_threshold_failure": True,
            "primary_claim_label": "B-BLOCKED",
            "selected_repair_target": THRESHOLD_REPAIR_TARGET,
            "failed_artifacts_preserved": True,
            "threshold_changes_require_new_versioned_guardrail": True,
        },
        "outputs": {
            "result": (
                "formal/output/CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-"
                "MINKOWSKI-v0.json"
            ),
            "manifest": (
                "formal/output/CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-"
                "MINKOWSKI-MANIFEST-v0.json"
            ),
            "execution_report": (
                "formal/docs/release/SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_"
                "MINKOWSKI_CALCULATION_EXECUTION_20260709_v0.json"
            ),
        },
        "claim_ceiling": {
            "claim_ladder_level": 3,
            "classification": "toy-model demonstration",
            "execution_e_repro_status": "pending_result_review",
            "not_gravity_dynamics": True,
            "not_source_admissibility": True,
            "not_seam_admissibility": True,
        },
        "reproduction_command": (
            "python -m formal.python.toe.calculations."
            "calc_scalar_stress_energy_divergence_identity_minkowski"
        ),
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
        "calculation_executed": False,
        "e_repro_claimed": False,
        "equation_compendium_row_added": False,
        "ccft_lane_status": "paused_upstream_prerequisites",
        "lean_status_wording": (
            "scoped Lean passed; full ToeFormal aggregate not run / not upgraded"
        ),
    }


def validate_guardrail_payload(payload: dict[str, Any]) -> None:
    required_interface = {
        "question",
        "inputs",
        "equation_surfaces",
        "assumptions",
        "units",
        "allowed_operations",
        "forbidden_claims",
        "success_criteria",
        "failure_criteria",
        "outputs",
        "claim_ceiling",
        "reproduction_command",
    }
    if not required_interface.issubset(payload):
        raise ValueError("guardrail is missing required sprint interface fields")
    if payload.get("selected_next_target") != EXECUTION_TARGET:
        raise ValueError("guardrail does not select the bounded execution target")
    if payload["claim_ceiling"].get("claim_ladder_level") != 3:
        raise ValueError("guardrail claim ceiling must remain Level 3")
    if payload["equation_surfaces"].get("equation_compendium_edited") is not False:
        raise ValueError("guardrail cannot edit the equation compendium")
    canonical_json_bytes(payload)


def build_execution_report() -> dict[str, Any]:
    result = json.loads(CALCULATION_OUTPUT_PATH.read_text(encoding="utf-8"))
    manifest = json.loads(CALCULATION_MANIFEST_PATH.read_text(encoding="utf-8"))
    if result.get("all_thresholds_passed") is not True:
        raise ValueError("calculation thresholds did not pass")
    if not all(result.get("threshold_checks", {}).values()):
        raise ValueError("one or more threshold checks are false")
    if manifest.get("output_sha256") != sha256_path(CALCULATION_OUTPUT_PATH):
        raise ValueError("manifest output hash differs")
    evidence = result["threshold_evidence"]
    return {
        "schema_id": (
            "SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_MINKOWSKI_CALCULATION_"
            "EXECUTION_20260709_v0"
        ),
        "calculation_id": result["calculation_id"],
        "status": "executed_pending_result_review",
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": EXECUTION_TARGET,
        "consumed_target_kind": (
            "scalar_stress_energy_divergence_identity_minkowski_calculation_"
            "execution"
        ),
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": (
            "scalar_stress_energy_divergence_identity_minkowski_calculation_"
            "result_review"
        ),
        "packet_result": EXECUTION_OUTCOME,
        "strict_packet_result": EXECUTION_STRICT_OUTCOME,
        "calculation_output_path": (
            "formal/output/CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-"
            "MINKOWSKI-v0.json"
        ),
        "calculation_output_sha256": sha256_path(CALCULATION_OUTPUT_PATH),
        "calculation_manifest_path": (
            "formal/output/CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-"
            "MINKOWSKI-MANIFEST-v0.json"
        ),
        "calculation_manifest_sha256": sha256_path(CALCULATION_MANIFEST_PATH),
        "guardrail_sha256": manifest["guardrail_sha256"],
        "script_sha256": manifest["script_sha256"],
        "canonical_json_contract": manifest["canonical_json_contract"],
        "control_counts": {
            "on_shell_time_resolution_rows": len(
                result["on_shell"]["time_slice_results"]
            ),
            "off_shell_time_resolution_rows": len(
                result["off_shell"]["time_slice_results"]
            ),
            "time_slice_count": len(result["parameters"]["time_slices"]),
            "resolution_count": len(result["parameters"]["resolutions_N"]),
            "divergence_component_count": 2,
        },
        "threshold_evidence": evidence,
        "threshold_checks": result["threshold_checks"],
        "all_thresholds_passed": True,
        "claim": {
            "primary_label": "E-REPRO",
            "claim_status": "generated_pending_result_review",
            "claim_ceiling_level": 3,
            "claim_scope": (
                "flat-Minkowski scalar stress-energy divergence identity toy "
                "calculation only"
            ),
        },
        "proposed_equation_ids_pending_review": result[
            "proposed_equation_ids_pending_review"
        ],
        "equation_compendium_edited": False,
        "boundary": result["boundary"],
        "ccft_lane_status": "paused_upstream_prerequisites",
        "lean_status_wording": (
            "scoped Lean passed; full ToeFormal aggregate not run / not upgraded"
        ),
    }


def _reject_nonfinite_json(token: str) -> None:
    raise ValueError(f"non-finite JSON token: {token}")


def _load_strict_json(path: Path) -> dict[str, Any]:
    payload = json.loads(
        path.read_text(encoding="utf-8"),
        parse_constant=_reject_nonfinite_json,
    )
    if not isinstance(payload, dict):
        raise ValueError("top-level JSON value must be an object")
    return payload


def verify_calculation_result(
    *,
    guardrail_path: Path = GUARDRAIL_REPORT_PATH,
    script_path: Path = CALCULATION_SCRIPT_PATH,
    output_path: Path = CALCULATION_OUTPUT_PATH,
    manifest_path: Path = CALCULATION_MANIFEST_PATH,
    execution_report_path: Path = EXECUTION_REPORT_PATH,
) -> dict[str, Any]:
    mismatch_codes: list[str] = []
    actual_hashes = {
        "guardrail_sha256": sha256_path(guardrail_path),
        "script_sha256": sha256_path(script_path),
        "output_sha256": sha256_path(output_path),
        "manifest_sha256": sha256_path(manifest_path),
        "execution_report_sha256": sha256_path(execution_report_path),
    }
    hash_code_by_key = {
        "guardrail_sha256": "guardrail_hash_mismatch",
        "script_sha256": "script_hash_mismatch",
        "output_sha256": "output_hash_mismatch",
        "manifest_sha256": "manifest_hash_mismatch",
        "execution_report_sha256": "execution_report_hash_mismatch",
    }
    for key, expected in EXPECTED_EXECUTION_HASHES.items():
        if actual_hashes[key] != expected:
            mismatch_codes.append(hash_code_by_key[key])

    result: dict[str, Any] | None = None
    manifest: dict[str, Any] | None = None
    execution_report: dict[str, Any] | None = None
    try:
        result = _load_strict_json(output_path)
        manifest = _load_strict_json(manifest_path)
        execution_report = _load_strict_json(execution_report_path)
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError):
        mismatch_codes.append("schema_mismatch")

    canonical_bytes_match = False
    independent_regeneration_match = False
    if result is not None and manifest is not None:
        try:
            canonical_bytes_match = (
                output_path.read_bytes() == calculation_canonical_json_bytes(result)
                and manifest_path.read_bytes()
                == calculation_canonical_json_bytes(manifest)
            )
        except (TypeError, ValueError):
            canonical_bytes_match = False
        if not canonical_bytes_match:
            mismatch_codes.append("canonicalization_mismatch")

        required_result_fields = {
            "schema_id",
            "calculation_id",
            "parameters",
            "on_shell",
            "off_shell",
            "threshold_evidence",
            "threshold_checks",
            "all_thresholds_passed",
            "claim",
            "boundary",
        }
        required_manifest_fields = {
            "schema_id",
            "calculation_id",
            "guardrail_sha256",
            "script_sha256",
            "output_sha256",
            "canonical_json_contract",
            "result_review_target",
        }
        if (
            not required_result_fields.issubset(result)
            or not required_manifest_fields.issubset(manifest)
            or result.get("calculation_id") != CALCULATION_ID
            or manifest.get("calculation_id") != CALCULATION_ID
        ):
            mismatch_codes.append("schema_mismatch")

        try:
            count_match = (
                result["parameters"]["time_slices"] == list(TIME_SLICES)
                and result["parameters"]["resolutions_N"] == list(RESOLUTIONS)
                and len(result["on_shell"]["time_slice_results"]) == 12
                and len(result["off_shell"]["time_slice_results"]) == 12
                and len(result["on_shell"]["resolution_aggregates"]) == 4
                and len(result["off_shell"]["resolution_aggregates"]) == 4
            )
        except (KeyError, TypeError):
            count_match = False
        if not count_match:
            mismatch_codes.append("count_mismatch")

        expected_check_keys = {
            "two_finest_convergence_order_at_least_1_8",
            "finest_combined_off_shell_relative_error_at_most_2_percent",
            "exact_coefficient_error_at_most_1e_12",
            "finest_off_shell_divergence_over_100_times_on_shell",
        }
        checks = result.get("threshold_checks", {})
        threshold_match = (
            result.get("all_thresholds_passed") is True
            and set(checks) == expected_check_keys
            and all(checks.values())
            and result.get("claim", {}).get("primary_label") == "E-REPRO"
            and result.get("claim", {}).get("claim_ceiling_level") == 3
        )
        if not threshold_match:
            mismatch_codes.append("threshold_mismatch")

        if (
            manifest.get("guardrail_sha256") != actual_hashes["guardrail_sha256"]
            or manifest.get("script_sha256") != actual_hashes["script_sha256"]
            or manifest.get("output_sha256") != actual_hashes["output_sha256"]
        ):
            mismatch_codes.append("manifest_hash_mismatch")

        fresh_result = rebuild_calculation_result()
        independent_regeneration_match = (
            calculation_canonical_json_bytes(fresh_result) == output_path.read_bytes()
        )
        if not independent_regeneration_match:
            mismatch_codes.append("regeneration_mismatch")

    if execution_report is not None:
        if (
            execution_report.get("calculation_output_sha256")
            != actual_hashes["output_sha256"]
            or execution_report.get("calculation_manifest_sha256")
            != actual_hashes["manifest_sha256"]
            or execution_report.get("all_thresholds_passed") is not True
        ):
            mismatch_codes.append("schema_mismatch")

    mismatch_codes = list(dict.fromkeys(mismatch_codes))
    accepted = not mismatch_codes
    threshold_evidence = result.get("threshold_evidence", {}) if result else {}
    return {
        "accepted": accepted,
        "primary_claim_label": "E-REPRO" if accepted else "B-BLOCKED",
        "claim_status": (
            "accepted_scoped_level_3_minkowski_pretest_only"
            if accepted
            else "blocked_reproducibility_mismatch"
        ),
        "mismatch_codes": mismatch_codes,
        "expected_hashes": EXPECTED_EXECUTION_HASHES,
        "actual_hashes": actual_hashes,
        "canonical_bytes_match": canonical_bytes_match,
        "independent_in_memory_regeneration_match": (
            independent_regeneration_match
        ),
        "threshold_evidence": threshold_evidence,
        "selected_next_target": (
            CURVED_RETEST_GUARDRAIL_TARGET
            if accepted
            else REPRODUCIBILITY_REPAIR_TARGET
        ),
    }


def build_review_report(**verification_paths: Path) -> dict[str, Any]:
    verification = verify_calculation_result(**verification_paths)
    accepted = verification["accepted"]
    return {
        "schema_id": (
            "SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_MINKOWSKI_CALCULATION_"
            "RESULT_REVIEW_20260709_v0"
        ),
        "review_id": (
            "SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_MINKOWSKI_CALCULATION_"
            "RESULT_REVIEW_v0"
        ),
        "status": (
            "accepted_scoped_e_repro" if accepted else "blocked_reproducibility_mismatch"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": REVIEW_TARGET,
        "consumed_target_kind": (
            "scalar_stress_energy_divergence_identity_minkowski_calculation_"
            "result_review"
        ),
        "selected_next_target": verification["selected_next_target"],
        "selected_next_target_kind": (
            "bounded_curved_space_scalar_qft_gr_source_contract_retest_"
            "guardrail_packet"
            if accepted
            else "scalar_minkowski_calculation_reproducibility_repair"
        ),
        "packet_result": REVIEW_OUTCOME if accepted else "B-BLOCKED",
        "strict_packet_result": REVIEW_STRICT_OUTCOME if accepted else "B-BLOCKED",
        "review_result": REVIEW_OUTCOME if accepted else "B-BLOCKED",
        "strict_review_result": REVIEW_STRICT_OUTCOME if accepted else "B-BLOCKED",
        "verification": verification,
        "claim": {
            "primary_label": verification["primary_claim_label"],
            "claim_status": verification["claim_status"],
            "claim_ceiling_level": 3,
            "claim_scope": (
                "flat-Minkowski scalar stress-energy divergence identity toy "
                "calculation only"
            ),
        },
        "execution_artifacts_modified_by_review": False,
        "equation_compendium_rows_activated": list(EQUATION_IDS) if accepted else [],
        "equation_compendium_status": (
            "ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO"
            if accepted
            else "not_activated"
        ),
        "ccft_lane_status": "paused_upstream_prerequisites",
        "remaining_blockers": [
            "no curved-spacetime source-contract witness",
            "no GR source admissibility",
            "no Bianchi compatibility",
            "no QFT-GR seam admissibility or closure",
            "no master-action promotion",
        ],
        "boundary": {
            "gravity_dynamics_validated": False,
            "source_admissibility_claimed": False,
            "bianchi_compatibility_claimed": False,
            "qft_gr_seam_admissibility_claimed": False,
            "qft_gr_seam_closure_claimed": False,
            "pillar_completion_claimed": False,
            "ccft_resumed": False,
            "ccft_validated": False,
            "master_action_promoted": False,
        },
        "lean_status_wording": (
            "scoped Lean passed; full ToeFormal aggregate not run / not upgraded"
        ),
    }


def write_report(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(report_json_bytes(payload))


def guardrail_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Prepare the scalar flat-limit guardrail.")
    parser.add_argument("--out", type=Path, default=GUARDRAIL_REPORT_PATH)
    args = parser.parse_args(argv)
    payload = build_guardrail_payload()
    validate_guardrail_payload(payload)
    write_report(args.out, payload)
    print(
        json.dumps(
            {
                "outcome": GUARDRAIL_OUTCOME,
                "selected_next_target": EXECUTION_TARGET,
            }
        )
    )
    return 0


def execution_report_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Record the scalar pretest execution.")
    parser.add_argument("--out", type=Path, default=EXECUTION_REPORT_PATH)
    args = parser.parse_args(argv)
    payload = build_execution_report()
    write_report(args.out, payload)
    print(
        json.dumps(
            {
                "outcome": EXECUTION_OUTCOME,
                "output_sha256": payload["calculation_output_sha256"],
                "selected_next_target": REVIEW_TARGET,
            }
        )
    )
    return 0


def review_report_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Review the scalar pretest result.")
    parser.add_argument("--out", type=Path, default=REVIEW_REPORT_PATH)
    args = parser.parse_args(argv)
    payload = build_review_report()
    write_report(args.out, payload)
    print(
        json.dumps(
            {
                "accepted": payload["verification"]["accepted"],
                "outcome": payload["packet_result"],
                "selected_next_target": payload["selected_next_target"],
            }
        )
    )
    return 0 if payload["verification"]["accepted"] else 1
