from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


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
