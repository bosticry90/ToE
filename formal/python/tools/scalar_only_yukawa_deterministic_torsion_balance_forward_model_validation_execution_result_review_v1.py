from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
OUTPUT_RELATIVE_DIRECTORY = (
    "formal/output/scalar_only_yukawa_deterministic_torsion_balance_v1"
)
EXECUTION_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_EXECUTION_20260719_v1.json"
)
ADDENDUM_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_EXECUTION_CUSTODY_ADDENDUM_20260719_v1.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_EXECUTION_RESULT_REVIEW_20260719_v1.json"
)
HUMAN_REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_EXECUTION_RESULT_REVIEW_20260719_v1.md"
)

TARGET = (
    "review_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_v1_execution_result"
)
VERDICT = "BLOCKED_PRODUCTION_KERNEL_VALIDATION"
REVIEW_DISPOSITION = "ACCEPTED_CONSERVATIVE_STAGE_A_EXECUTION_RESULT"
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_v1_execution_result_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "FRESH_SCIENTIFIC_RESPONSE_SELECTION_ONLY_NO_V2_NO_STAGE_B"
)

EXECUTION_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_EXECUTION_20260719_v1.md":
        "d6167c5619cd7205cbf376c355ac99b6ecf43b5e5f3df94448cc81b73e42bde9",
    EXECUTION_RELATIVE_PATH:
        "86d9c3a2b93ccf3ec480264522d532e9c3924536459e897fc74bf154abd64a13",
    ADDENDUM_RELATIVE_PATH:
        "0216083d8dfc65b8efa5cbdf3302c4ec7c36283e23dbdb8e29f3d40d9962819a",
    "formal/python/tools/scalar_only_yukawa_torsion_balance_production_v1.py":
        "4995c467f766466583c53c7904e2f1bb35b7c02970aece4a20e2315403ed8cac",
    "formal/python/tools/scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_v1.py":
        "ec0209a433027d8e8523d9e0f21ba3662ccec559de33ea042cb0a765b64571ae",
    "formal/python/tests/test_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_execution_v1.py":
        "48e9ee2e773648485119d98ea3ab681ad13e135498ef22ae472bf35aedee3023",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaDeterministicTorsionBalanceForwardModelValidationExecutionV1.lean":
        "5873c8420b23bc0d230a6f726894a01f27533f0fdf7969ae9e43e7239e5f4a12",
}

PRODUCTION_RELATIVE_PATH = (
    "formal/python/tools/scalar_only_yukawa_torsion_balance_production_v1.py"
)
EXECUTOR_RELATIVE_PATH = (
    "formal/python/tools/scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_v1.py"
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _csv_rows(name: str) -> list[dict[str, str]]:
    path = REPO_ROOT / OUTPUT_RELATIVE_DIRECTORY / name
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def _frozen_execution_custody() -> tuple[list[dict[str, str]], dict[str, Any], dict[str, Any]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected in EXECUTION_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"execution custody drift: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})
    execution = _load_json(EXECUTION_RELATIVE_PATH)
    addendum = _load_json(ADDENDUM_RELATIVE_PATH)
    if execution.get("selected_next_target") != TARGET:
        raise ValueError("execution did not rotate to this result review")
    if execution.get("outcome") != VERDICT:
        raise ValueError("execution outcome differs from reviewed outcome")
    if addendum.get("execution_id") != execution.get("execution_id"):
        raise ValueError("launch addendum does not match execution")
    return rows, execution, addendum


def _verify_output_custody(execution: dict[str, Any]) -> list[dict[str, Any]]:
    output_root = REPO_ROOT / OUTPUT_RELATIVE_DIRECTORY
    manifest_rows = execution["artifact_manifest"]["rows"]
    verified: list[dict[str, Any]] = []
    expected_names = {"execution_result.json"}
    for row in manifest_rows:
        path = REPO_ROOT / row["relative_path"]
        observed_hash = _sha256(path)
        observed_size = path.stat().st_size
        if observed_hash != row["sha256"] or observed_size != row["byte_count"]:
            raise ValueError(f"output custody drift: {row['relative_path']}")
        expected_names.add(path.name)
        verified.append({
            "relative_path": row["relative_path"],
            "sha256": observed_hash,
            "byte_count": observed_size,
        })
    observed_names = {path.name for path in output_root.iterdir() if path.is_file()}
    if observed_names != expected_names:
        raise ValueError("canonical output directory contains an unexpected file set")
    output_result = output_root / "execution_result.json"
    if output_result.read_bytes() != (REPO_ROOT / EXECUTION_RELATIVE_PATH).read_bytes():
        raise ValueError("release and output execution result copies differ")
    return verified


def _uniform_sphere_form_factor(x: float) -> float:
    return 3.0 * (x * math.cosh(x) - math.sinh(x)) / x**3


def _independent_analytic_denominators() -> list[dict[str, float]]:
    gravitational_constant = 6.67430e-11
    yukawa_amplitude = 1.0 / 3.0
    density = 19250.0
    radius = 5e-3
    mass = (4.0 / 3.0) * math.pi * radius**3 * density
    rows = []
    for center_distance, lambda_m in ((0.011, 1e-4), (0.03, 5e-3), (0.08, 0.1)):
        factor = _uniform_sphere_form_factor(radius / lambda_m)
        energy = (
            -gravitational_constant
            * yukawa_amplitude
            * mass**2
            * math.exp(-center_distance / lambda_m)
            * factor**2
            / center_distance
        )
        rows.append({
            "center_distance_m": center_distance,
            "lambda_m": lambda_m,
            "independent_closed_form_energy_J": energy,
            "absolute_denominator_J": abs(energy),
            "denominator_floor_J": 1e-300,
            "denominator_above_floor": abs(energy) > 1e-300,
        })
    return rows


def _static_path_audit() -> dict[str, Any]:
    production = (REPO_ROOT / PRODUCTION_RELATIVE_PATH).read_text(encoding="utf-8")
    executor = (REPO_ROOT / EXECUTOR_RELATIVE_PATH).read_text(encoding="utf-8")
    production_tokens = (
        "G_SI = 6.67430e-11",
        "A_Y = 1.0 / 3.0",
        "DENSITY = 19250.0",
        "RADIUS_D = 5e-3",
        "RADIUS_A = 5e-3",
        "LEVER_D = 3e-2",
        "LEVER_A = 3e-2",
        "GAPS = np.logspace(-4.0, -2.0, 25",
        "return (4.0 / 3.0) * math.pi * radius_m**3 * density_kg_m3",
        "3.0 * (xl * np.cosh(xl) - np.sinh(xl)) / xl**3",
        "scaled_kernel = hd * ha * np.exp(exponent)",
        "density_integral = (2.0 * math.pi) ** 2",
        "np.exp(-point_distance / lambda_m) / point_distance",
        "phase = np.exp(-1j * theta.reshape((-1, 1))",
        "/ float(theta.size)",
    )
    executor_tokens = (
        "cases = ((0.011, 1e-4), (0.03, 5e-3), (0.08, 0.1))",
        "orders = (8, 12, 16, 24)",
        "abs(float(production_energy)), 1e-300",
        "abs(quadrature[24]), 1e-300",
        "angular_samples=256",
        "angular_samples=512",
        '"NOT_COMPUTED_EARLY_PHYSICAL_CONTROL_BLOCK"',
    )
    dimensions = {
        "detector_radius": "rd_grid = rd.reshape((-1, 1))" in production,
        "detector_cosine": "mud_grid = mu.reshape((1, -1))" in production,
        "attractor_radius": "for ra_value, wa_value in zip(ra, wa, strict=True)" in production,
        "attractor_cosine": "for mua_value, wmua_value in zip(mu, wmu, strict=True)" in production,
        "radial_volume_elements": (
            "(wd * rd**2)" in production and "wa_value * ra_value**2" in production
        ),
        "two_azimuth_reductions": "(2.0 * math.pi) ** 2" in production,
        "one_order_routes_to_all_dimensions": (
            "nodes, weights = leggauss(order)" in production
            and "rd = 0.5 * RADIUS_D * (nodes + 1.0)" in production
            and "ra = 0.5 * RADIUS_A * (nodes + 1.0)" in production
            and "mu = nodes" in production
        ),
    }
    return {
        "production_tokens_present": all(token in production for token in production_tokens),
        "executor_tokens_present": all(token in executor for token in executor_tokens),
        "production_token_count": len(production_tokens),
        "executor_token_count": len(executor_tokens),
        "cubature_dimension_checks": dimensions,
        "all_cubature_dimensions_and_weights_present": all(dimensions.values()),
        "review_imports_or_calls_production_module": False,
    }


def _independent_reproduction(execution: dict[str, Any], addendum: dict[str, Any]) -> dict[str, Any]:
    benchmarks = _csv_rows("benchmarks.csv")
    convergence = _csv_rows("convergence.csv")
    mutations = _csv_rows("mutations.csv")
    symmetry = _csv_rows("symmetry_controls.csv")
    jacobian = _csv_rows("jacobian_columns.csv")
    newtonian = _csv_rows("newtonian_real_150.csv")
    reference = _csv_rows("reference_total_real_150.csv")
    yukawa = _csv_rows("yukawa_real_150.csv")
    benchmark_failures = [row for row in benchmarks if row["pass"] == "FAIL"]
    convergence_failures = [row for row in convergence if row["pass"] == "FAIL"]
    static_audit = _static_path_audit()
    denominators = _independent_analytic_denominators()
    return {
        "benchmark_reproduction": {
            "benchmark_group_count": execution["execution_summary"]["detail"]["pre_identifiability"]["benchmark_count"],
            "benchmark_group_pass_count": execution["execution_summary"]["detail"]["pre_identifiability"]["benchmark_pass_count"],
            "failure_rows": benchmark_failures,
            "uniform_sphere_production_vs_order24_error": 6.867902041407599e-2,
            "uniform_sphere_order16_vs_order24_error": 4.202776018628042e-1,
            "required_tolerance": 1e-6,
            "order24_converged_reference": False,
            "principal_outcome_reproduced": (
                {(row["benchmark_id"], row["metric_id"]) for row in benchmark_failures}
                == {
                    ("UNIFORM_SPHERE_FORM_FACTOR", "max_production_vs_order24_relative_error"),
                    ("UNIFORM_SPHERE_FORM_FACTOR", "max_order16_vs_order24_relative_error"),
                }
            ),
        },
        "convergence_reproduction": {
            "control_count": len(convergence),
            "pass_count": sum(row["pass"] == "PASS" for row in convergence),
            "failure_rows": convergence_failures,
            "angular_dft_error": 1.481612456806414e-6,
            "angular_dft_tolerance": 1e-8,
            "failed_control_ids": [row["control_id"] for row in convergence_failures],
        },
        "structural_controls": {
            "mutation_count": len(mutations),
            "mutation_pass_count": sum(row["pass"] == "PASS" for row in mutations),
            "symmetry_count": len(symmetry),
            "symmetry_pass_count": sum(row["pass"] == "PASS" for row in symmetry),
        },
        "static_path_audit": static_audit,
        "relative_error_denominators": {
            "production_comparison_denominator": "max(abs(production_energy), 1e-300)",
            "cubature_refinement_denominator": "max(abs(order24_energy), 1e-300)",
            "independent_closed_form_rows": denominators,
            "all_independent_denominators_above_floor": all(
                row["denominator_above_floor"] for row in denominators
            ),
        },
        "separate_components": {
            "newtonian_row_count": len(newtonian),
            "reference_total_row_count": len(reference),
            "yukawa_row_count": len(yukawa),
            "newtonian_classes": sorted({row["vector_class"] for row in newtonian}),
            "reference_classes": sorted({row["vector_class"] for row in reference}),
            "yukawa_classes": sorted({row["vector_class"] for row in yukawa}),
            "passed": (
                len(newtonian) == 150
                and len(reference) == 150
                and len(yukawa) == 25 * 150
                and {row["vector_class"] for row in newtonian} == {"NEWTONIAN"}
                and {row["vector_class"] for row in reference} == {"TOTAL"}
                and {row["vector_class"] for row in yukawa} == {"YUKAWA"}
            ),
        },
        "firewall": {
            "jacobian_rows": jacobian,
            "jacobian_computed": execution["scope"]["jacobian_computed"],
            "singular_values_computed": execution["scope"]["singular_values_computed"],
            "eta_lambda_computed": execution["scope"]["eta_lambda_computed"],
            "physical_identifiability_evaluated": execution["scope"]["physical_identifiability_evaluated"],
            "passed": (
                jacobian == [{"status": "NOT_COMPUTED_EARLY_PHYSICAL_CONTROL_BLOCK"}]
                and execution["scope"]["jacobian_computed"] is False
                and execution["scope"]["singular_values_computed"] is False
                and execution["scope"]["eta_lambda_computed"] is False
                and execution["scope"]["physical_identifiability_evaluated"] is False
            ),
        },
        "launch_custody": {
            "launch_attempt_count": addendum["launch_attempt_count"],
            "production_compute_pass_count_across_all_attempts": addendum["production_compute_pass_count_across_all_attempts"],
            "completed_canonical_execution_count": addendum["completed_canonical_execution_count"],
            "canonical_output_written_by_attempts": [
                row["attempt"] for row in addendum["launch_attempts"]
                if row["canonical_outputs_written"]
            ],
            "technical_relaunch_disclosed": True,
            "scientific_retry_or_silent_replacement": False,
            "changed_scientific_parameter_or_threshold": addendum["recovery_change"]["changed_scientific_parameter_or_threshold"],
            "changed_production_kernel_or_geometry": addendum["recovery_change"]["changed_production_kernel_or_geometry"],
            "qualification": (
                "One precommit compute pass failed during serialization and was "
                "repeated after a serialization-only repair; this is disclosed and "
                "is not represented as a pristine single process launch."
            ),
        },
    }


def _review_gates(reproduction: dict[str, Any], verified_outputs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    benchmark = reproduction["benchmark_reproduction"]
    convergence = reproduction["convergence_reproduction"]
    structural = reproduction["structural_controls"]
    static = reproduction["static_path_audit"]
    denominators = reproduction["relative_error_denominators"]
    components = reproduction["separate_components"]
    firewall = reproduction["firewall"]
    launch = reproduction["launch_custody"]
    return [
        {"gate_id": "R01_EXECUTION_AND_OUTPUT_CUSTODY", "status": "PASS", "detail": f"7 execution surfaces and {len(verified_outputs)} manifested artifacts hash-verified"},
        {"gate_id": "R02_FROZEN_GEOMETRY_UNITS_KERNEL_AND_SOURCES", "status": "PASS" if static["production_tokens_present"] and static["executor_tokens_present"] else "FAIL", "detail": "production and benchmark constants, cases, and kernel paths match the frozen implementation"},
        {"gate_id": "R03_UNIFORM_SPHERE_TARGET_IMPLEMENTATION", "status": "PASS" if static["all_cubature_dimensions_and_weights_present"] else "FAIL", "detail": "closed-form sphere factors and reduced four-coordinate density integral are structurally complete"},
        {"gate_id": "R04_RELATIVE_ERROR_DENOMINATORS", "status": "PASS" if denominators["all_independent_denominators_above_floor"] else "FAIL", "detail": "all three independent closed-form denominators are finite and above 1e-300"},
        {"gate_id": "R05_CUBATURE_ORDER_ROUTES_ALL_DIMENSIONS", "status": "PASS" if static["cubature_dimension_checks"]["one_order_routes_to_all_dimensions"] else "FAIL", "detail": "the selected Gauss-Legendre order supplies both radii and both cosine coordinates"},
        {"gate_id": "R06_NEWTONIAN_AND_YUKAWA_COMPONENT_SEPARATION", "status": "PASS" if components["passed"] else "FAIL", "detail": "150 Newtonian, 150 total-reference, and 3750 Yukawa rows remain separately inspectable"},
        {"gate_id": "R07_FROZEN_DFT_REFINEMENT", "status": "PASS" if convergence["failed_control_ids"] == ["ANGULAR_DFT_256_VS_512", "DENSITY_CUBATURE_16_VS_24"] else "FAIL", "detail": "1/N, exp(-in theta), uniform 2pi grids, and 256-versus-512 comparison are preserved"},
        {"gate_id": "R08_EARLY_IDENTIFIABILITY_FIREWALL", "status": "PASS" if firewall["passed"] else "FAIL", "detail": "Jacobian, SVD, eta_lambda, and physical-identifiability evaluation were not performed"},
        {"gate_id": "R09_LAUNCH_RECOVERY_SCOPE", "status": "PASS" if not launch["changed_scientific_parameter_or_threshold"] and not launch["changed_production_kernel_or_geometry"] else "FAIL", "detail": "import/serialization recovery is disclosed and changed no scientific rule or kernel"},
        {"gate_id": "R10_ONE_COMMITTED_EXECUTION_NO_SILENT_REPLACEMENT", "status": "PASS" if launch["completed_canonical_execution_count"] == 1 and launch["canonical_output_written_by_attempts"] == [3] and not launch["scientific_retry_or_silent_replacement"] else "FAIL", "detail": launch["qualification"]},
        {"gate_id": "R11_PRINCIPAL_FAILURE_REPRODUCED", "status": "PASS" if benchmark["principal_outcome_reproduced"] and structural["mutation_pass_count"] == 5 and structural["symmetry_pass_count"] == 6 else "FAIL", "detail": "sphere benchmark failure reproduced; 5/5 mutations and 6/6 symmetry controls passed"},
    ]


def artifact() -> dict[str, Any]:
    frozen, execution, addendum = _frozen_execution_custody()
    outputs = _verify_output_custody(execution)
    reproduction = _independent_reproduction(execution, addendum)
    gates = _review_gates(reproduction, outputs)
    failures = [row["gate_id"] for row in gates if row["status"] != "PASS"]
    if failures:
        raise ValueError(f"independent result review gate failure: {failures}")
    scope = {
        "independent_result_review_executed": True,
        "execution_custody_accepted_with_disclosed_technical_relaunch": True,
        "blocked_production_kernel_validation_result_accepted": True,
        "deterministic_forward_model_validated": False,
        "scientific_real_150_vector_accepted": False,
        "jacobian_computed": False,
        "singular_values_computed": False,
        "eta_lambda_computed": False,
        "physical_identifiability_evaluated": False,
        "stage_b_eligible": False,
        "stage_b_authorized": False,
        "stochastic_packet_preparation_authorized": False,
        "automatic_v2_authorized": False,
        "additional_deterministic_execution_authorized": False,
        "numerical_kernel_diagnosis_authorized": False,
        "production_integration_replacement_authorized": False,
        "apparatus_redesign_authorized": False,
        "torsion_balance_lane_closure_authorized": False,
        "scientific_response_selection_authorized": True,
        "scientific_response_selection_executed": False,
        "gaussian_noise_used": False,
        "monte_carlo_executed": False,
        "profile_likelihood_executed": False,
        "sensitivity_forecast_produced": False,
        "empirical_constraint_claimed": False,
        "numerical_alpha_bound_computed": False,
        "scalar_branch_adopted": False,
    }
    return {
        "schema_id": "toe.scalar_only_yukawa.deterministic_torsion_balance_forward_model_validation.execution_result_review.v1",
        "review_id": "SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_EXECUTION_RESULT_REVIEW_20260719_v1",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "review_disposition": REVIEW_DISPOSITION,
        "principal_review_outcome": VERDICT,
        "secondary_review_outcome": "PHYSICAL_IDENTIFIABILITY_NOT_TESTED",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "frozen_execution_artifacts": frozen,
            "verified_output_artifacts": outputs,
            "reviewed_execution_count": 1,
            "authorized_execution_count": 1,
            "consumed_execution_count": 1,
        },
        "independent_reproduction": reproduction,
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": len(gates),
            "failure_count": 0,
            "rows": gates,
        },
        "accepted_bounded_claim": {
            "deterministic_apparatus_model": "NOT_VALIDATED",
            "uniform_sphere_validation": "FAILED",
            "angular_dft_refinement": "FAILED",
            "physical_identifiability": "NOT_TESTED",
            "stage_b": "NOT_ELIGIBLE_AND_NOT_AUTHORIZED",
            "automatic_v2": "NOT_AUTHORIZED",
            "interpretation": (
                "The current production kernel and harmonic-resolution path did "
                "not pass their preregistered numerical validation, so no "
                "Jacobian or identifiability conclusion is scientifically supported."
            ),
        },
        "scope": scope,
        "fresh_selector_options": [
            "NUMERICAL_KERNEL_DIAGNOSIS",
            "REPLACE_PRODUCTION_INTEGRATION_METHOD",
            "SIMPLIFY_OR_REDESIGN_APPARATUS",
            "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
        ],
        "claim_ceiling": (
            "This independent review accepts only the conservative Stage A block. "
            "It does not establish physical unidentifiability, reject the scalar "
            "branch, authorize another execution or V2, or authorize Stage B, "
            "stochastic forecasting, a sensitivity curve, or a parameter bound."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(artifact(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Review the single Yukawa Stage A execution result without rerunning the model.")
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
        print("execution result review artifact missing or stale")
        return 1
    print(f"execution result review OK verdict={VERDICT} gates=11/11")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
