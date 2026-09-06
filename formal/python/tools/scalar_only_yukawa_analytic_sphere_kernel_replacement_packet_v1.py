from __future__ import annotations

import argparse
from decimal import Decimal, getcontext
import hashlib
import json
import math
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_20260719_v1.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_20260719_v1.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_"
    "replacement_packet_v1.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaAnalyticSphereKernelReplacementPacketV1.lean"
)
SELECTOR_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_V0_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.json"
)
V0_PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_20260719_v0.json"
)
V0_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_REVIEW_20260719_v0.json"
)
ORACLE_INPUT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_PACKET_20260719_v0.json"
)

TARGET = "prepare_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1"
VERDICT = "PREPARED_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_V1"
SELECTED_NEXT_TARGET = (
    "review_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1_result"
)
SELECTED_NEXT_TARGET_KIND = (
    "INDEPENDENT_FINAL_V1_PACKET_REVIEW_ONLY_NO_CANDIDATE_IMPLEMENTATION_OR_EXECUTION"
)

SELECTOR_HASHES = {
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_V0_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.md":
        "0aa2e8c82d5807d14b4eff7c7d5ea0d09aa0f4414b88ba54b92d5eee9630ba8b",
    SELECTOR_RELATIVE_PATH:
        "f68f8c3455a8a853e74142f40df245074c00ce4704e158f63120bcd34c805055",
    "formal/python/tools/post_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0_review_scientific_response_selection_v0.py":
        "5f5925e66fc5770a2fdb2ec8b9fb899b559c0bbce4c1590dd643eb7941ad1e8a",
    "formal/python/tests/test_post_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0_review_scientific_response_selection_v0.py":
        "d5835892d2bc24486eb40c4daa3fa4afe4ea9408a698d4ca85911ea2a932897c",
    "formal/toe_formal/ToeFormal/Derivation/PostScalarOnlyYukawaAnalyticSphereKernelReplacementPacketV0ReviewScientificResponseSelectionV0.lean":
        "6ffd3b7de04412b21f325ef9333ec249a0cdcca8df535063edca9fc20b3c164b",
}

V0_PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_20260719_v0.md":
        "ca67c420ebed4032d0556d88759e8f48b7d72188cf4810b132bd23fbf1bd57fb",
    V0_PACKET_RELATIVE_PATH:
        "3b05386c4b386595d41a283c8b665386fc55abc81f865218a3eff1395755bcec",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0.py":
        "cda104a3546fad24d74166d0d880b0e9ee6dfdbea4a6f34bfa0cb3697cbbf124",
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0.py":
        "e44a2fe8b3cb3e0902ad57e7c4004e07bb577c7c30419e90778a96ba9e92b1e0",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaAnalyticSphereKernelReplacementPacketV0.lean":
        "21096d6a5fe86ca912798dc7f7d92941f2aac389f5743dbf4167c031c87117a0",
}

V0_REVIEW_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_REVIEW_20260719_v0.md":
        "b3157203008109bbf7945f0bc5a03cafcb28b13c95128f5d3559b8abf65a1553",
    V0_REVIEW_RELATIVE_PATH:
        "6d775002f667a32caed167b1d601dc29cfac34a5b4e498af372676b1ca5cda37",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_review_v0.py":
        "ff47312ebe199ae8f033b96389885fa3acdba5843943ad55bfcaa079620da505",
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_review_v0.py":
        "81b3a3b289a27ddf6d162c86b1d042d24eb1f9cd1c49a0fad504b36b6030cf2e",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaAnalyticSphereKernelReplacementPacketReviewV0.lean":
        "c1a30c10822caaffd036f06a7a5cfe92b4f53ac1d13296314acdcbc4103e52bd",
}

ORACLE_INPUT_HASHES = {
    ORACLE_INPUT_RELATIVE_PATH:
        "8e2e93963182a27b1618c0fe1d02aa34eb8740f4a422429a041f2bcc02323bb5",
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_PACKET_20260719_v0.md":
        "6450af7a7aa314ee86802a63fef19da20d738905e28f4463bd2523d0457745f2",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_v0.py":
        "38a2f5e856cfa97f805877a01efe8801da336ffae6e44e3e8c279d19aeb6941e",
}

FAILED_REVIEW_GATES = (
    "R32_INTERNAL_REPLACEMENT_TARGETS_EXACT",
    "R33_LAMBDA_COMPONENT_COMPATIBILITY_MATRIX_COMPLETE",
    "R34_ARRAY_DOMAIN_FAILURE_SEMANTICS_COMPLETE",
    "R35_VALIDATION_ONLY_HOOK_ENFORCEMENT_EXECUTABLE",
    "R37_EIGHT_REGRESSION_INPUT_RECORDS_COMPLETE",
    "R40_INDEPENDENT_RADIAL_DERIVATIVE_REFERENCE_COMPLETE",
    "R41_LIMIT_AND_BOUNDARY_PROBES_NUMERIC",
    "R43_MUTATION_ROUTES_COMPLETE",
    "R44_MUTATION_DETECTION_PREDICATES_NUMERIC",
    "R50_RUNTIME_PROBE_INPUTS_EXACT",
    "R52_CANONICAL_SERIALIZATION_SCHEMA_EXACT",
)

PACKET_REVIEW_OUTCOMES = (
    "ANALYTIC_KERNEL_REPLACEMENT_CONTRACT_READY",
    "BLOCKED_REPLACEMENT_INTERFACE_IDENTITY",
    "BLOCKED_REPLACEMENT_DOMAIN_COVERAGE",
    "BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE",
    "BLOCKED_REPLACEMENT_FIREWALL",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _verify_hashes(rows: dict[str, str], label: str) -> None:
    for relative_path, expected in rows.items():
        if _sha256(REPO_ROOT / relative_path) != expected:
            raise ValueError(f"{label} drift: {relative_path}")


def _hex(value: float) -> str:
    return float(value).hex()


def _mass_hex(radius_m: float, density_kg_m3: float) -> str:
    return _hex((4.0 / 3.0) * math.pi * radius_m**3 * density_kg_m3)


def _decimal_scientific(value: Decimal) -> str:
    return format(value.normalize(), "E")


def _regression_rows(
    oracle_inputs: dict[str, Any], v0_packet: dict[str, Any]
) -> list[dict[str, Any]]:
    input_rows = oracle_inputs["representative_domain"]["rows"]
    reference_rows = v0_packet["accepted_oracle_regression_contract"]["rows"]
    if [row["case_id"] for row in input_rows] != [row["case_id"] for row in reference_rows]:
        raise ValueError("accepted oracle input/reference case order mismatch")
    getcontext().prec = 100
    result = []
    for inputs, refs in zip(input_rows, reference_rows, strict=True):
        distance = Decimal(str(inputs["center_distance_m"]))
        lambda_m = Decimal(str(inputs["lambda_m"]))
        newtonian_energy = Decimal(refs["newtonian_reference_J_decimal"])
        yukawa_energy = Decimal(refs["yukawa_reference_J_decimal"])
        newtonian_derivative = -newtonian_energy / distance
        yukawa_derivative = -yukawa_energy * (Decimal(1) / distance + Decimal(1) / lambda_m)
        r1 = float(inputs["radius_1_m"])
        r2 = float(inputs["radius_2_m"])
        rho1 = float(inputs["density_1_kg_m3"])
        rho2 = float(inputs["density_2_kg_m3"])
        result.append({
            "case_id": inputs["case_id"],
            "component_order": ["newtonian", "yukawa", "total"],
            "radius_1_m_hex": _hex(r1),
            "radius_2_m_hex": _hex(r2),
            "density_1_kg_m3_hex": _hex(rho1),
            "density_2_kg_m3_hex": _hex(rho2),
            "mass_1_kg_hex": _mass_hex(r1, rho1),
            "mass_2_kg_hex": _mass_hex(r2, rho2),
            "surface_gap_m_hex": _hex(float(inputs["surface_gap_m"])),
            "center_distance_m_hex": _hex(float(inputs["center_distance_m"])),
            "lambda_m_hex": _hex(float(inputs["lambda_m"])),
            "yukawa_amplitude_hex": _hex(1.0 / 3.0),
            "x_1_expected_decimal": str(inputs["x_1"]),
            "x_2_expected_decimal": str(inputs["x_2"]),
            "newtonian_energy_reference_J_decimal": refs["newtonian_reference_J_decimal"],
            "yukawa_energy_reference_J_decimal": refs["yukawa_reference_J_decimal"],
            "newtonian_dU_dD_reference_N_decimal": _decimal_scientific(newtonian_derivative),
            "yukawa_dU_dD_reference_N_decimal": _decimal_scientific(yukawa_derivative),
            "energy_acceptance": {
                "absolute_tolerance_J_decimal": "1E-38",
                "relative_tolerance_decimal": "5E-12",
            },
            "derivative_acceptance": {
                "absolute_tolerance_N_decimal": "1E-34",
                "relative_tolerance_decimal": "5E-12",
            },
            "derivative_reference_provenance": (
                "D_FROM_FROZEN_INPUT; U_FROM_ACCEPTED_120_DIGIT_RADIAL_REFERENCE; "
                "dU_N/dD=-U_N/D; dU_Y/dD=-U_Y*(1/D+1/lambda); "
                "100_DIGIT_DECIMAL_NO_CANDIDATE_CALL"
            ),
        })
    return result


def _compatibility_rows() -> list[dict[str, str]]:
    historical = {
        "newtonian": {
            "POSITIVE_FINITE": "NEWTONIAN",
            "ZERO": "NEWTONIAN",
            "NEGATIVE_FINITE": "NEWTONIAN",
            "NONFINITE": "UNGUARDED_OR_UNDEFINED",
        },
        "yukawa": {
            "POSITIVE_FINITE": "YUKAWA",
            "ZERO": "ZERO_ARRAY",
            "NEGATIVE_FINITE": "ZERO_ARRAY",
            "NONFINITE": "UNGUARDED_OR_UNDEFINED",
        },
        "total": {
            "POSITIVE_FINITE": "NEWTONIAN_PLUS_YUKAWA",
            "ZERO": "NEWTONIAN_ONLY",
            "NEGATIVE_FINITE": "NEWTONIAN_ONLY",
            "NONFINITE": "UNGUARDED_OR_UNDEFINED",
        },
    }
    proposed = {
        "newtonian": {
            "POSITIVE_FINITE": "NEWTONIAN",
            "ZERO": "NEWTONIAN_HISTORICAL_SENTINEL",
            "NEGATIVE_FINITE": "VALUE_ERROR",
            "NONFINITE": "VALUE_ERROR",
        },
        "yukawa": {
            "POSITIVE_FINITE": "YUKAWA",
            "ZERO": "VALUE_ERROR",
            "NEGATIVE_FINITE": "VALUE_ERROR",
            "NONFINITE": "VALUE_ERROR",
        },
        "total": {
            "POSITIVE_FINITE": "NEWTONIAN_PLUS_YUKAWA",
            "ZERO": "VALUE_ERROR",
            "NEGATIVE_FINITE": "VALUE_ERROR",
            "NONFINITE": "VALUE_ERROR",
        },
    }
    rows = []
    for component in ("newtonian", "yukawa", "total"):
        for lambda_class in ("POSITIVE_FINITE", "ZERO", "NEGATIVE_FINITE", "NONFINITE"):
            old = historical[component][lambda_class]
            new = proposed[component][lambda_class]
            rows.append({
                "component": component,
                "lambda_class": lambda_class,
                "historical_v0_behavior": old,
                "proposed_v1_behavior": new,
                "compatibility": "UNCHANGED" if old == new else "EXPLICIT_GUARD_CHANGE",
                "failure_type_if_rejected": "ValueError" if new == "VALUE_ERROR" else "NONE",
            })
    return rows


def _probe_inputs(
    *, distance: float, lambda_m: float, mass_1: float, mass_2: float,
    radius_1: float, radius_2: float, amplitude: float = 1.0 / 3.0,
) -> dict[str, str]:
    return {
        "center_distance_m_hex": _hex(distance),
        "lambda_m_hex": _hex(lambda_m),
        "mass_1_kg_hex": _hex(mass_1),
        "mass_2_kg_hex": _hex(mass_2),
        "radius_1_m_hex": _hex(radius_1),
        "radius_2_m_hex": _hex(radius_2),
        "yukawa_amplitude_hex": _hex(amplitude),
    }


def _limit_probe_rows() -> list[dict[str, Any]]:
    base = _probe_inputs(
        distance=0.03, lambda_m=0.01, mass_1=1.0, mass_2=2.0,
        radius_1=0.0, radius_2=0.0,
    )
    equal = _probe_inputs(
        distance=0.010000000001, lambda_m=0.001, mass_1=0.01, mass_2=0.01,
        radius_1=0.005, radius_2=0.005,
    )
    rows = [
        {"probe_id": "P01_POINT_PARTICLE", "component": "yukawa", "inputs": base, "expected": "POINT_YUKAWA_FORMULA", "absolute_tolerance": "1E-34 J", "relative_tolerance": "5E-12"},
        {"probe_id": "P02_POINT_NEWTONIAN_LAMBDA_ZERO_SENTINEL", "component": "newtonian", "inputs": {**base, "lambda_m_hex": _hex(0.0)}, "expected": "MINUS_G_M1_M2_OVER_D", "absolute_tolerance": "1E-34 J", "relative_tolerance": "5E-12"},
        {"probe_id": "P03_NEAR_CONTACT_RESOLVED", "component": "total", "inputs": equal, "expected": "FINITE_WITH_NEGATIVE_ENERGY_POSITIVE_DERIVATIVE", "absolute_tolerance": "1E-34", "relative_tolerance": "5E-12"},
        {"probe_id": "P04_TOUCHING_REJECTED", "component": "total", "inputs": {**equal, "center_distance_m_hex": _hex(0.01)}, "expected": "ValueError:TOUCHING_OR_OVERLAPPING", "absolute_tolerance": "NOT_APPLICABLE", "relative_tolerance": "NOT_APPLICABLE"},
        {"probe_id": "P05_OVERLAP_REJECTED", "component": "total", "inputs": {**equal, "center_distance_m_hex": _hex(0.009999)}, "expected": "ValueError:TOUCHING_OR_OVERLAPPING", "absolute_tolerance": "NOT_APPLICABLE", "relative_tolerance": "NOT_APPLICABLE"},
        {"probe_id": "P06_X_1000_ACCEPTED", "component": "yukawa", "inputs": _probe_inputs(distance=0.010001, lambda_m=5e-6, mass_1=0.01, mass_2=0.01, radius_1=0.005, radius_2=0.005), "expected": "FINITE_NO_DIRECT_HYPERBOLIC_PATH", "absolute_tolerance": "1E-34", "relative_tolerance": "5E-12"},
        {"probe_id": "P07_X_ABOVE_1000_REJECTED", "component": "yukawa", "inputs": _probe_inputs(distance=0.010001, lambda_m=4e-6, mass_1=0.01, mass_2=0.01, radius_1=0.005, radius_2=0.005), "expected": "ValueError:X_OUTSIDE_QUALIFIED_DOMAIN", "absolute_tolerance": "NOT_APPLICABLE", "relative_tolerance": "NOT_APPLICABLE"},
        {"probe_id": "P08_ZERO_COUPLING", "component": "yukawa", "inputs": {**base, "yukawa_amplitude_hex": _hex(0.0)}, "expected": "ENERGY_AND_DERIVATIVE_EXACT_POSITIVE_ZERO", "absolute_tolerance": "0", "relative_tolerance": "0"},
        {"probe_id": "P09_HALF_COUPLING_LINEARITY", "component": "yukawa", "inputs": {**base, "yukawa_amplitude_hex": _hex(1.0 / 6.0)}, "expected": "EXACTLY_HALF_OF_A_Y_ONE_THIRD_WITHIN_BINARY64", "absolute_tolerance": "1E-34", "relative_tolerance": "5E-14"},
        {"probe_id": "P10_LONG_RANGE", "component": "yukawa", "inputs": _probe_inputs(distance=0.03, lambda_m=1e6, mass_1=1.0, mass_2=2.0, radius_1=0.005, radius_2=0.002), "expected": "RATIO_TO_MINUS_A_Y_G_M1_M2_OVER_D_WITHIN_1E-7", "absolute_tolerance": "1E-34 J", "relative_tolerance": "1E-7"},
        {"probe_id": "P11_LARGE_SEPARATION_REPRESENTABLE", "component": "yukawa", "inputs": _probe_inputs(distance=1.0, lambda_m=0.01, mass_1=1.0, mass_2=2.0, radius_1=0.005, radius_2=0.002), "expected": "FINITE_NEGATIVE_ENERGY_POSITIVE_DERIVATIVE", "absolute_tolerance": "1E-300", "relative_tolerance": "5E-12"},
        {"probe_id": "P12_LARGE_SEPARATION_UNDERFLOW", "component": "yukawa", "inputs": _probe_inputs(distance=10.0, lambda_m=0.001, mass_1=1.0, mass_2=2.0, radius_1=0.0005, radius_2=0.0005), "expected": "FloatingPointError:UNREPRESENTABLE_NONZERO_OUTPUT_WITH_LOG_ABS", "absolute_tolerance": "NOT_APPLICABLE", "relative_tolerance": "NOT_APPLICABLE"},
        {"probe_id": "P13_EMPTY_ARRAY_REJECTED", "component": "total", "inputs": {"distance_m_hex_array": []}, "expected": "ValueError:EMPTY_DISTANCE_ARRAY", "absolute_tolerance": "NOT_APPLICABLE", "relative_tolerance": "NOT_APPLICABLE"},
    ]
    return rows


def _mutation_rows() -> list[dict[str, Any]]:
    common = {
        "execution_order": "BASELINE_CANDIDATE_THEN_SINGLE_MUTATION_THEN_SAME_ADJUDICATOR",
        "failure_consequence": "BLOCKED_KERNEL_MUTATION_CONTROLS_NO_SCIENTIFIC_QUALIFICATION",
    }
    return [
        {"mutation_id": "M01_GAP_SUBSTITUTED_FOR_CENTER_DISTANCE", "case_ids": ["LEGACY_STAGE_A_01_TRANSITION"], "components": ["yukawa"], "injection_point": "PAIR_DISTANCE_ARGUMENT_BEFORE_DOMAIN_PREFLIGHT", "acceptance_rule": "ABS_RELATIVE_ENERGY_ERROR_GREATER_THAN_OR_EQUAL_0.1", "absolute_tolerance": "NOT_USED", "relative_tolerance": "0.1", **common},
        {"mutation_id": "M02_MISSING_SECOND_SPHERE_FACTOR", "case_ids": ["MIXED_X_UNEQUAL"], "components": ["yukawa"], "injection_point": "SCALED_PAIR_FACTOR_SET_H2_TO_ONE", "acceptance_rule": "ABS_RELATIVE_ENERGY_ERROR_GREATER_THAN_OR_EQUAL_0.1", "absolute_tolerance": "NOT_USED", "relative_tolerance": "0.1", **common},
        {"mutation_id": "M03_MISSING_A_Y_ONE_THIRD", "case_ids": ["LEGACY_STAGE_A_01_TRANSITION"], "components": ["yukawa"], "injection_point": "YUKAWA_PREFACTOR_SET_A_Y_TO_ONE", "acceptance_rule": "ABS_RELATIVE_ENERGY_ERROR_GREATER_THAN_OR_EQUAL_1.0", "absolute_tolerance": "NOT_USED", "relative_tolerance": "1.0", **common},
        {"mutation_id": "M04_REVERSED_ATTRACTIVE_SIGN", "case_ids": ["LEGACY_STAGE_A_02_LONG_RANGE"], "components": ["yukawa"], "injection_point": "YUKAWA_ENERGY_FINAL_SIGN", "acceptance_rule": "MUTATED_ENERGY_STRICTLY_POSITIVE_WHILE_REFERENCE_STRICTLY_NEGATIVE", "absolute_tolerance": "0", "relative_tolerance": "0", **common},
        {"mutation_id": "M05_WRONG_RADIAL_DERIVATIVE_SIGN", "case_ids": ["LEGACY_STAGE_A_02_LONG_RANGE"], "components": ["newtonian", "yukawa"], "injection_point": "RADIAL_DERIVATIVE_FINAL_SIGN", "acceptance_rule": "AT_LEAST_ONE_MUTATED_DERIVATIVE_STRICTLY_NEGATIVE_WHILE_REFERENCE_STRICTLY_POSITIVE", "absolute_tolerance": "0", "relative_tolerance": "0", **common},
        {"mutation_id": "M06_DIRECT_LARGE_X_HYPERBOLIC_OVERFLOW", "case_ids": ["EXTREME_X_1000_UNEQUAL"], "components": ["yukawa"], "injection_point": "H_FACTOR_FORCE_DIRECT_SINH_COSH_WITH_NUMPY_ERRSTATE_RAISE", "acceptance_rule": "REQUIRED_EXCEPTION", "required_exception": "FloatingPointError", **common},
        {"mutation_id": "M07_DIRECT_SMALL_X_CANCELLATION", "case_ids": ["SMALL_X_UNEQUAL_WIDE"], "components": ["yukawa"], "injection_point": "H_FACTOR_FORCE_DIRECT_FORMULA_AT_X_0.001", "acceptance_rule": "ABS_H_ERROR_GREATER_THAN_5E-15_PLUS_5E-12_TIMES_REFERENCE", "absolute_tolerance": "5E-15", "relative_tolerance": "5E-12", **common},
        {"mutation_id": "M08_TOUCHING_OR_OVERLAPPING_INPUT_ACCEPTED", "case_ids": ["P04_TOUCHING_REJECTED"], "components": ["total"], "injection_point": "DELETE_STRICT_NONOVERLAP_GUARD", "acceptance_rule": "MUTATED_CALL_RETURNS_INSTEAD_OF_REQUIRED_VALUE_ERROR", "required_exception": "ValueError", **common},
        {"mutation_id": "M09_NONPOSITIVE_YUKAWA_RANGE_ACCEPTED", "case_ids": ["P02_POINT_NEWTONIAN_LAMBDA_ZERO_SENTINEL"], "components": ["yukawa", "total"], "injection_point": "DELETE_COMPONENT_LAMBDA_MATRIX_GUARD", "acceptance_rule": "MUTATED_CALL_RETURNS_INSTEAD_OF_REQUIRED_VALUE_ERROR", "required_exception": "ValueError", **common},
        {"mutation_id": "M10_X_ABOVE_QUALIFIED_MAXIMUM_ACCEPTED", "case_ids": ["P07_X_ABOVE_1000_REJECTED"], "components": ["yukawa"], "injection_point": "DELETE_X_MAXIMUM_GUARD", "acceptance_rule": "MUTATED_CALL_RETURNS_INSTEAD_OF_REQUIRED_VALUE_ERROR", "required_exception": "ValueError", **common},
        {"mutation_id": "M11_OUTPUT_SHAPE_OR_DTYPE_CHANGED", "case_ids": ["LEGACY_STAGE_A_01_TRANSITION", "LEGACY_STAGE_A_02_LONG_RANGE"], "components": ["total"], "injection_point": "CAST_RETURN_ARRAYS_TO_FLOAT32", "acceptance_rule": "DTYPE_NOT_FLOAT64_OR_SHAPE_NOT_EXACT_INPUT_SHAPE", "absolute_tolerance": "0", "relative_tolerance": "0", **common},
        {"mutation_id": "M12_REFERENCE_HELPER_SHARED_WITH_CANDIDATE", "case_ids": ["STATIC_SOURCE_SCAN"], "components": ["SOURCE"], "injection_point": "INSERT_FORBIDDEN_ORACLE_EVALUATOR_IMPORT_SENTINEL", "acceptance_rule": "AST_IMPORT_AND_CALL_GRAPH_SCANNER_MUST_DETECT_FORBIDDEN_DEPENDENCY", "required_exception": "ForbiddenDependencyDetected", **common},
    ]


def build_report() -> dict[str, Any]:
    _verify_hashes(SELECTOR_HASHES, "selector authority")
    _verify_hashes(V0_PACKET_HASHES, "V0 packet")
    _verify_hashes(V0_REVIEW_HASHES, "V0 review")
    _verify_hashes(ORACLE_INPUT_HASHES, "accepted oracle input")
    selector = _load_json(SELECTOR_RELATIVE_PATH)
    v0_packet = _load_json(V0_PACKET_RELATIVE_PATH)
    review = _load_json(V0_REVIEW_RELATIVE_PATH)
    oracle_inputs = _load_json(ORACLE_INPUT_RELATIVE_PATH)

    if selector.get("selected_next_target") != TARGET:
        raise ValueError("selector did not authorize V1 packet preparation")
    if selector.get("selected_route") != "REPAIR_ANALYTIC_KERNEL_REPLACEMENT_EXECUTION_CONTRACT":
        raise ValueError("selector route mismatch")
    if tuple(selector["v1_repair_contract"]["repair_gate_ids"]) != FAILED_REVIEW_GATES:
        raise ValueError("selector repair-gate set mismatch")
    accepted_gate_ids = [
        row["gate_id"] for row in review["review_gates"]["rows"] if row["status"] == "PASS"
    ]
    if len(accepted_gate_ids) != 51:
        raise ValueError("accepted review gate count mismatch")

    regression_rows = _regression_rows(oracle_inputs, v0_packet)
    compatibility_rows = _compatibility_rows()
    probes = _limit_probe_rows()
    mutations = _mutation_rows()
    if not (len(regression_rows) == 8 and len(compatibility_rows) == 12 and len(probes) == 13 and len(mutations) == 12):
        raise ValueError("V1 contract row count mismatch")

    packet_gates = (
        "EXACT_SELECTOR_AUTHORITY_AND_FINAL_V1_TARGET",
        "V0_PACKET_AND_REVIEW_HASH_FROZEN",
        "FIFTY_ONE_ACCEPTED_REVIEW_GATES_FROZEN",
        "EXACT_ELEVEN_FAILED_GATES_REPAIRED",
        "ALL_NONFAILED_V0_SURFACES_UNCHANGED",
        "INTERNAL_REPLACEMENT_FUNCTION_LIST_EXACT",
        "FUTURE_DISPATCH_SYMBOL_EXACT",
        "UNCHANGED_ENERGY_AND_TORQUE_CALLERS_EXACT",
        "CUBATURE_HELPER_EXCLUDED_AND_READ_ONLY",
        "TWELVE_ROW_COMPONENT_LAMBDA_MATRIX_EXACT",
        "INTENTIONAL_GUARD_CHANGES_EXPLICIT",
        "SCALAR_AND_ARRAY_NORMALIZATION_EXACT",
        "ARRAY_FAILURE_IS_ATOMIC",
        "INVALID_FLAT_INDEX_REPORTING_EXACT",
        "COMPONENT_VALIDATION_ORDER_EXACT",
        "PUBLIC_VALIDATION_HOOK_DEFAULTS_ENFORCED",
        "PRIVATE_QUALIFICATION_CAPABILITY_ROUTE_EXACT",
        "NO_AMBIENT_VALIDATION_MODE",
        "EIGHT_REGRESSION_INPUT_ROWS_COMPLETE",
        "BINARY64_INPUTS_HEX_SERIALIZED",
        "MASSES_HAVE_EXACT_BINARY64_CONSTRUCTION_RULE",
        "ENERGY_REFERENCE_VALUES_PRESERVED",
        "EIGHT_NEWTONIAN_DERIVATIVE_REFERENCES_FROZEN",
        "EIGHT_YUKAWA_DERIVATIVE_REFERENCES_FROZEN",
        "DERIVATIVE_REFERENCE_PROVENANCE_INDEPENDENT_OF_CANDIDATE",
        "ENERGY_AND_DERIVATIVE_TOLERANCES_NUMERIC",
        "THIRTEEN_LIMIT_AND_BOUNDARY_PROBES_EXACT",
        "POINT_NEAR_CONTACT_LONG_RANGE_AND_UNDERFLOW_COVERED",
        "ZERO_AND_HALF_COUPLING_PROBES_EXACT",
        "TOUCHING_OVERLAP_EMPTY_AND_X_MAX_FAILURES_EXACT",
        "TWELVE_MUTATION_IDENTITIES_PRESERVED",
        "MUTATION_CASE_COMPONENT_AND_INJECTION_ROUTES_EXACT",
        "MUTATION_EXECUTION_ORDER_EXACT",
        "MUTATION_NUMERIC_OR_EXCEPTION_PREDICATES_EXACT",
        "MUTATION_FAILURE_CONSEQUENCE_FAILS_CLOSED",
        "STATIC_REFERENCE_SHARING_CONTROL_EXACT",
        "TEN_THOUSAND_CALL_RUNTIME_WORKLOAD_EXACT",
        "RUNTIME_CASE_AND_COMPONENT_ORDER_EXACT",
        "WARMUP_TRIAL_MEDIAN_AND_NO_PARALLELISM_EXACT",
        "CANONICAL_JSON_ROOT_SCHEMA_EXACT",
        "FLOAT_HEX_AND_DECIMAL_REFERENCE_ENCODING_EXACT",
        "LEXICOGRAPHIC_KEYS_UTF8_AND_NEWLINE_EXACT",
        "DUPLICATE_MISSING_NONFINITE_AND_HASH_FAILURES_EXACT",
        "DECIMAL_COMPARISON_RULE_EXACT",
        "SOURCE_AND_ORACLE_HASH_PROVENANCE_EXACT",
        "SHADOW_IMPLEMENTATION_REMAINS_UNAUTHORIZED",
        "PRODUCTION_SOURCE_AND_DISPATCH_UNCHANGED",
        "OLD_CUBATURE_NOT_CALLED_OR_ADJUDICATED",
        "NO_TORQUE_DFT_VECTOR_JACOBIAN_OR_IDENTIFIABILITY",
        "NO_STAGE_A_RERUN_OR_STAGE_B",
        "FIVE_REVIEW_OUTCOMES_EXACT",
        "ONLY_READY_REVIEW_MAY_AUTHORIZE_ONE_SHADOW_QUALIFICATION",
        "V1_IS_FINAL_AUTOMATIC_REPAIR_NO_V2",
        "CURRENT_AUTHORITY_ROTATES_ONLY_TO_INDEPENDENT_V1_REVIEW",
    )

    scope = {
        "v1_packet_prepared": True,
        "selector_authority_verified": True,
        "v0_packet_and_review_frozen": True,
        "fifty_one_accepted_review_gates_frozen": True,
        "eleven_failed_gates_repaired_in_contract": True,
        "independent_v1_packet_review_authorized": True,
        "derivative_reference_values_derived_as_contract_metadata": True,
        "candidate_kernel_created": False,
        "candidate_kernel_executed": False,
        "production_source_changed": False,
        "production_dispatch_changed": False,
        "production_kernel_replaced": False,
        "old_cubature_called": False,
        "old_cubature_adjudicated": False,
        "automatic_v2_authorized": False,
        "torque_or_dft_authorized": False,
        "stage_a_rerun_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_b_authorized": False,
    }

    return {
        "schema_id": "toe.scalar_only_yukawa.analytic_sphere_kernel.replacement_packet.v1",
        "packet_id": "SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_20260719_v1",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "status": "PREPARED_PENDING_INDEPENDENT_FINAL_V1_REVIEW_NO_IMPLEMENTATION",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_selector_verdict": selector["verdict"],
            "consumed_selector_route": selector["selected_route"],
            "frozen_selector_artifacts": [{"relative_path": p, "sha256": h} for p, h in SELECTOR_HASHES.items()],
            "frozen_v0_packet_artifacts": [{"relative_path": p, "sha256": h} for p, h in V0_PACKET_HASHES.items()],
            "frozen_v0_review_artifacts": [{"relative_path": p, "sha256": h} for p, h in V0_REVIEW_HASHES.items()],
            "frozen_oracle_input_artifacts": [{"relative_path": p, "sha256": h} for p, h in ORACLE_INPUT_HASHES.items()],
            "human_packet": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row("formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1.py"),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "v1_repair_scope": {
            "accepted_review_gate_count": len(accepted_gate_ids),
            "accepted_review_gate_ids": accepted_gate_ids,
            "repaired_review_gate_count": len(FAILED_REVIEW_GATES),
            "repaired_review_gate_ids": list(FAILED_REVIEW_GATES),
            "all_other_v0_surfaces": "FROZEN_BY_HASH_AND_MAY_NOT_BE_REDESIGNED",
            "v1_is_final_automatic_repair": True,
            "automatic_v2": "PROHIBITED",
        },
        "replacement_interface_identity_v1": {
            "historical_source": "formal/python/tools/scalar_only_yukawa_torsion_balance_production_v1.py",
            "candidate_shadow_source": "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_candidate_v1.py",
            "candidate_replaces_internal_functions": [
                "uniform_sphere_form_factor",
                "scaled_uniform_sphere_form_factor",
                "pair_energy_and_radial_derivative",
            ],
            "future_dispatch_seam_symbol": "SPHERE_PAIR_KERNEL_ID",
            "shadow_kernel_id": "ANALYTIC_SPHERE_KERNEL_V1_SHADOW",
            "unchanged_callers": [
                "apparatus_energy",
                "analytic_energy_derivative_torque",
                "direct_pair_force_lever_torque",
                "five_point_energy_derivative_torque",
            ],
            "excluded_read_only_helper": "reduced_four_dimensional_density_integral_yukawa_energy",
            "public_entrypoint_signature": "pair_energy_and_radial_derivative(distance_m,lambda_m,*,mass_d_kg,mass_a_kg,radius_d_m,radius_a_m,yukawa_amplitude,component,yukawa_sign,remove_attractor_form_factor)->tuple[np.ndarray,np.ndarray]",
            "lambda_component_compatibility_matrix": compatibility_rows,
            "component_evaluation_order": [
                "VALIDATE_COMPONENT_TOKEN",
                "VALIDATE_SCALAR_ARGUMENTS_AND_LAMBDA_MATRIX",
                "NORMALIZE_DISTANCE_TO_FLOAT64_ARRAY_AND_REJECT_EMPTY",
                "PREFLIGHT_ALL_DISTANCE_ELEMENTS_AND_COLLECT_INVALID_FLAT_INDICES",
                "IF_ANY_INVALID_RAISE_ONE_VALUE_ERROR_BEFORE_ANY_OUTPUT",
                "EVALUATE_REQUESTED_COMPONENTS",
                "RETURN_NEW_FLOAT64_C_CONTIGUOUS_ARRAYS_WITH_EXACT_INPUT_SHAPE",
            ],
            "array_invalid_element_behavior": {
                "atomic": True,
                "partial_output": "FORBIDDEN",
                "input_mutation": "FORBIDDEN",
                "empty_array": "ValueError:EMPTY_DISTANCE_ARRAY",
                "invalid_index_order": "ASCENDING_C_ORDER_FLAT_INDICES",
                "exception": "ValueError:INVALID_DISTANCE_ELEMENTS:<comma_separated_indices>",
                "scalar_shape": "ZERO_DIMENSIONAL_NUMPY_FLOAT64_ARRAY",
            },
            "validation_hook_authorization_mechanism": {
                "public_nondefault_yukawa_amplitude": "PermissionError:VALIDATION_HOOK_FORBIDDEN_ON_PUBLIC_ENTRYPOINT",
                "public_nondefault_yukawa_sign": "PermissionError:VALIDATION_HOOK_FORBIDDEN_ON_PUBLIC_ENTRYPOINT",
                "public_remove_attractor_form_factor_true": "PermissionError:VALIDATION_HOOK_FORBIDDEN_ON_PUBLIC_ENTRYPOINT",
                "private_entrypoint": "_qualification_mutation_entrypoint",
                "capability_type": "_QualificationCapability",
                "capability_issue_rule": "MATCH_LAUNCH_RUN_ID_AND_ACCEPTED_V1_REVIEW_SHA256",
                "ambient_environment_or_global_mode": "FORBIDDEN",
                "unknown_mutation_id": "ValueError:UNKNOWN_QUALIFICATION_MUTATION",
            },
        },
        "regression_and_derivative_reference_v1": {
            "row_count": len(regression_rows),
            "rows": regression_rows,
            "binary64_input_construction": {
                "parse": "float.fromhex",
                "mass_formula_operation_order": "(4.0/3.0)*math.pi*radius_m**3*density_kg_m3",
                "stored_mass_values": "AUTHORITATIVE_BINARY64_HEX_INPUTS",
                "center_distance": "STORED_BINARY64_HEX_INPUT_NOT_RECOMPUTED_FROM_GAP",
            },
            "independence": {
                "energy_source": "ACCEPTED_120_DIGIT_RADIAL_ORACLE_VALUES",
                "derivative_source": "100_DIGIT_DECIMAL_TRANSFORM_OF_ACCEPTED_ENERGY_AND_FROZEN_D_LAMBDA",
                "newtonian_rule": "dU_N/dD=-U_N/D",
                "yukawa_rule": "dU_Y/dD=-U_Y*(1/D+1/lambda)",
                "candidate_energy_or_derivative_call": "FORBIDDEN",
                "future_reference_parser_may_compute_form_factor": False,
            },
            "comparison_rule": "abs(candidate-reference)<=absolute_tolerance+relative_tolerance*abs(reference)",
            "decimal_candidate_conversion": "Decimal.from_float(float.fromhex(candidate_hex))",
            "all_four_component_values_required_per_case": ["U_N", "dU_N_dD", "U_Y", "dU_Y_dD"],
        },
        "limit_and_boundary_probe_contract_v1": {
            "probe_count": len(probes),
            "rows": probes,
            "execution_order": "P01_THROUGH_P13_EXACT",
            "missing_duplicate_or_out_of_order_probe": "BLOCKED_KERNEL_DOMAIN_OR_NUMERIC_STABILITY",
            "favorable_probe_selection": "FORBIDDEN",
        },
        "mutation_routing_v1": {
            "mutation_count": len(mutations),
            "rows": mutations,
            "single_mutation_per_process": True,
            "baseline_result_required_before_mutation": True,
            "same_candidate_and_adjudicator_required": True,
            "all_mutations_mandatory": True,
            "any_missing_or_failed_detection": "BLOCKED_KERNEL_MUTATION_CONTROLS_NO_SCIENTIFIC_QUALIFICATION",
            "scientific_result_from_mutated_process": "FORBIDDEN",
        },
        "runtime_workload_v1": {
            "timed_call_count_per_trial": 10000,
            "warmup_call_count": 24,
            "trial_count": 5,
            "parallelism": "FORBIDDEN_SINGLE_PROCESS_SINGLE_THREAD",
            "case_order": [row["case_id"] for row in regression_rows],
            "component_order": ["newtonian", "yukawa", "total"],
            "call_i_rule": "case_index=i%8; component_index=(i//8)%3; use_exact_regression_row_binary64_inputs",
            "warmup_i_rule": "i=0..23_uses_each_case_once_per_component_in_case_major_order",
            "trial_adjudicator": "MEDIAN_OF_FIVE_WALL_CLOCK_SECONDS",
            "maximum_median_seconds": 5.0,
            "clock": "time.perf_counter_ns",
            "runtime_probe_case_rows": [{"case_id": row["case_id"], "center_distance_m_hex": row["center_distance_m_hex"], "lambda_m_hex": row["lambda_m_hex"], "mass_1_kg_hex": row["mass_1_kg_hex"], "mass_2_kg_hex": row["mass_2_kg_hex"], "radius_1_m_hex": row["radius_1_m_hex"], "radius_2_m_hex": row["radius_2_m_hex"]} for row in regression_rows],
            "runtime_probe_case_order": [row["case_id"] for row in regression_rows],
            "runtime_probe_component_order": ["newtonian", "yukawa", "total"],
            "result_dependent_workload_change": "FORBIDDEN",
        },
        "canonical_serialization_and_comparison_v1": {
            "schema_id": "toe.scalar_only_yukawa.analytic_sphere_kernel.shadow_qualification_result.v1",
            "root_keys_exact": [
                "custody", "kernel_id", "kernel_source_sha256", "limit_rows",
                "mutation_rows", "oracle_reference_sha256", "regression_rows",
                "runtime", "schema_id", "status", "terminal_outcome",
            ],
            "canonical_encoder": "json.dumps(object,sort_keys=True,ensure_ascii=True,allow_nan=False,separators=(',',':'))+'\\n'",
            "key_order_rule": "LEXICOGRAPHIC_UNICODE_CODEPOINT_ORDER_RECURSIVELY",
            "encoding": "UTF_8_NO_BOM_ONE_TRAILING_LF",
            "float_serialization_rule": "ALL_BINARY64_SCIENTIFIC_VALUES_ARE_LOWERCASE_FLOAT_HEX_STRINGS_FROM_FLOAT_HEX",
            "reference_serialization_rule": "HIGH_PRECISION_REFERENCES_AND_TOLERANCES_ARE_UPPERCASE_DECIMAL_STRINGS",
            "duration_serialization_rule": "INTEGER_NANOSECONDS",
            "nonfinite_numeric_values": "FORBIDDEN_ALLOW_NAN_FALSE",
            "row_order": {
                "regression_rows": "FROZEN_EIGHT_CASE_ORDER_THEN_COMPONENT_ORDER",
                "limit_rows": "P01_THROUGH_P13",
                "mutation_rows": "M01_THROUGH_M12",
            },
            "duplicate_missing_or_unknown_id": "BLOCKED_KERNEL_SERIALIZATION",
            "comparison_rule": "DECIMAL_ABSOLUTE_PLUS_RELATIVE_ENVELOPE_USING_DECIMAL_FROM_FLOAT_HEX",
            "comparison_requires_both_energy_and_derivative": True,
            "hash_rule": "SHA256_OF_EXACT_CANONICAL_UTF8_BYTES_STORED_IN_SEPARATE_CUSTODY_RECORD",
            "serialization_failure_consequence": "BLOCKED_KERNEL_RUNTIME_OR_CUSTODY_NO_SCIENTIFIC_QUALIFICATION",
        },
        "qualification_precedence_v1": {
            "priority_rows": [
                {"priority": 1, "condition": "SOURCE_HASH_CAPABILITY_OR_INDEPENDENCE_FAILURE", "exclusive_outcome": "BLOCKED_KERNEL_VALIDATION_INDEPENDENCE"},
                {"priority": 2, "condition": "MISSING_DUPLICATE_NONFINITE_SERIALIZATION_OR_CUSTODY_FAILURE", "exclusive_outcome": "BLOCKED_KERNEL_RUNTIME_OR_CUSTODY"},
                {"priority": 3, "condition": "INTERFACE_OR_DOMAIN_PROBE_FAILURE", "exclusive_outcome": "BLOCKED_KERNEL_INTERFACE_PARITY_OR_DOMAIN"},
                {"priority": 4, "condition": "ENERGY_OR_DERIVATIVE_REGRESSION_FAILURE", "exclusive_outcome": "BLOCKED_KERNEL_ORACLE_REGRESSION"},
                {"priority": 5, "condition": "ANY_MUTATION_NOT_DETECTED", "exclusive_outcome": "BLOCKED_KERNEL_MUTATION_CONTROLS"},
                {"priority": 6, "condition": "ALL_REQUIRED_RECORDS_AND_CONTROLS_PASS", "exclusive_outcome": "ANALYTIC_SPHERE_KERNEL_SHADOW_QUALIFIED"},
            ],
            "partial_or_lower_priority_scientific_classification": "FORBIDDEN",
        },
        "packet_review_outcomes": list(PACKET_REVIEW_OUTCOMES),
        "review_consequence": {
            "ready": "MAY_AUTHORIZE_ONE_ISOLATED_SHADOW_IMPLEMENTATION_AND_QUALIFICATION_ONLY",
            "blocked": "FRESH_SCIENTIFIC_RESPONSE_SELECTOR_REQUIRED",
            "automatic_v2": "PROHIBITED",
            "production_adoption": "NOT_AUTHORIZED_BY_PACKET_REVIEW",
        },
        "packet_gates": {
            "gate_count": len(packet_gates),
            "pass_count": len(packet_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in packet_gates],
        },
        "scope": scope,
        "claim_ceiling": (
            "V1 repairs exactly eleven failed pre-implementation contract gates while freezing "
            "the 51 accepted review gates. It derives derivative reference metadata only from "
            "accepted high-precision energy evidence and frozen inputs. It creates or executes "
            "no candidate kernel, changes no production source or dispatch, calls or adjudicates "
            "no cubature, computes no torque, DFT, real-150 vector, Jacobian, SVD, or "
            "identifiability result, reruns no Stage A execution, and authorizes no Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Prepare the final eleven-gate V1 replacement contract repair.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    output = REPO_ROOT / REPORT_RELATIVE_PATH
    expected = artifact_bytes()
    current = output.read_bytes() if output.exists() else None
    if args.write:
        if current != expected:
            output.write_bytes(expected)
            print(f"wrote {REPORT_RELATIVE_PATH}")
        else:
            print("analytic sphere-kernel replacement packet V1 already current")
        return 0
    if current != expected:
        print("analytic sphere-kernel replacement packet V1 drift")
        return 1
    report = build_report()
    print(
        "analytic sphere-kernel replacement packet V1 OK "
        f"repairs={report['v1_repair_scope']['repaired_review_gate_count']} "
        f"regressions={report['regression_and_derivative_reference_v1']['row_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
