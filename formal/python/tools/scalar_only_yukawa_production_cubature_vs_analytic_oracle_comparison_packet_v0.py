from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_production_cubature_vs_"
    "analytic_oracle_comparison_packet_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaProductionCubatureVsAnalyticOracleComparisonPacketV0.lean"
)
SELECTOR_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_V0_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_SELECTION_"
    "20260719_v0.json"
)
ORACLE_PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_PACKET_20260719_v0.json"
)
ORACLE_EXECUTION_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_EXECUTION_20260719_v0.json"
)
ORACLE_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_EXECUTION_RESULT_REVIEW_20260719_v0.json"
)
STAGE_A_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_EXECUTION_RESULT_REVIEW_20260719_v1.json"
)

TARGET = (
    "prepare_scalar_only_yukawa_production_cubature_vs_analytic_oracle_"
    "comparison_packet_v0"
)
VERDICT = (
    "PREPARED_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_"
    "COMPARISON_PACKET_V0"
)
SELECTED_NEXT_TARGET = (
    "review_scalar_only_yukawa_production_cubature_vs_analytic_oracle_"
    "comparison_packet_v0_result"
)
SELECTED_NEXT_TARGET_KIND = (
    "INDEPENDENT_PACKET_REVIEW_ONLY_NO_PRODUCTION_COMPARISON_EXECUTION"
)

SELECTOR_HASHES = {
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_V0_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.md":
        "7f3007c16f0c0a9aa3ac06fea5434649cd26f558b5dcab48d7296738a3fa1043",
    SELECTOR_RELATIVE_PATH:
        "d55cabd9974e700fc8d38d3853de0acaef1c5c9554b0f09d5f26de3e51733efc",
    "formal/python/tools/post_scalar_only_yukawa_analytic_sphere_oracle_qualification_v0_execution_result_scientific_response_selection_v0.py":
        "2f8688392eeeeb50e498adaa82b7011267da5f1aeffdbf7070db30b4ab98e22f",
    "formal/python/tests/test_post_scalar_only_yukawa_analytic_sphere_oracle_qualification_v0_execution_result_scientific_response_selection_v0.py":
        "5356a9a700394e64f85d407276c502e98030e1ff234c40fb5e8b9c6bef214f59",
    "formal/toe_formal/ToeFormal/Derivation/PostScalarOnlyYukawaAnalyticSphereOracleQualificationV0ExecutionResultScientificResponseSelectionV0.lean":
        "61886f4b1b45d6a1b433d8ff91d5b3099ce0d9effcdc322768ebed148b8e94bd",
}

SCIENTIFIC_PATH_HASHES = {
    "formal/python/tools/scalar_only_yukawa_torsion_balance_production_v1.py":
        "4995c467f766466583c53c7904e2f1bb35b7c02970aece4a20e2315403ed8cac",
    "formal/python/tools/scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_v1.py":
        "ec0209a433027d8e8523d9e0f21ba3662ccec559de33ea042cb0a765b64571ae",
    "formal/python/tools/scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0.py":
        "c7faf54b21904349c628fc4f2df4ee703ecdd6fbed7fd0c2777bc09c5055e45d",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_v0.py":
        "5d357f9346a3c6bf6168d6330ff1fb62017ac3eda90e05e57605f23392be17eb",
    ORACLE_PACKET_RELATIVE_PATH:
        "8e2e93963182a27b1618c0fe1d02aa34eb8740f4a422429a041f2bcc02323bb5",
    ORACLE_EXECUTION_RELATIVE_PATH:
        "d2527fd3c03a107734b3b55920c35f73185cbbf0f6c13132ff94c40ec447676d",
    ORACLE_REVIEW_RELATIVE_PATH:
        "e963c033514e47e374cb6caced1ab533ed6ea08792f964c04e079e7b67088868",
    STAGE_A_REVIEW_RELATIVE_PATH:
        "c6a7278025714753144e429d47fe065eb8a40bdd8d45e3f609a25c0ffd6aa968",
}

ORDERS = (8, 16, 24, 32, 40, 48)
CASE_IDS = (
    "LEGACY_STAGE_A_00_LARGE_X",
    "LEGACY_STAGE_A_01_TRANSITION",
    "LEGACY_STAGE_A_02_LONG_RANGE",
    "SMALL_X_UNEQUAL_WIDE",
    "MIXED_X_UNEQUAL",
    "SMALL_GAP_LARGE_X",
    "EXTREME_X_1000_UNEQUAL",
    "LONG_RANGE_UNEQUAL_WIDE",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _function_names(relative_path: str) -> set[str]:
    tree = ast.parse((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    return {
        node.name for node in ast.walk(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }


def _frozen_cases(oracle_packet: dict[str, Any]) -> list[dict[str, Any]]:
    rows_by_id = {
        row["case_id"]: row for row in oracle_packet["representative_domain"]["rows"]
    }
    if tuple(rows_by_id) != CASE_IDS:
        raise ValueError("accepted oracle case ordering drifted")
    rows = []
    for case_id in CASE_IDS:
        source = rows_by_id[case_id]
        if source["strictly_nonoverlapping"] is not True:
            raise ValueError(f"non-overlap failed: {case_id}")
        gap = float(source["center_distance_m"]) - float(source["radius_1_m"]) - float(
            source["radius_2_m"]
        )
        if abs(gap - float(source["surface_gap_m"])) > 1e-15 or gap <= 0.0:
            raise ValueError(f"gap reconstruction failed: {case_id}")
        row = dict(source)
        row["comparison_role"] = (
            "EXACT_STAGE_A_FAILURE_REPLAY"
            if "FAILED_STAGE_A_CONFIGURATION" in source["roles"]
            else "QUALIFIED_ORACLE_STRATUM"
        )
        rows.append(row)
    return rows


def build_report() -> dict[str, Any]:
    for collection_name, collection in (
        ("selector", SELECTOR_HASHES),
        ("scientific path", SCIENTIFIC_PATH_HASHES),
    ):
        for relative_path, expected in collection.items():
            path = REPO_ROOT / relative_path
            if not path.exists() or _sha256(path) != expected:
                raise ValueError(f"{collection_name} custody failed: {relative_path}")

    selector = _load_json(SELECTOR_RELATIVE_PATH)
    oracle_packet = _load_json(ORACLE_PACKET_RELATIVE_PATH)
    oracle_execution = _load_json(ORACLE_EXECUTION_RELATIVE_PATH)
    oracle_review = _load_json(ORACLE_REVIEW_RELATIVE_PATH)
    stage_a_review = _load_json(STAGE_A_REVIEW_RELATIVE_PATH)
    if selector["selected_next_target"] != TARGET:
        raise ValueError("selector does not authorize this packet")
    if selector["selected_route"] != (
        "COMPARE_FAILED_PRODUCTION_CUBATURE_AGAINST_QUALIFIED_ANALYTIC_ORACLE"
    ):
        raise ValueError("unexpected selected route")
    if oracle_review["verdict"] != "ACCEPTED_ANALYTIC_SPHERE_ORACLE_QUALIFIED":
        raise ValueError("analytic oracle has not been accepted")
    if stage_a_review["accepted_bounded_claim"]["uniform_sphere_validation"] != "FAILED":
        raise ValueError("Stage A production-kernel failure is not frozen")
    if oracle_execution["principal_result"] != "ANALYTIC_SPHERE_ORACLE_QUALIFIED":
        raise ValueError("oracle execution result drifted")

    production_names = _function_names(
        "formal/python/tools/scalar_only_yukawa_torsion_balance_production_v1.py"
    )
    diagnostic_names = _function_names(
        "formal/python/tools/scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0.py"
    )
    oracle_names = _function_names(
        "formal/python/tools/scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_v0.py"
    )
    required_production_functions = {
        "sphere_mass",
        "pair_energy_and_radial_derivative",
        "reduced_four_dimensional_density_integral_yukawa_energy",
    }
    if not required_production_functions <= production_names:
        raise ValueError("frozen Stage A production functions missing")
    if "_fixed_density_integral" not in diagnostic_names:
        raise ValueError("frozen parameterized fixed-tensor mirror missing")
    if not {"_uy_stable_float", "_radial_h"} <= oracle_names:
        raise ValueError("accepted oracle functions missing")

    cases = _frozen_cases(oracle_packet)
    required_roles = {
        "FAILED_STAGE_A_CONFIGURATION",
        "WIDE_SEPARATION",
        "SMALL_POSITIVE_GAP",
        "TRANSITION_DOMAIN",
        "LONG_RANGE",
        "LARGE_X",
        "SMALL_X",
    }
    observed_roles = {role for row in cases for role in row["roles"]}
    if not required_roles <= observed_roles:
        raise ValueError("frozen case roles do not cover required regimes")

    metrics = {
        "absolute_error_J": "abs(U_production_n-U_oracle)",
        "relative_error": (
            "abs(U_production_n-U_oracle)/max(abs(U_oracle),U_floor_J)"
        ),
        "signed_ratio": "U_production_n/U_oracle_when_abs_U_oracle_gt_U_floor_J",
        "convergence_ratio": "q_n=epsilon_n/epsilon_previous_when_epsilon_previous_gt_0",
        "oracle_floor_J": 1e-36,
        "accuracy_absolute_tolerance_J": 1e-36,
        "accuracy_relative_tolerance": 1e-6,
        "accuracy_rule": "absolute_error_J<=1e-36+1e-6*abs(U_oracle)",
        "accuracy_is_component_case_and_order_specific": True,
        "order_48_is_never_a_reference": True,
        "combined_energy_may_decide_component_accuracy": False,
    }

    classification_contract = {
        "multilabel_reporting_permitted": True,
        "near_threshold_default": "PRODUCTION_FAILURE_NOT_LOCALIZED",
        "predicates": {
            "PRODUCTION_CUBATURE_VALIDATED_ON_TESTED_CASES": (
                "both components pass accuracy_rule for every case at orders 32,40,48 "
                "and abs(P48-P40)<=1e-36+1e-6*abs(oracle)"
            ),
            "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED": (
                "at least four cases fail at orders 32,40,48 and their signed ratios over "
                "orders 32,40,48 have relative spread<=0.005 with median abs(ratio-1)>=0.001"
            ),
            "YUKAWA_SPECIFIC_IMPLEMENTATION_DEFECT_INDICATED": (
                "Newtonian passes every case at orders 32,40,48 while Yukawa fails at "
                "least one case at all three orders with a matched Yukawa mutation fingerprint"
            ),
            "FIXED_ORDER_CUBATURE_INADEQUATE": (
                "at least one required component-case fails at order48 and, over orders "
                "24,32,40,48, errors either increase by >=5% once or have two q_n>=0.95"
            ),
            "SLOW_BUT_CONVERGENT_AND_ECONOMICALLY_INFERIOR": (
                "at least one required component-case fails at order48, errors strictly "
                "decrease over orders 16,24,32,40,48 with every q_n<0.95, and the fitted "
                "order/runtime needed for accuracy exceeds the frozen work envelope"
            ),
            "REGIME_DEPENDENT_PRODUCTION_FAILURE": (
                "the same component passes orders 32,40,48 in at least one frozen regime "
                "and fails all three orders in at least one other frozen regime"
            ),
            "NEAR_CONTACT_OR_TRANSITION_REGIME_UNDERSAMPLED": (
                "REGIME_DEPENDENT_PRODUCTION_FAILURE holds, every failing small-gap or "
                "transition case has q_40>=0.95 or q_48>=0.95, and at least one wide "
                "long-range case passes orders 32,40,48"
            ),
            "PRODUCTION_FAILURE_NOT_LOCALIZED": (
                "one or more component-cases fail accuracy but no other registered root-cause "
                "predicate is fully satisfied"
            ),
            "PRODUCTION_COMPARISON_TIMEOUT": (
                "the total, per-stage, per-case, or per-order work cap is exceeded or any "
                "required atomic comparison cell is missing"
            ),
        },
        "post_result_predicate_change": "FORBIDDEN",
        "visual_trend_classification": "FORBIDDEN",
        "favorable_rounding": "FORBIDDEN",
    }

    controls = [
        {
            "control_id": "C01_POINT_EQUIVALENT_NEWTONIAN",
            "mutation": "NONE",
            "required_detection": "production Newtonian companion and shell oracle agree in the point-equivalent limit",
        },
        {
            "control_id": "C02_MISSING_A_Y_ONE_THIRD",
            "mutation": "set A_Y=1",
            "required_detection": "YUKAWA_SPECIFIC_IMPLEMENTATION_DEFECT_INDICATED",
        },
        {
            "control_id": "C03_GAP_FOR_CENTER_DISTANCE",
            "mutation": "replace D by g in kernel denominator or exponential",
            "required_detection": "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED",
        },
        {
            "control_id": "C04_RADIUS_AS_DIAMETER",
            "mutation": "replace each R by 2R on production input",
            "required_detection": "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED",
        },
        {
            "control_id": "C05_ONE_DIMENSION_UNREFINED",
            "mutation": "hold mu2 order at 8 while metadata order increases",
            "required_detection": "FIXED_ORDER_CUBATURE_INADEQUATE",
        },
        {
            "control_id": "C06_WEIGHT_NORMALIZATION_BIAS",
            "mutation": "multiply every production quadrature weight product by 1.01",
            "required_detection": "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED",
        },
        {
            "control_id": "C07_COMPONENT_CHANNEL_SWAP",
            "mutation": "swap Newtonian and Yukawa output labels",
            "required_detection": "CHANNEL_IDENTITY_FIREWALL",
        },
        {
            "control_id": "C08_ORDER_METADATA_OVERCLAIM",
            "mutation": "record order48 metadata for an order40 evaluation",
            "required_detection": "ORDER_CUSTODY_FIREWALL",
        },
        {
            "control_id": "C09_ORACLE_OVERWRITE",
            "mutation": "write production value into oracle field",
            "required_detection": "ORACLE_IMMUTABILITY_FIREWALL",
        },
        {
            "control_id": "C10_CONSTANT_MULTIPLICATIVE_BIAS",
            "mutation": "multiply every production component by 1.02 after integration",
            "required_detection": "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED",
        },
    ]

    stages = [
        {"stage_id": "P1_CUSTODY_AND_STATIC_IDENTITY", "cap_seconds": 20},
        {"stage_id": "P2_TEN_PRODUCTION_PATH_CONTROLS", "cap_seconds": 120},
        {"stage_id": "P3_ORDERS_8_16_24", "cap_seconds": 300},
        {"stage_id": "P4_ORDERS_32_40_48", "cap_seconds": 600},
        {"stage_id": "P5_METRICS_AND_CLASSIFICATION", "cap_seconds": 60},
        {"stage_id": "P6_ATOMIC_SERIALIZATION_AND_FIREWALL", "cap_seconds": 20},
    ]
    resource_contract = {
        "maximum_total_wall_clock_seconds": 1200,
        "maximum_memory_mib": 4096,
        "per_order_cell_caps_seconds": {
            "8": 2,
            "16": 5,
            "24": 10,
            "32": 20,
            "40": 40,
            "48": 60,
        },
        "stage_caps": stages,
        "sum_of_stage_caps_seconds": sum(row["cap_seconds"] for row in stages),
        "process_group_termination": "MANDATORY",
        "raw_launcher_transcript": "PRESERVED",
        "per_case_order_component_atomic_records": "REQUIRED",
        "timeout_and_child_termination_timestamps": "REQUIRED",
        "zero_surviving_processes": "REQUIRED",
        "budget_exhaustion_behavior": "FAIL_CLOSED_PRODUCTION_COMPARISON_TIMEOUT",
        "result_dependent_budget_change": "FORBIDDEN",
    }

    packet_review_outcomes = [
        "PRODUCTION_COMPARISON_CONTRACT_READY",
        "BLOCKED_PRODUCTION_PATH_IDENTITY",
        "BLOCKED_ORACLE_CUSTODY",
        "BLOCKED_CASE_GRID_CONTRACT",
        "BLOCKED_METRIC_OR_CLASSIFICATION_CONTRACT",
        "BLOCKED_MUTATION_ROUTING",
        "BLOCKED_RESOURCE_OR_CUSTODY_CONTRACT",
        "BLOCKED_SCOPE_OR_PROVENANCE",
    ]
    gates = (
        "SELECTOR_HASHES_MATCH",
        "SCIENTIFIC_PATH_HASHES_MATCH",
        "ACCEPTED_ORACLE_REVIEW_FROZEN",
        "STAGE_A_KERNEL_FAILURE_FROZEN",
        "PRODUCTION_REMAINS_UNADJUDICATED",
        "EXACT_STAGE_A_YUKAWA_FUNCTION_PRESENT",
        "PARAMETERIZED_FIXED_TENSOR_MIRROR_PRESENT",
        "ORACLE_FUNCTIONS_PRESENT",
        "EIGHT_ACCEPTED_ORACLE_CASES_FROZEN",
        "THREE_STAGE_A_FAILURE_CASES_FROZEN",
        "STRICT_NONOVERLAP_REPRODUCED",
        "SHORT_TRANSITION_LONG_AND_WIDE_ROLES_COVERED",
        "ORDERS_8_16_24_32_40_48_FROZEN",
        "NEWTONIAN_AND_YUKAWA_CHANNELS_SEPARATE",
        "COMBINED_ENERGY_NON_DECISION_BEARING",
        "ABSOLUTE_ERROR_FORMULA_FROZEN",
        "RELATIVE_ERROR_FLOOR_FROZEN",
        "ACCURACY_TOLERANCE_FROZEN",
        "CONVERGENCE_RATIO_FROZEN",
        "ORDER48_NOT_AN_ORACLE",
        "MULTI_ORDER_TREND_REQUIRED",
        "NINE_TERMINAL_CLASSIFICATION_PREDICATES_FROZEN",
        "MULTILABEL_REPORTING_EXPLICIT",
        "NEAR_THRESHOLD_UNRESOLVED",
        "TEN_LIVE_PATH_CONTROLS_FROZEN",
        "ORDER_METADATA_CUSTODY_CONTROL_FROZEN",
        "ORACLE_IMMUTABILITY_CONTROL_FROZEN",
        "PRODUCTION_AND_ORACLE_CODE_CHANGES_FORBIDDEN",
        "PER_CELL_RUNTIME_WORK_AND_MEMORY_RECORDS_REQUIRED",
        "SIX_STAGE_RESOURCE_ENVELOPE_COHERENT",
        "PROCESS_GROUP_AND_ATOMIC_CUSTODY_REQUIRED",
        "NO_PACKET_EXECUTION_NOW",
        "NO_PRODUCTION_REPAIR_OR_REPLACEMENT",
        "NO_TORQUE_OR_DFT",
        "NO_VECTOR_JACOBIAN_IDENTIFIABILITY_OR_STAGE_B",
        "INDEPENDENT_PACKET_REVIEW_REQUIRED",
    )

    return {
        "schema_id": (
            "toe.scalar_only_yukawa.production_cubature_vs_analytic_oracle."
            "comparison_packet.v0"
        ),
        "packet_id": (
            "SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_"
            "COMPARISON_PACKET_20260719_v0"
        ),
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "status": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_selection_verdict": selector["verdict"],
            "frozen_selector_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in SELECTOR_HASHES.items()
            ],
            "frozen_scientific_paths": [
                {"relative_path": path, "sha256": digest}
                for path, digest in SCIENTIFIC_PATH_HASHES.items()
            ],
            "human_packet": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_production_cubature_vs_"
                "analytic_oracle_comparison_packet_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
            "authorized_comparison_execution_count_after_review": 1,
            "performed_comparison_execution_count": 0,
        },
        "accepted_inputs": {
            "analytic_oracle": "QUALIFIED_AND_ACCEPTED",
            "oracle_maximum_relative_difference": oracle_review["accepted_result"][
                "maximum_relative_difference"
            ],
            "production_cubature": "UNADJUDICATED",
            "stage_a_uniform_sphere_validation": "FAILED",
            "stage_a_production_vs_order24_error": stage_a_review[
                "independent_reproduction"
            ]["benchmark_reproduction"]["uniform_sphere_production_vs_order24_error"],
            "stage_a_order16_vs_order24_error": stage_a_review[
                "independent_reproduction"
            ]["benchmark_reproduction"]["uniform_sphere_order16_vs_order24_error"],
        },
        "production_path_identity": {
            "stage_a_module": "scalar_only_yukawa_torsion_balance_production_v1.py",
            "stage_a_yukawa_function": (
                "reduced_four_dimensional_density_integral_yukawa_energy"
            ),
            "parameterized_mirror_module": (
                "scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0.py"
            ),
            "parameterized_mirror_function": "_fixed_density_integral",
            "dimensions_refined_together": ["r1", "mu1", "r2", "mu2"],
            "quadrature": "GAUSS_LEGENDRE_TENSOR_PRODUCT_BINARY64",
            "summation": "PAIRWISE_NUMPY_BINARY64",
            "newtonian_channel_qualification": (
                "PARAMETERIZED_COMPANION_DIAGNOSTIC_USING_THE_SAME_FROZEN_NODES_"
                "WEIGHTS_COORDINATE_MAP_AND_VOLUME_NORMALIZATION;_NOT_A_SEPARATE_"
                "STAGE_A_SCIENTIFIC_OUTPUT"
            ),
            "legacy_equivalence_control_required": True,
            "production_repair_or_algorithm_change": "FORBIDDEN",
        },
        "oracle_path_identity": {
            "module": "scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_v0.py",
            "energy_function": "_uy_stable_float",
            "radial_function": "_radial_h",
            "oracle_values_read_only": True,
            "production_import_into_oracle": "FORBIDDEN",
        },
        "comparison_domain": {
            "case_count": len(cases),
            "case_ids": list(CASE_IDS),
            "orders": list(ORDERS),
            "component_count": 2,
            "components": ["NEWTONIAN", "YUKAWA"],
            "required_atomic_scientific_cells": len(cases) * len(ORDERS) * 2,
            "rows": cases,
            "post_result_case_or_order_change": "FORBIDDEN",
        },
        "metric_contract": metrics,
        "classification_contract": classification_contract,
        "controls": {
            "control_count": len(controls),
            "all_use_production_comparison_pipeline": True,
            "rows": controls,
        },
        "resource_and_custody_contract": resource_contract,
        "packet_review_outcomes": packet_review_outcomes,
        "packet_gates": {
            "gate_count": len(gates),
            "pass_count": len(gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in gates],
        },
        "scope": {
            "comparison_packet_prepared": True,
            "independent_packet_review_performed": False,
            "production_comparison_executed": False,
            "oracle_rerun_performed": False,
            "production_kernel_repaired": False,
            "production_kernel_replaced": False,
            "torque_computed": False,
            "angular_dft_computed": False,
            "final_real_150_vector_computed": False,
            "jacobian_or_svd_computed": False,
            "identifiability_computed": False,
            "stage_a_rerun_performed": False,
            "stage_b_performed": False,
        },
        "claim_ceiling": (
            "This packet prepares an energy-level comparison contract only. It performs "
            "no production calculation, adjudicates or changes no kernel, computes no "
            "torque or harmonics, reruns no Stage A, decides no identifiability question, "
            "and authorizes no Stage B work before independent packet review."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the bounded production-cubature versus analytic-oracle comparison packet."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    rendered = artifact_bytes()
    if args.write:
        path.write_bytes(rendered)
        print(f"wrote {REPORT_RELATIVE_PATH} verdict={VERDICT}")
        return 0
    if not path.exists() or path.read_bytes() != rendered:
        print("production-vs-oracle comparison packet artifact missing or stale")
        return 1
    report = json.loads(path.read_text(encoding="utf-8"))
    print(
        "production-vs-oracle comparison packet OK "
        f"cases={report['comparison_domain']['case_count']} "
        f"gates={report['packet_gates']['pass_count']}/"
        f"{report['packet_gates']['gate_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
