from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_20260719_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_REVIEW_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_REVIEW_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_production_cubature_vs_"
    "analytic_oracle_comparison_packet_review_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaProductionCubatureVsAnalyticOracleComparisonPacketReviewV0.lean"
)

TARGET = (
    "review_scalar_only_yukawa_production_cubature_vs_analytic_oracle_"
    "comparison_packet_v0_result"
)
VERDICT = "BLOCKED_PRODUCTION_COMPARISON_CONTRACT_INCOMPLETE"
PRINCIPAL_OUTCOME = "BLOCKED_PRODUCTION_PATH_IDENTITY"
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_yukawa_production_cubature_vs_analytic_oracle_"
    "comparison_packet_review_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "SCIENTIFIC_RESPONSE_SELECTION_ONLY_NO_PACKET_REPAIR_OR_COMPARISON_EXECUTION"
)

PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_COMPARISON_PACKET_20260719_v0.md":
        "255208335825d75616f27cd76df09f7743092ffc2b8a766e484d041c89acea1c",
    PACKET_RELATIVE_PATH:
        "e8a3a610b60749386758c7b666cd20f3f80dd96fb3571a99250055fedb7062a7",
    "formal/python/tools/scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v0.py":
        "87313c439a7841af21828b26483a74daa00d25e4487c4c9765de7c58aed09193",
    "formal/python/tests/test_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v0.py":
        "52558c1d185698800260f45e2401342763872da36bd9807621faf5242a65ef29",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaProductionCubatureVsAnalyticOracleComparisonPacketV0.lean":
        "67a5ae19cc0c300bd6d47546f14f073f514962147cd96cd010fb46b10acf11a8",
}

DIAGNOSTICS = (
    "MIRROR_ACCUMULATION_DIFFERS_FROM_HISTORICAL_STAGE_A",
    "UNEQUAL_RADIUS_MIRROR_SCOPE_NOT_SEPARATED_FROM_HISTORICAL_ADJUDICATION",
    "LEGACY_EQUIVALENCE_TOLERANCE_AND_FAILURE_BEHAVIOR_NOT_FROZEN",
    "SLOW_CONVERGENCE_FIT_AND_ECONOMIC_PREDICATE_UNDEFINED",
    "MUTATION_FINGERPRINT_MATCH_RULE_UNDEFINED",
    "CONTROL_CASE_ORDER_AND_TOLERANCE_ROUTING_UNFROZEN",
    "INCOMPLETE_RECORD_CLASSIFICATION_PRECEDENCE_UNFROZEN",
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


def _function_source(relative_path: str, function_name: str) -> str:
    source = (REPO_ROOT / relative_path).read_text(encoding="utf-8")
    tree = ast.parse(source)
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == function_name:
            segment = ast.get_source_segment(source, node)
            if segment is None:
                raise ValueError(f"cannot extract function: {function_name}")
            return segment
    raise ValueError(f"missing function: {function_name}")


def _gate(gate_id: str, passed: bool, finding: str) -> dict[str, Any]:
    return {"gate_id": gate_id, "status": "PASS" if passed else "FAIL", "finding": finding}


def build_review() -> dict[str, Any]:
    frozen = []
    for relative_path, expected in PACKET_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"comparison packet custody drift: {relative_path}")
        frozen.append({"relative_path": relative_path, "sha256": observed})
    packet = _load_json(PACKET_RELATIVE_PATH)
    if packet["selected_next_target"] != TARGET:
        raise ValueError("packet does not rotate to this review")
    if packet["status"] != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("packet is not pending independent review")
    if packet["scope"]["production_comparison_executed"] is not False:
        raise ValueError("packet preparation unexpectedly executed the comparison")

    historical_source = _function_source(
        "formal/python/tools/scalar_only_yukawa_torsion_balance_production_v1.py",
        "reduced_four_dimensional_density_integral_yukawa_energy",
    )
    mirror_source = _function_source(
        "formal/python/tools/scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0.py",
        "_fixed_density_integral",
    )
    historical_identity = {
        "uses_sequential_outer_accumulation": "total +=" in historical_source,
        "uses_fixed_equal_radius_constants": (
            "RADIUS_D" in historical_source and "RADIUS_A" in historical_source
        ),
        "uses_one_order_for_all_dimensions": "leggauss(order)" in historical_source,
        "function_sha256": hashlib.sha256(historical_source.encode("utf-8")).hexdigest(),
    }
    mirror_identity = {
        "uses_block_list_accumulation": (
            "newton_blocks" in mirror_source and "yukawa_blocks" in mirror_source
        ),
        "pairwise_is_default": 'summation: str = "PAIRWISE"' in mirror_source,
        "ordinary_mode_exists": 'summation == "ORDINARY"' in mirror_source,
        "parameterizes_unequal_radii": (
            'case["radius_1_m"]' in mirror_source and 'case["radius_2_m"]' in mirror_source
        ),
        "mixed_dimension_mutation_exists": "mixed_mu2_order" in mirror_source,
        "function_sha256": hashlib.sha256(mirror_source.encode("utf-8")).hexdigest(),
    }
    path_audit = {
        "historical": historical_identity,
        "mirror": mirror_identity,
        "accumulation_algorithm_identical_as_frozen": False,
        "physical_input_domain_identical_as_frozen": False,
        "packet_declares_legacy_equivalence_control": packet["production_path_identity"][
            "legacy_equivalence_control_required"
        ],
        "legacy_equivalence_tolerance_present": False,
        "legacy_equivalence_failure_behavior_present": False,
        "historical_decision_bearing_cases_separated_from_mirror_only_cases": False,
        "finding": (
            "The historical Stage A function performs sequential outer accumulation on "
            "fixed equal radii. The mirror defaults to block-list NumPy pairwise summation "
            "and parameterizes unequal radii. A legacy-equivalence control is named but "
            "has no frozen tolerance, cases/orders, or failure consequence."
        ),
    }

    domain = packet["comparison_domain"]
    case_rows = domain["rows"]
    case_audit = {
        "case_count": len(case_rows),
        "case_ids_exact": [row["case_id"] for row in case_rows] == domain["case_ids"],
        "legacy_case_count": sum(
            row["comparison_role"] == "EXACT_STAGE_A_FAILURE_REPLAY" for row in case_rows
        ),
        "strict_nonoverlap": all(
            float(row["center_distance_m"])
            > float(row["radius_1_m"]) + float(row["radius_2_m"])
            and float(row["surface_gap_m"]) > 0.0
            for row in case_rows
        ),
        "gap_reconstruction_max_error_m": max(
            abs(
                float(row["center_distance_m"])
                - float(row["radius_1_m"])
                - float(row["radius_2_m"])
                - float(row["surface_gap_m"])
            )
            for row in case_rows
        ),
        "orders_exact": domain["orders"] == [8, 16, 24, 32, 40, 48],
        "components_exact": domain["components"] == ["NEWTONIAN", "YUKAWA"],
        "atomic_cell_count_reproduced": (
            len(case_rows) * len(domain["orders"]) * len(domain["components"])
        ),
    }

    metrics = packet["metric_contract"]
    classifications = packet["classification_contract"]
    predicates = classifications["predicates"]
    classification_audit = {
        "predicate_count": len(predicates),
        "accuracy_rule_complete": (
            metrics["accuracy_absolute_tolerance_J"] == 1e-36
            and metrics["accuracy_relative_tolerance"] == 1e-6
        ),
        "order48_not_reference": metrics["order_48_is_never_a_reference"],
        "validated_predicate_multi_order": all(
            token in predicates["PRODUCTION_CUBATURE_VALIDATED_ON_TESTED_CASES"]
            for token in ("32", "40", "48")
        ),
        "fixed_order_predicate_multi_order": all(
            token in predicates["FIXED_ORDER_CUBATURE_INADEQUATE"]
            for token in ("24", "32", "40", "48")
        ),
        "slow_fit_method_frozen": False,
        "economic_projection_rule_frozen": False,
        "mutation_fingerprint_distance_and_tolerance_frozen": False,
        "systematic_bias_component_grouping_frozen": False,
        "timeout_suppresses_partial_scientific_labels": False,
        "multilabel_permitted": classifications["multilabel_reporting_permitted"],
        "near_threshold_unresolved": (
            classifications["near_threshold_default"] == "PRODUCTION_FAILURE_NOT_LOCALIZED"
        ),
        "post_result_changes_forbidden": (
            classifications["post_result_predicate_change"] == "FORBIDDEN"
            and classifications["visual_trend_classification"] == "FORBIDDEN"
            and classifications["favorable_rounding"] == "FORBIDDEN"
        ),
    }

    controls = packet["controls"]
    control_rows = controls["rows"]
    control_audit = {
        "control_count": len(control_rows),
        "ids_unique": len({row["control_id"] for row in control_rows}) == len(control_rows),
        "live_pipeline_asserted": controls["all_use_production_comparison_pipeline"],
        "case_ids_frozen_per_control": all("case_ids" in row for row in control_rows),
        "orders_frozen_per_control": all("orders" in row for row in control_rows),
        "acceptance_tolerances_frozen_per_control": all(
            "acceptance_rule" in row for row in control_rows
        ),
        "legacy_equivalence_control_is_one_of_ten": any(
            row["control_id"] == "C00_LEGACY_EQUIVALENCE" for row in control_rows
        ),
        "metadata_and_oracle_firewalls_present": {
            "C08_ORDER_METADATA_OVERCLAIM",
            "C09_ORACLE_OVERWRITE",
        } <= {row["control_id"] for row in control_rows},
        "finding": (
            "The mutations name expected effects, but do not freeze their case IDs, "
            "orders, numerical acceptance rules, or exact legacy-equivalence routing."
        ),
    }

    resource = packet["resource_and_custody_contract"]
    resource_audit = {
        "total_seconds": resource["maximum_total_wall_clock_seconds"],
        "memory_mib": resource["maximum_memory_mib"],
        "stage_count": len(resource["stage_caps"]),
        "stage_cap_sum_seconds": sum(row["cap_seconds"] for row in resource["stage_caps"]),
        "per_order_cap_keys": sorted(int(key) for key in resource["per_order_cell_caps_seconds"]),
        "process_group_required": resource["process_group_termination"] == "MANDATORY",
        "atomic_records_required": (
            resource["per_case_order_component_atomic_records"] == "REQUIRED"
        ),
        "zero_survivors_required": resource["zero_surviving_processes"] == "REQUIRED",
        "fails_closed": (
            resource["budget_exhaustion_behavior"]
            == "FAIL_CLOSED_PRODUCTION_COMPARISON_TIMEOUT"
        ),
        "full_record_set_required_for_scientific_classification": False,
    }

    gates = [
        _gate("R01_EXACT_PACKET_CUSTODY_AND_TARGET", True, "five packet surfaces hash-verified"),
        _gate("R02_PENDING_REVIEW_AND_NO_EXECUTION", not packet["scope"]["production_comparison_executed"], "packet preparation generated no cubature values"),
        _gate("R03_ACCEPTED_ORACLE_AND_STAGE_A_FAILURE_FROZEN", packet["accepted_inputs"]["analytic_oracle"] == "QUALIFIED_AND_ACCEPTED" and packet["accepted_inputs"]["stage_a_uniform_sphere_validation"] == "FAILED", "accepted inputs preserved"),
        _gate("R04_EXACT_EIGHT_CASES", case_audit["case_count"] == 8 and case_audit["case_ids_exact"], "accepted oracle case order exact"),
        _gate("R05_THREE_EXACT_STAGE_A_CASES", case_audit["legacy_case_count"] == 3, "three historical configurations retained"),
        _gate("R06_STRICT_NONOVERLAP_AND_GAP_SEMANTICS", case_audit["strict_nonoverlap"] and case_audit["gap_reconstruction_max_error_m"] <= 2e-17, "D=R1+R2+g reproduced"),
        _gate("R07_ORDER_LADDER_EXACT", case_audit["orders_exact"], "orders 8,16,24,32,40,48"),
        _gate("R08_COMPONENT_CHANNELS_EXACT", case_audit["components_exact"], "Newtonian and Yukawa separate"),
        _gate("R09_NINETY_SIX_ATOMIC_CELLS", case_audit["atomic_cell_count_reproduced"] == domain["required_atomic_scientific_cells"] == 96, "8*6*2 exact"),
        _gate("R10_HISTORICAL_STAGE_A_FUNCTION_PRESENT", historical_identity["uses_one_order_for_all_dimensions"], "exact Stage A Yukawa function located"),
        _gate("R11_PARAMETERIZED_MIRROR_PRESENT", mirror_identity["parameterizes_unequal_radii"], "generalized fixed-tensor path located"),
        _gate("R12_HISTORICAL_AND_MIRROR_ACCUMULATION_IDENTICAL", path_audit["accumulation_algorithm_identical_as_frozen"], path_audit["finding"]),
        _gate("R13_HISTORICAL_AND_MIRROR_DECISION_SCOPE_SEPARATED", path_audit["historical_decision_bearing_cases_separated_from_mirror_only_cases"], "unequal-radius mirror results are not separately bounded from historical adjudication"),
        _gate("R14_LEGACY_EQUIVALENCE_RULE_EXECUTABLE", path_audit["legacy_equivalence_tolerance_present"] and path_audit["legacy_equivalence_failure_behavior_present"], "control is named but tolerance and consequence are absent"),
        _gate("R15_ORACLE_PATH_HASH_PINNED_AND_READ_ONLY", packet["oracle_path_identity"]["oracle_values_read_only"], "accepted reference immutability explicit"),
        _gate("R16_PRODUCTION_AND_ORACLE_CHANGES_FORBIDDEN", packet["production_path_identity"]["production_repair_or_algorithm_change"] == "FORBIDDEN" and packet["oracle_path_identity"]["production_import_into_oracle"] == "FORBIDDEN", "no tuning or repair during comparison"),
        _gate("R17_ABSOLUTE_AND_RELATIVE_METRICS_FROZEN", "abs(" in metrics["absolute_error_J"] and "max(" in metrics["relative_error"], "component metrics explicit"),
        _gate("R18_ACCURACY_ENVELOPE_FROZEN", classification_audit["accuracy_rule_complete"], metrics["accuracy_rule"]),
        _gate("R19_ORDER48_NEVER_REFERENCE", classification_audit["order48_not_reference"], "oracle remains analytic"),
        _gate("R20_EXACT_NINE_CLASSIFICATION_LABELS", classification_audit["predicate_count"] == 9, "registered label set exact"),
        _gate("R21_VALIDATED_LABEL_REQUIRES_THREE_FINAL_ORDERS", classification_audit["validated_predicate_multi_order"], "single favorable order insufficient"),
        _gate("R22_FIXED_ORDER_LABEL_REQUIRES_MULTI_ORDER_TREND", classification_audit["fixed_order_predicate_multi_order"], "orders 24 through 48 used"),
        _gate("R23_REGIME_DEPENDENT_LABEL_HAS_PASS_FAIL_CONTRAST", "same component" in predicates["REGIME_DEPENDENT_PRODUCTION_FAILURE"], "component-specific regime contrast"),
        _gate("R24_SLOW_CONVERGENCE_FIT_AND_COST_RULE_EXECUTABLE", classification_audit["slow_fit_method_frozen"] and classification_audit["economic_projection_rule_frozen"], "fit family, data subset, extrapolation, and cost threshold are unspecified"),
        _gate("R25_SYSTEMATIC_BIAS_AND_FINGERPRINT_RULES_EXECUTABLE", classification_audit["mutation_fingerprint_distance_and_tolerance_frozen"] and classification_audit["systematic_bias_component_grouping_frozen"], "component grouping and mutation-fingerprint matching are unspecified"),
        _gate("R26_NEAR_THRESHOLD_RESULTS_UNRESOLVED", classification_audit["near_threshold_unresolved"], "no favorable rounding"),
        _gate("R27_MULTILABEL_REPORTING_EXPLICIT", classification_audit["multilabel_permitted"], "compatible root causes may coexist"),
        _gate("R28_POST_RESULT_CHANGES_FORBIDDEN", classification_audit["post_result_changes_forbidden"], "visual classification prohibited"),
        _gate("R29_EXACT_TEN_CONTROLS", control_audit["control_count"] == 10 and control_audit["ids_unique"], "frozen mutation identities exact"),
        _gate("R30_LIVE_COMPARISON_PIPELINE_ASSERTED", control_audit["live_pipeline_asserted"], "substitute path disallowed by packet intent"),
        _gate("R31_CONTROL_CASE_ORDER_AND_TOLERANCE_ROUTING", control_audit["case_ids_frozen_per_control"] and control_audit["orders_frozen_per_control"] and control_audit["acceptance_tolerances_frozen_per_control"], control_audit["finding"]),
        _gate("R32_ORDER_AND_ORACLE_CUSTODY_CONTROLS_PRESENT", control_audit["metadata_and_oracle_firewalls_present"], "metadata overclaim and oracle overwrite named"),
        _gate("R33_RESOURCE_TOTAL_AND_MEMORY_EXACT", resource_audit["total_seconds"] == 1200 and resource_audit["memory_mib"] == 4096, "bounded envelope exact"),
        _gate("R34_PER_ORDER_CAPS_EXACT", resource_audit["per_order_cap_keys"] == [8,16,24,32,40,48], "all order cells bounded"),
        _gate("R35_PROCESS_GROUP_ATOMIC_AND_ZERO_SURVIVOR_CUSTODY", resource_audit["process_group_required"] and resource_audit["atomic_records_required"] and resource_audit["zero_survivors_required"], "launcher custody complete"),
        _gate("R36_INCOMPLETE_RECORDS_SUPPRESS_SCIENTIFIC_CLASSIFICATION", classification_audit["timeout_suppresses_partial_scientific_labels"] and resource_audit["full_record_set_required_for_scientific_classification"], "timeout is named but exclusive precedence over partial labels is not frozen"),
        _gate("R37_STAGE_CAPS_COHERENT_WITH_TOTAL", resource_audit["stage_count"] == 6 and resource_audit["stage_cap_sum_seconds"] == 1120 <= resource_audit["total_seconds"], "six stages fit total cap"),
        _gate("R38_ALL_DOWNSTREAM_FIREWALLS_CLOSED", not any(packet["scope"][key] for key in ("production_kernel_repaired","production_kernel_replaced","torque_computed","angular_dft_computed","final_real_150_vector_computed","jacobian_or_svd_computed","identifiability_computed","stage_a_rerun_performed","stage_b_performed")), "no downstream work performed"),
        _gate("R39_NO_COMPARISON_EXECUTION_AUTHORIZED_BY_BLOCKED_REVIEW", True, "review failure consumes no execution authority"),
        _gate("R40_FRESH_RESPONSE_SELECTOR_REQUIRED", True, "review cannot repair its own packet"),
    ]
    failures = [row["gate_id"] for row in gates if row["status"] == "FAIL"]
    if len(gates) != 40 or len(failures) != 7:
        raise ValueError("unexpected independent review gate accounting")

    scope = {
        "independent_packet_review_performed": True,
        "packet_custody_verified": True,
        "blocked_contract_result_issued": True,
        "fresh_scientific_response_selector_authorized": True,
        "comparison_contract_ready": False,
        "comparison_execution_authorized": False,
        "comparison_execution_performed": False,
        "packet_repair_authorized": False,
        "production_kernel_repair_authorized": False,
        "production_kernel_replacement_authorized": False,
        "torque_or_dft_authorized": False,
        "final_real_150_vector_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_a_rerun_authorized": False,
        "stage_b_eligible": False,
        "stage_b_authorized": False,
    }
    return {
        "schema_id": (
            "toe.scalar_only_yukawa.production_cubature_vs_analytic_oracle."
            "comparison_packet_review.v0"
        ),
        "review_id": (
            "SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_"
            "COMPARISON_PACKET_REVIEW_20260719_v0"
        ),
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "principal_review_outcome": PRINCIPAL_OUTCOME,
        "secondary_review_outcomes": [
            "BLOCKED_METRIC_OR_CLASSIFICATION_CONTRACT",
            "BLOCKED_MUTATION_ROUTING",
        ],
        "status": "INDEPENDENT_PACKET_REVIEW_COMPLETE_BLOCKED",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_verdict": packet["verdict"],
            "frozen_packet_artifacts": frozen,
            "human_review": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_production_cubature_vs_"
                "analytic_oracle_comparison_packet_review_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
            "authorized_comparison_execution_count": 0,
            "performed_comparison_execution_count": 0,
        },
        "independent_case_and_accounting_audit": case_audit,
        "independent_production_path_identity_audit": path_audit,
        "independent_classification_audit": classification_audit,
        "independent_control_routing_audit": control_audit,
        "independent_resource_and_custody_audit": resource_audit,
        "diagnostics": list(DIAGNOSTICS),
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": len(gates) - len(failures),
            "failure_count": len(failures),
            "failed_gate_ids": failures,
            "rows": gates,
        },
        "accepted_surfaces": {
            "packet_custody": "ACCEPTED",
            "oracle_custody": "ACCEPTED",
            "case_grid": "ACCEPTED_8_CASES",
            "order_ladder": "ACCEPTED_6_ORDERS",
            "component_separation": "ACCEPTED",
            "atomic_record_count": "ACCEPTED_96",
            "resource_envelope": "ACCEPTED",
            "production_comparison_contract": "NOT_READY",
        },
        "bounded_repair_burden_for_fresh_selector": {
            "historical_path": (
                "Freeze ORDINARY sequential accumulation for the exact Stage A equivalence "
                "lane, define its cases/orders/tolerance, and separate mirror-only unequal-"
                "radius diagnostics from claims about historical production."
            ),
            "classification": (
                "Freeze the slow-convergence fit, economic extrapolation, per-component "
                "systematic-bias grouping, and mutation-fingerprint distance/tolerance."
            ),
            "controls": (
                "Assign every control exact cases, orders, injection point, acceptance rule, "
                "and failure consequence through the future production comparison runner."
            ),
            "incomplete_records": (
                "Make PRODUCTION_COMPARISON_TIMEOUT exclusive and suppress all scientific "
                "classifications unless all 96 required cells and mandatory controls complete."
            ),
            "automatic_repair": "NOT_AUTHORIZED",
        },
        "scope": scope,
        "claim_ceiling": (
            "This review establishes only that the V0 comparison contract is not yet "
            "reproducibly executable. It does not judge production cubature, rerun the "
            "oracle, repair or replace a kernel, compute torque or harmonics, decide "
            "identifiability, rerun Stage A, or authorize Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_review(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Independently review the production-vs-oracle comparison packet without executing it."
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
        print("production-vs-oracle packet review artifact missing or stale")
        return 1
    report = json.loads(path.read_text(encoding="utf-8"))
    print(
        "production-vs-oracle packet review OK "
        f"verdict={report['verdict']} "
        f"pass={report['review_gates']['pass_count']} "
        f"fail={report['review_gates']['failure_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
