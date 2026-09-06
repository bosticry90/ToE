from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_REVIEW_20260719_v1.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_REVIEW_20260719_v1.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_production_cubature_vs_analytic_"
    "oracle_comparison_packet_review_v1.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaProductionCubatureVsAnalyticOracleComparisonPacketReviewV1.lean"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_20260719_v1.json"
)

TARGET = (
    "review_scalar_only_yukawa_production_cubature_vs_analytic_oracle_"
    "comparison_packet_v1_result"
)
VERDICT = "BLOCKED_PRODUCTION_COMPARISON_CONTRACT_INCOMPLETE"
PRINCIPAL_OUTCOME = "BLOCKED_MUTATION_ROUTING"
SECONDARY_OUTCOME = "BLOCKED_INCOMPLETE_RECORD_PRECEDENCE"
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_yukawa_production_cubature_vs_analytic_oracle_"
    "comparison_packet_v1_review_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "FRESH_SCIENTIFIC_RESPONSE_SELECTION_ONLY_NO_V2_REPAIR_OR_COMPARISON_EXECUTION"
)

PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_COMPARISON_PACKET_20260719_v1.md":
        "42ab8162052180b58362cc5049cd7fe523aba82ee0859785b3d4f06c638f4e0f",
    PACKET_RELATIVE_PATH:
        "e43867cc6d36ea5ed0ca45f01b6626e61a35a45b48acb04e732a8b089f0913d1",
    "formal/python/tools/scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v1.py":
        "0725d3d09b7e6c4f350c1b31a5ba87feec99ecbf951946d433ba9229cd23b6ec",
    "formal/python/tests/test_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v1.py":
        "3c6f1e837473a76aa9fe9831df6f1a7fb7b127cac0abd266d20c8da856a0dac6",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaProductionCubatureVsAnalyticOracleComparisonPacketV1.lean":
        "ec26f5f00621eed218c8825c31c4f67f20d3ce7ad91b730c2c0bfe3c8b85e3fc",
}

FAILED_GATE_IDS = (
    "R34_C03_C04_REQUIRED_CLASSIFIER_LABELS_REACHABLE",
    "R35_C02_FINGERPRINT_CONTROL_PREREQUISITES_ROUTED",
    "R36_C06_C10_DETECTION_INDEPENDENT_OF_UNKNOWN_BASELINE",
    "R42_DUPLICATE_RECORD_PRECEDENCE_UNIQUE",
    "R43_TIMEOUT_OUTCOME_NAMESPACE_UNAMBIGUOUS",
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


def _control_by_id(packet: dict[str, Any], control_id: str) -> dict[str, Any]:
    matches = [
        row for row in packet["mandatory_control_contract"]["rows"]
        if row["control_id"] == control_id
    ]
    if len(matches) != 1:
        raise ValueError(f"expected one control row for {control_id}")
    return matches[0]


def build_report() -> dict[str, Any]:
    for relative_path, expected_hash in PACKET_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected_hash:
            raise ValueError(f"V1 packet custody drift: {relative_path}")

    packet = _load_json(PACKET_RELATIVE_PATH)
    if packet.get("target") != (
        "prepare_scalar_only_yukawa_production_cubature_vs_analytic_oracle_"
        "comparison_packet_v1"
    ):
        raise ValueError("V1 packet target mismatch")
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("V1 packet did not authorize this review")
    if packet.get("scope", {}).get("comparison_execution_performed") is not False:
        raise ValueError("V1 packet unexpectedly performed comparison execution")

    frozen = packet["frozen_v0_surfaces"]
    source = packet["production_source_and_attribution_contract"]
    equivalence = packet["historical_path_equivalence_contract"]
    classification = packet["classification_contract_v1"]
    systematic = classification["systematic_bias"]
    fingerprint = classification["yukawa_mutation_fingerprint"]
    completion = packet["completion_and_precedence_contract"]

    c02 = _control_by_id(packet, "C02_MISSING_A_Y_ONE_THIRD")
    c03 = _control_by_id(packet, "C03_GAP_FOR_CENTER_DISTANCE")
    c04 = _control_by_id(packet, "C04_RADIUS_AS_DIAMETER")
    c06 = _control_by_id(packet, "C06_WEIGHT_NORMALIZATION_BIAS")
    c10 = _control_by_id(packet, "C10_CONSTANT_MULTIPLICATIVE_BIAS")

    required_systematic_cases = int(systematic["minimum_qualifying_cases_per_component"])
    required_systematic_orders = tuple(systematic["orders"])
    impossible_general_controls = []
    for control in (c03, c04):
        case_count = len(control["case_ids"])
        routed_orders = tuple(control["orders"])
        if case_count < required_systematic_cases or not set(required_systematic_orders).issubset(
            routed_orders
        ):
            impossible_general_controls.append({
                "control_id": control["control_id"],
                "case_count": case_count,
                "minimum_classifier_case_count": required_systematic_cases,
                "routed_orders": list(routed_orders),
                "required_classifier_orders": list(required_systematic_orders),
                "required_detection": control["required_detection"],
                "reachable": False,
            })

    c02_has_newtonian_route = "NEWTONIAN" in c02["components"]
    c02_has_all_fingerprint_orders = tuple(c02["orders"]) == tuple(
        fingerprint["order_within_case"]
    )
    c02_has_all_fingerprint_cases = tuple(c02["case_ids"]) == tuple(
        fingerprint["case_order"]
    )

    baseline_dependent_controls = []
    for control, multiplier in ((c06, 1.01), (c10, 1.02)):
        baseline_dependent_controls.append({
            "control_id": control["control_id"],
            "multiplier": multiplier,
            "identity": "R_MUTATED=MULTIPLIER*R_BASELINE",
            "relative_spread_identity": "RELATIVE_SPREAD(R_MUTATED)=RELATIVE_SPREAD(R_BASELINE)",
            "classifier_spread_max": systematic["maximum_relative_spread"],
            "unknown_baseline_spread_can_prevent_required_label": True,
            "detection_independent_of_scientific_baseline": False,
        })

    priority2 = next(
        row for row in completion["exclusive_precedence"] if row["priority"] == 2
    )
    duplicate_declared = completion["duplicate_cell_behavior"]
    duplicate_priority_outcome = priority2["exclusive_outcome"]
    duplicate_outcome_unique = duplicate_declared == duplicate_priority_outcome
    timeout_token = "PRODUCTION_COMPARISON_TIMEOUT"
    timeout_in_scientific_labels = timeout_token in classification["scientific_labels_exact"]
    timeout_requires_empty_scientific_labels = (
        completion["scientific_labels_on_priority_1_2_or_3"]
        == "FORBIDDEN_EMPTY_LIST_REQUIRED"
    )

    gate_specs = (
        ("R01_EXACT_V1_PACKET_CUSTODY", True, "five V1 artifacts hash-verified"),
        ("R02_SELECTOR_AUTHORITY_PRESERVED", True, "selector artifacts frozen by packet"),
        ("R03_V0_PACKET_CUSTODY_PRESERVED", True, "V0 artifacts frozen by packet"),
        ("R04_PREPARED_STATUS_AND_NO_EXECUTION", packet["status"] == "PREPARED_PENDING_INDEPENDENT_REVIEW_NO_EXECUTION", "no comparison values produced"),
        ("R05_THIRTY_THREE_ACCEPTED_GATES_FROZEN", frozen["accepted_review_gate_count"] == 33, "33 accepted review gates retained"),
        ("R06_EXACT_SEVEN_GATE_REPAIR_SCOPE", packet["v1_repair_scope"]["repaired_review_gate_count"] == 7, "seven failed gates named"),
        ("R07_EIGHT_CASES_UNCHANGED", frozen["comparison_domain"]["case_count"] == 8, "case count unchanged"),
        ("R08_SIX_ORDERS_UNCHANGED", frozen["comparison_domain"]["orders"] == [8, 16, 24, 32, 40, 48], "order ladder unchanged"),
        ("R09_TWO_COMPONENTS_UNCHANGED", frozen["comparison_domain"]["components"] == ["NEWTONIAN", "YUKAWA"], "component channels unchanged"),
        ("R10_NINETY_SIX_CELLS_UNCHANGED", len(source["source_rows"]) == 96, "96 source rows exact"),
        ("R11_SOURCE_PARTITION_EXACT", source["source_counts"] == {"HISTORICAL_STAGE_A_YUKAWA": 18, "MIRROR_NEWTONIAN_COMPANION": 48, "PARAMETERIZED_MIRROR_YUKAWA_EXTENSION": 30}, "18+48+30 exact"),
        ("R12_HISTORICAL_YUKAWA_CALLED_DIRECTLY", source["historical_function_called_directly"] is True, "historical path not substituted"),
        ("R13_NEWTONIAN_COMPANION_SCOPE_EXPLICIT", source["newtonian_historical_claim"].startswith("FORBIDDEN"), "Newtonian historical overclaim barred"),
        ("R14_MIRROR_EXTENSION_SCOPE_EXPLICIT", source["unequal_radius_historical_claim"] == "FORBIDDEN", "unequal-radius overclaim barred"),
        ("R15_SOURCE_EXECUTION_ORDER_FROZEN", "ASCENDING_ORDER" in source["execution_order"], "case/order/component sequence explicit"),
        ("R16_C00_CASES_EXACT", len(equivalence["case_ids"]) == 3, "three legacy cases exact"),
        ("R17_C00_ORDERS_EXACT", equivalence["orders"] == [8, 16, 24], "identity orders exact"),
        ("R18_C00_SEQUENCE_EXACT", "HISTORICAL_FIRST_THEN_MIRROR_ORDINARY" in equivalence["execution_order"], "call sequence exact"),
        ("R19_C00_TOLERANCE_NUMERIC", equivalence["absolute_tolerance_J"] == 1e-36 and equivalence["relative_tolerance"] == 5e-14, "absolute and relative tolerances exact"),
        ("R20_C00_FAILURE_STOPS_SCIENCE", equivalence["failure_consequence"].startswith("BLOCKED_PRODUCTION_PATH_IDENTITY"), "failure consequence exact"),
        ("R21_SLOW_CANDIDATE_RULE_EXECUTABLE", "STRICTLY_DECREASE" in classification["slow_convergence_fit"]["candidate_prerequisite"], "positive finite monotone prerequisite"),
        ("R22_SLOW_ERROR_FITS_EXACT", classification["slow_convergence_fit"]["full_fit_orders"] == [16, 24, 32, 40, 48] and classification["slow_convergence_fit"]["tail_fit_orders"] == [24, 32, 40, 48], "full and tail OLS fits exact"),
        ("R23_SLOW_STABILITY_THRESHOLDS_EXACT", classification["slow_convergence_fit"]["minimum_r_squared_each_fit"] == 0.98 and classification["slow_convergence_fit"]["maximum_relative_exponent_difference"] == 0.20, "fit stability numeric"),
        ("R24_RUNTIME_FIT_EXECUTABLE", classification["slow_convergence_fit"]["runtime_fit_minimum_r_squared"] == 0.95, "runtime fit family and threshold exact"),
        ("R25_ECONOMIC_RULE_EXECUTABLE", "GT_60" in classification["slow_convergence_fit"]["economic_inferiority_rule"] and "GT_1200" in classification["slow_convergence_fit"]["economic_inferiority_rule"], "per-case and total thresholds exact"),
        ("R26_SYSTEMATIC_BIAS_COMPONENT_SEPARATED", systematic["grouping"].startswith("SEPARATELY_PER_COMPONENT"), "components never pooled"),
        ("R27_SYSTEMATIC_BIAS_VECTOR_AND_SPREAD_EXACT", systematic["minimum_qualifying_cases_per_component"] == 4 and systematic["maximum_relative_spread"] == 0.005, "case count and spread exact"),
        ("R28_FINGERPRINT_VECTOR_EXACT", fingerprint["vector_length"] == 24 and c02_has_all_fingerprint_cases and c02_has_all_fingerprint_orders, "case/order vector exact"),
        ("R29_FINGERPRINT_METRIC_AND_TOLERANCE_EXACT", fingerprint["maximum_relative_l2_distance"] == 0.05 and fingerprint["maximum_entrywise_absolute_difference"] == 0.10, "distance thresholds exact"),
        ("R30_FINGERPRINT_PREREQUISITES_STATED", "NEWTONIAN_PASSES_ALL_8_CASES" in fingerprint["newtonian_prerequisite"], "Newtonian prerequisite stated"),
        ("R31_TEN_V0_CONTROL_IDS_PRESERVED", packet["mandatory_control_contract"]["frozen_mutation_control_count"] == 10, "ten mutation identities preserved"),
        ("R32_ELEVEN_MANDATORY_CONTROLS_EXACT", packet["mandatory_control_contract"]["total_mandatory_control_count"] == 11, "one preflight plus ten controls"),
        ("R33_CONTROL_ROUTE_FIELDS_COMPLETE", all(all(row.get(key) not in (None, [], "") for key in ("case_ids", "orders", "components", "execution_order", "injection_point", "acceptance_rule", "failure_consequence")) for row in packet["mandatory_control_contract"]["rows"]), "descriptive route fields present"),
        ("R34_C03_C04_REQUIRED_CLASSIFIER_LABELS_REACHABLE", len(impossible_general_controls) == 0, "C03/C04 route fewer than four cases and omit required final-order triple"),
        ("R35_C02_FINGERPRINT_CONTROL_PREREQUISITES_ROUTED", c02_has_newtonian_route, "C02 routes Yukawa only but its required label needs eight-case Newtonian pass"),
        ("R36_C06_C10_DETECTION_INDEPENDENT_OF_UNKNOWN_BASELINE", all(row["detection_independent_of_scientific_baseline"] for row in baseline_dependent_controls), "positive scaling preserves unknown baseline ratio spread"),
        ("R37_IDENTITY_AND_CUSTODY_FIREWALL_CONTROLS_PRESENT", all(_control_by_id(packet, cid)["required_detection"].endswith("FIREWALL") for cid in ("C07_COMPONENT_CHANNEL_SWAP", "C08_ORDER_METADATA_OVERCLAIM", "C09_ORACLE_OVERWRITE")), "three custody firewalls exact"),
        ("R38_RESOURCE_ENVELOPE_PRESERVED", frozen["resource_and_custody_contract"]["maximum_total_wall_clock_seconds"] == 1200 and frozen["resource_and_custody_contract"]["maximum_memory_mib"] == 4096, "resource limits unchanged"),
        ("R39_ALL_SOURCE_ROWS_HAVE_SCOPE", all(row.get("evidence_scope") for row in source["source_rows"]), "every cell scope serialized"),
        ("R40_FULL_96_CELL_PRECONDITION", completion["required_unique_scientific_cells"] == 96, "full cell count required"),
        ("R41_ALL_CONTROL_PRECONDITION", completion["required_mandatory_controls"] == 11, "all controls required"),
        ("R42_DUPLICATE_RECORD_PRECEDENCE_UNIQUE", duplicate_outcome_unique, f"duplicate declares {duplicate_declared} but priority-2 declares {duplicate_priority_outcome}"),
        ("R43_TIMEOUT_OUTCOME_NAMESPACE_UNAMBIGUOUS", not (timeout_in_scientific_labels and timeout_requires_empty_scientific_labels), "timeout is both a scientific label and an exclusive outcome requiring empty scientific labels"),
        ("R44_PARTIAL_CLASSIFICATION_SUPPRESSED", completion["completed_subset_classification"] == "FORBIDDEN", "partial subsets cannot classify"),
        ("R45_EXACT_NINE_LABELS_PRESERVED", len(classification["scientific_labels_exact"]) == 9, "nine label tokens unchanged"),
        ("R46_DOWNSTREAM_FIREWALLS_CLOSED", packet["scope"]["torque_or_dft_authorized"] is False and packet["scope"]["stage_b_authorized"] is False, "no downstream authority"),
        ("R47_AUTOMATIC_V2_PROHIBITED", packet["final_attempt_boundary"]["automatic_v2_authorized"] is False, "final automatic repair boundary honored"),
        ("R48_FRESH_SELECTOR_REQUIRED", True, "blocked final attempt rotates only to fresh selector"),
    )

    gate_rows = [
        {"gate_id": gate_id, "status": "PASS" if passed else "FAIL", "finding": finding}
        for gate_id, passed, finding in gate_specs
    ]
    failed = [row["gate_id"] for row in gate_rows if row["status"] == "FAIL"]
    if tuple(failed) != FAILED_GATE_IDS:
        raise ValueError(f"unexpected V1 review gate failures: {failed}")

    scope = {
        "independent_v1_packet_review_performed": True,
        "v1_packet_custody_verified": True,
        "thirty_three_frozen_gates_preserved": True,
        "blocked_final_contract_result_issued": True,
        "fresh_scientific_response_selector_authorized": True,
        "comparison_contract_ready": False,
        "comparison_execution_authorized": False,
        "comparison_execution_performed": False,
        "automatic_v2_authorized": False,
        "packet_repair_authorized": False,
        "production_cubature_adjudicated": False,
        "kernel_repair_or_replacement_authorized": False,
        "torque_or_dft_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_a_rerun_authorized": False,
        "stage_b_authorized": False,
    }

    return {
        "schema_id": "toe.scalar_only_yukawa.production_cubature_vs_analytic_oracle.comparison_packet_review.v1",
        "review_id": "SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_COMPARISON_PACKET_REVIEW_20260719_v1",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "status": "INDEPENDENT_V1_PACKET_REVIEW_COMPLETE_BLOCKED_FINAL_AUTOMATIC_REPAIR",
        "principal_review_outcome": PRINCIPAL_OUTCOME,
        "secondary_review_outcomes": [SECONDARY_OUTCOME],
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_verdict": packet["verdict"],
            "frozen_packet_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in PACKET_HASHES.items()
            ],
            "human_review": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_production_cubature_vs_"
                "analytic_oracle_comparison_packet_review_v1.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
            "authorized_comparison_execution_count": 0,
            "performed_comparison_execution_count": 0,
        },
        "accepted_surfaces": {
            "frozen_review_gates": "33_PRESERVED",
            "analytic_oracle": "QUALIFIED_AND_ACCEPTED",
            "case_order_component_and_96_cell_accounting": "ACCEPTED",
            "historical_mirror_source_partition": "ACCEPTED",
            "historical_identity_preflight": "ACCEPTED_AS_EXECUTABLE",
            "slow_fit_and_economic_rules": "ACCEPTED_AS_EXECUTABLE",
            "systematic_bias_and_fingerprint_metrics": "ACCEPTED_AS_NUMERIC",
            "resource_and_downstream_firewalls": "ACCEPTED",
            "overall_comparison_contract": "NOT_READY",
        },
        "independent_control_reachability_audit": {
            "systematic_classifier_minimum_case_count": required_systematic_cases,
            "systematic_classifier_required_orders": list(required_systematic_orders),
            "unreachable_general_defect_controls": impossible_general_controls,
            "c02_routes_newtonian_prerequisite": c02_has_newtonian_route,
            "c02_routes_all_fingerprint_cases": c02_has_all_fingerprint_cases,
            "c02_routes_all_fingerprint_orders": c02_has_all_fingerprint_orders,
            "baseline_dependent_systematic_controls": baseline_dependent_controls,
            "finding": (
                "C03 and C04 cannot reach their required four-case, three-final-order "
                "classifier predicate. C02 lacks the Newtonian fixture required by its "
                "own label. C06 and C10 preserve unknown baseline spread, so detection "
                "depends on the scientific result."
            ),
        },
        "independent_completion_precedence_audit": {
            "duplicate_declared_behavior": duplicate_declared,
            "duplicate_priority2_behavior": duplicate_priority_outcome,
            "duplicate_outcome_unique": duplicate_outcome_unique,
            "timeout_token": timeout_token,
            "timeout_in_scientific_label_set": timeout_in_scientific_labels,
            "priority2_requires_empty_scientific_label_list": timeout_requires_empty_scientific_labels,
            "timeout_namespace_unambiguous": False,
            "partial_subset_classification_forbidden": completion["completed_subset_classification"] == "FORBIDDEN",
        },
        "review_gates": {
            "gate_count": len(gate_rows),
            "pass_count": sum(row["status"] == "PASS" for row in gate_rows),
            "failure_count": len(failed),
            "failed_gate_ids": failed,
            "rows": gate_rows,
        },
        "final_attempt_disposition": {
            "automatic_v2": "PROHIBITED",
            "silent_packet_repair": "PROHIBITED",
            "comparison_execution": "NOT_AUTHORIZED",
            "fresh_selector_required": True,
            "bounded_future_choices": [
                "HISTORICAL_PATH_IDENTITY_ISOLATION_ONLY",
                "MIRROR_ONLY_COMPARISON_WITH_HISTORICAL_CLAIMS_WITHDRAWN",
                "DIRECT_ANALYTIC_KERNEL_REPLACEMENT",
                "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
            ],
        },
        "scope": scope,
        "claim_ceiling": (
            "This review establishes only that V1 preserves the accepted surfaces but "
            "does not close mutation reachability or completion precedence reproducibly. "
            "It performs no comparison, adjudicates no cubature, repairs no packet or "
            "kernel, computes no torque, DFT, vector, Jacobian, SVD, or identifiability "
            "result, reruns no Stage A execution, and authorizes no Stage B activity."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Independently review the final V1 comparison packet.")
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
            print("comparison packet V1 review already current")
        return 0
    if current != expected:
        print("comparison packet V1 review drift")
        return 1
    report = build_report()
    print(
        "comparison packet V1 review OK "
        f"verdict={report['verdict']} pass={report['review_gates']['pass_count']} "
        f"fail={report['review_gates']['failure_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
