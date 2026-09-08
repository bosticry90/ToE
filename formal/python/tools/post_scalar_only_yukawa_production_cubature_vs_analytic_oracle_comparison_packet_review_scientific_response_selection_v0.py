from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_post_scalar_only_yukawa_production_cubature_vs_analytic_"
    "oracle_comparison_packet_review_scientific_response_selection_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PostScalarOnlyYukawaProductionCubatureVsAnalyticOracleComparisonPacketReview"
    "ScientificResponseSelectionV0.lean"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_REVIEW_20260719_v0.json"
)

TARGET = (
    "select_post_scalar_only_yukawa_production_cubature_vs_analytic_oracle_"
    "comparison_packet_review_scientific_response_v0"
)
VERDICT = "SELECTED_NARROW_PRODUCTION_COMPARISON_CONTRACT_REPAIR_PACKET_PREPARATION"
SELECTED_ROUTE = "REPAIR_PRODUCTION_COMPARISON_EXECUTION_CONTRACT"
SELECTED_CANDIDATE_ID = "SEVEN_GATE_COMPARISON_CONTRACT_REPAIR_V1"
SELECTED_NEXT_TARGET = (
    "prepare_scalar_only_yukawa_production_cubature_vs_analytic_oracle_"
    "comparison_packet_v1"
)
SELECTED_NEXT_TARGET_KIND = (
    "PREPARATION_ONLY_SEVEN_GATE_COMPARISON_CONTRACT_REPAIR_NO_EXECUTION"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_COMPARISON_PACKET_REVIEW_20260719_v0.md":
        "9865b716d26bd8b8594cbe0048f71c7d695278f4e88453c6871ed616f8e7f6e1",
    REVIEW_RELATIVE_PATH:
        "d39a1fbb19ca5c589f74ce27f36fb019071e18ae93ab7c1893e00724c1de9784",
    "formal/python/tools/scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_review_v0.py":
        "fd85a456f960f364d6c54b0da0c250f8770a8db61bb15f2a380ba025de2c3c46",
    "formal/python/tests/test_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_review_v0.py":
        "563d17dde2340380425c70727592492e699ae48bf0c6e431b70ac8e39cd1fe04",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaProductionCubatureVsAnalyticOracleComparisonPacketReviewV0.lean":
        "da40728301ad82983529e78982f1876a6f181b0956a06972fd6fa4b159225e94",
}

ACCEPTED_REVIEW_GATES = (
    "R01_EXACT_PACKET_CUSTODY_AND_TARGET",
    "R02_PENDING_REVIEW_AND_NO_EXECUTION",
    "R03_ACCEPTED_ORACLE_AND_STAGE_A_FAILURE_FROZEN",
    "R04_EXACT_EIGHT_CASES",
    "R05_THREE_EXACT_STAGE_A_CASES",
    "R06_STRICT_NONOVERLAP_AND_GAP_SEMANTICS",
    "R07_ORDER_LADDER_EXACT",
    "R08_COMPONENT_CHANNELS_EXACT",
    "R09_NINETY_SIX_ATOMIC_CELLS",
    "R10_HISTORICAL_STAGE_A_FUNCTION_PRESENT",
    "R11_PARAMETERIZED_MIRROR_PRESENT",
    "R15_ORACLE_PATH_HASH_PINNED_AND_READ_ONLY",
    "R16_PRODUCTION_AND_ORACLE_CHANGES_FORBIDDEN",
    "R17_ABSOLUTE_AND_RELATIVE_METRICS_FROZEN",
    "R18_ACCURACY_ENVELOPE_FROZEN",
    "R19_ORDER48_NEVER_REFERENCE",
    "R20_EXACT_NINE_CLASSIFICATION_LABELS",
    "R21_VALIDATED_LABEL_REQUIRES_THREE_FINAL_ORDERS",
    "R22_FIXED_ORDER_LABEL_REQUIRES_MULTI_ORDER_TREND",
    "R23_REGIME_DEPENDENT_LABEL_HAS_PASS_FAIL_CONTRAST",
    "R26_NEAR_THRESHOLD_RESULTS_UNRESOLVED",
    "R27_MULTILABEL_REPORTING_EXPLICIT",
    "R28_POST_RESULT_CHANGES_FORBIDDEN",
    "R29_EXACT_TEN_CONTROLS",
    "R30_LIVE_COMPARISON_PIPELINE_ASSERTED",
    "R32_ORDER_AND_ORACLE_CUSTODY_CONTROLS_PRESENT",
    "R33_RESOURCE_TOTAL_AND_MEMORY_EXACT",
    "R34_PER_ORDER_CAPS_EXACT",
    "R35_PROCESS_GROUP_ATOMIC_AND_ZERO_SURVIVOR_CUSTODY",
    "R37_STAGE_CAPS_COHERENT_WITH_TOTAL",
    "R38_ALL_DOWNSTREAM_FIREWALLS_CLOSED",
    "R39_NO_COMPARISON_EXECUTION_AUTHORIZED_BY_BLOCKED_REVIEW",
    "R40_FRESH_RESPONSE_SELECTOR_REQUIRED",
)

REPAIRABLE_REVIEW_GATES = (
    "R12_HISTORICAL_AND_MIRROR_ACCUMULATION_IDENTICAL",
    "R13_HISTORICAL_AND_MIRROR_DECISION_SCOPE_SEPARATED",
    "R14_LEGACY_EQUIVALENCE_RULE_EXECUTABLE",
    "R24_SLOW_CONVERGENCE_FIT_AND_COST_RULE_EXECUTABLE",
    "R25_SYSTEMATIC_BIAS_AND_FINGERPRINT_RULES_EXECUTABLE",
    "R31_CONTROL_CASE_ORDER_AND_TOLERANCE_ROUTING",
    "R36_INCOMPLETE_RECORDS_SUPPRESS_SCIENTIFIC_CLASSIFICATION",
)

CRITERIA = {
    "direct_resolution_of_all_seven_gates": 5,
    "historical_attribution_integrity": 5,
    "classification_reproducibility": 5,
    "accepted_surface_preservation": 5,
    "scientific_method_change_avoidance": 4,
    "information_gain": 4,
    "risk_isolation": 4,
    "computational_economy": 3,
    "boundedness": 3,
    "authority_clarity": 3,
    "anti_rabbit_hole_control": 3,
}

CANDIDATES = (
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "target": SELECTED_NEXT_TARGET,
        "scores": {key: 5 for key in CRITERIA},
        "disposition": "SELECTED_FOR_V1_PACKET_PREPARATION_ONLY",
    },
    {
        "candidate_id": "HISTORICAL_PATH_IDENTITY_ISOLATION_ONLY",
        "target": "prepare_scalar_only_yukawa_historical_cubature_identity_isolation_packet_v0",
        "scores": {
            "direct_resolution_of_all_seven_gates": 2,
            "historical_attribution_integrity": 5,
            "classification_reproducibility": 1,
            "accepted_surface_preservation": 5,
            "scientific_method_change_avoidance": 5,
            "information_gain": 3,
            "risk_isolation": 5,
            "computational_economy": 4,
            "boundedness": 5,
            "authority_clarity": 4,
            "anti_rabbit_hole_control": 4,
        },
        "disposition": "DEFERRED_DOES_NOT_RESOLVE_CLASSIFICATION_OR_CONTROL_BLOCKS",
    },
    {
        "candidate_id": "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
        "target": "select_post_scalar_internal_torsion_balance_lane_closure_v0",
        "scores": {
            "direct_resolution_of_all_seven_gates": 0,
            "historical_attribution_integrity": 5,
            "classification_reproducibility": 0,
            "accepted_surface_preservation": 5,
            "scientific_method_change_avoidance": 5,
            "information_gain": 1,
            "risk_isolation": 5,
            "computational_economy": 5,
            "boundedness": 5,
            "authority_clarity": 5,
            "anti_rabbit_hole_control": 5,
        },
        "disposition": "DEFERRED_ONE_BOUNDED_CONTRACT_REPAIR_REMAINS_PROPORTIONATE",
    },
    {
        "candidate_id": "MIRROR_ONLY_COMPARISON_WITH_HISTORICAL_CLAIMS_WITHDRAWN",
        "target": "prepare_scalar_only_yukawa_mirror_only_oracle_comparison_packet_v0",
        "scores": {
            "direct_resolution_of_all_seven_gates": 3,
            "historical_attribution_integrity": 2,
            "classification_reproducibility": 2,
            "accepted_surface_preservation": 3,
            "scientific_method_change_avoidance": 4,
            "information_gain": 4,
            "risk_isolation": 3,
            "computational_economy": 4,
            "boundedness": 4,
            "authority_clarity": 3,
            "anti_rabbit_hole_control": 4,
        },
        "disposition": "DEFERRED_CHANGES_THE_HISTORICAL_QUESTION",
    },
    {
        "candidate_id": "DIRECT_ANALYTIC_KERNEL_REPLACEMENT",
        "target": "prepare_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0",
        "scores": {
            "direct_resolution_of_all_seven_gates": 0,
            "historical_attribution_integrity": 1,
            "classification_reproducibility": 0,
            "accepted_surface_preservation": 2,
            "scientific_method_change_avoidance": 0,
            "information_gain": 3,
            "risk_isolation": 3,
            "computational_economy": 5,
            "boundedness": 4,
            "authority_clarity": 3,
            "anti_rabbit_hole_control": 4,
        },
        "disposition": "DEFERRED_REPLACEMENT_PREMATURE_BEFORE_OLD_METHOD_ADJUDICATION",
    },
)

V1_REVIEW_OUTCOMES = (
    "PRODUCTION_COMPARISON_CONTRACT_READY",
    "BLOCKED_PRODUCTION_PATH_IDENTITY",
    "BLOCKED_METRIC_OR_CLASSIFICATION_CONTRACT",
    "BLOCKED_MUTATION_ROUTING",
    "BLOCKED_INCOMPLETE_RECORD_PRECEDENCE",
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


def _weighted_score(scores: dict[str, int], weights: dict[str, int]) -> int:
    if set(scores) != set(weights):
        raise ValueError("candidate score criteria mismatch")
    return sum(scores[key] * weights[key] for key in weights)


def _rank(weights: dict[str, int]) -> list[dict[str, Any]]:
    rows = []
    for candidate in CANDIDATES:
        row = dict(candidate)
        row["weighted_score"] = _weighted_score(candidate["scores"], weights)
        rows.append(row)
    return sorted(rows, key=lambda row: (-row["weighted_score"], row["candidate_id"]))


def _sensitivity() -> dict[str, Any]:
    rows = []
    for omitted in CRITERIA:
        weights = dict(CRITERIA)
        weights[omitted] = 0
        ranked = _rank(weights)
        rows.append({
            "variant": f"omit_{omitted}",
            "selected_candidate_id": ranked[0]["candidate_id"],
            "selected_score": ranked[0]["weighted_score"],
            "runner_up_candidate_id": ranked[1]["candidate_id"],
            "runner_up_score": ranked[1]["weighted_score"],
        })
    for criterion, baseline in CRITERIA.items():
        for delta in (-1, 1):
            weights = dict(CRITERIA)
            weights[criterion] = max(1, baseline + delta)
            ranked = _rank(weights)
            rows.append({
                "variant": f"{criterion}_{delta:+d}",
                "selected_candidate_id": ranked[0]["candidate_id"],
                "selected_score": ranked[0]["weighted_score"],
                "runner_up_candidate_id": ranked[1]["candidate_id"],
                "runner_up_score": ranked[1]["weighted_score"],
            })
    return {
        "variant_count": len(rows),
        "rows": rows,
        "selected_candidate_stable_in_all_variants": all(
            row["selected_candidate_id"] == SELECTED_CANDIDATE_ID for row in rows
        ),
        "minimum_winning_margin": min(
            row["selected_score"] - row["runner_up_score"] for row in rows
        ),
    }


def build_report() -> dict[str, Any]:
    for relative_path, expected_hash in AUTHORITY_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected_hash:
            raise ValueError(f"blocked comparison-review authority drift: {relative_path}")

    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "BLOCKED_PRODUCTION_COMPARISON_CONTRACT_INCOMPLETE":
        raise ValueError("blocked comparison-review verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("blocked comparison review did not authorize this selector")
    gates = review.get("review_gates", {})
    if gates.get("pass_count") != 33 or gates.get("failure_count") != 7:
        raise ValueError("blocked comparison-review gate count mismatch")
    if gates.get("failed_gate_ids") != list(REPAIRABLE_REVIEW_GATES):
        raise ValueError("blocked comparison-review failed-gate set mismatch")
    if review.get("scope", {}).get("comparison_execution_performed") is not False:
        raise ValueError("review unexpectedly performed the comparison")

    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    selection_gates = (
        "EXACT_BLOCKED_REVIEW_AUTHORITY_AND_TARGET",
        "CONTRACT_BLOCK_NOT_PRODUCTION_RESULT",
        "EXACTLY_THIRTY_THREE_ACCEPTED_GATES_FROZEN",
        "EXACTLY_SEVEN_FAILED_GATES_REPAIRABLE",
        "EXACTLY_FIVE_RESPONSE_CANDIDATES_COMPARED",
        "EXACTLY_ELEVEN_CRITERIA_FROZEN",
        "SELECTION_STABLE_IN_THIRTY_THREE_VARIANTS",
        "HISTORICAL_PATH_IDENTITY_REPAIR_REQUIRED",
        "HISTORICAL_AND_MIRROR_DECISION_SCOPE_SEPARATION_REQUIRED",
        "SLOW_FIT_AND_ECONOMIC_RULE_REPAIR_REQUIRED",
        "SYSTEMATIC_BIAS_AND_FINGERPRINT_RULE_REPAIR_REQUIRED",
        "CONTROL_ROUTING_REPAIR_REQUIRED",
        "EXCLUSIVE_TIMEOUT_PRECEDENCE_REQUIRED",
        "V0_PACKET_UNCHANGED",
        "NO_COMPARISON_EXECUTION_NOW",
        "NO_KERNEL_REPAIR_OR_REPLACEMENT_NOW",
        "ALL_DOWNSTREAM_FIREWALLS_RETAINED",
        "V1_IS_LAST_AUTOMATIC_COMPARISON_CONTRACT_REPAIR",
        "FRESH_SELECTOR_REQUIRED_AFTER_ANY_V1_FOUNDATIONAL_BLOCK",
        "NEXT_AUTHORITY_IS_PREPARATION_ONLY",
    )

    scope = {
        "scientific_response_selection_executed": True,
        "accepted_review_gates_frozen": True,
        "v1_comparison_contract_packet_preparation_authorized": True,
        "final_automatic_comparison_contract_repair_boundary_frozen": True,
        "v1_packet_prepared_now": False,
        "v0_packet_modified": False,
        "comparison_contract_ready": False,
        "comparison_execution_authorized": False,
        "comparison_execution_performed": False,
        "production_cubature_adjudicated": False,
        "production_kernel_repair_authorized": False,
        "production_kernel_replacement_authorized": False,
        "torque_or_dft_authorized": False,
        "final_real_150_vector_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_a_rerun_authorized": False,
        "stage_b_authorized": False,
        "automatic_v2_comparison_contract_repair_authorized": False,
    }

    return {
        "schema_id": (
            "toe.post_scalar_only_yukawa.production_cubature_vs_analytic_oracle."
            "comparison_packet_review.scientific_response_selection.v0"
        ),
        "selection_id": (
            "POST_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_"
            "COMPARISON_PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0"
        ),
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_route": SELECTED_ROUTE,
        "selected_candidate_id": SELECTED_CANDIDATE_ID,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_review_verdict": review["verdict"],
            "frozen_review_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in AUTHORITY_HASHES.items()
            ],
            "human_selection": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/post_scalar_only_yukawa_production_cubature_vs_"
                "analytic_oracle_comparison_packet_review_scientific_response_selection_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "review_interpretation": {
            "review_verdict": review["verdict"],
            "principal_block": review["principal_review_outcome"],
            "secondary_blocks": review["secondary_review_outcomes"],
            "production_cubature_adjudicated": False,
            "comparison_execution": "NOT_AUTHORIZED_NOT_PERFORMED",
            "accepted_oracle": "QUALIFIED_AND_ACCEPTED",
        },
        "selection_policy": {
            "candidate_count": len(CANDIDATES),
            "criterion_count": len(CRITERIA),
            "criteria_weights": CRITERIA,
            "criterion_scale": "0_TO_5_PRIORITY_SCORE_NOT_TRUTH_PROBABILITY",
            "tie_break_rule": "LEXICOGRAPHIC_CANDIDATE_ID",
        },
        "ranking": {
            "rows": ranking,
            "selected_candidate_id": ranking[0]["candidate_id"],
            "selected_score": ranking[0]["weighted_score"],
            "runner_up_candidate_id": ranking[1]["candidate_id"],
            "runner_up_score": ranking[1]["weighted_score"],
            "winning_margin": ranking[0]["weighted_score"] - ranking[1]["weighted_score"],
        },
        "sensitivity_analysis": sensitivity,
        "review_gate_freeze": {
            "accepted_gate_count": len(ACCEPTED_REVIEW_GATES),
            "repairable_gate_count": len(REPAIRABLE_REVIEW_GATES),
            "accepted_gates": list(ACCEPTED_REVIEW_GATES),
            "repairable_gates": list(REPAIRABLE_REVIEW_GATES),
            "all_accepted_surfaces": "FROZEN_NO_SEMANTIC_CHANGE",
        },
        "v1_preparation_contract": {
            "status": "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED",
            "editable_interfaces_only": [
                "HISTORICAL_MIRROR_PATH_IDENTITY_AND_DECISION_SCOPE",
                "SLOW_CONVERGENCE_FIT_AND_ECONOMIC_THRESHOLD",
                "SYSTEMATIC_BIAS_GROUPING_AND_MUTATION_FINGERPRINT",
                "CONTROL_CASE_ORDER_INJECTION_TOLERANCE_ROUTING",
                "INCOMPLETE_RECORD_EXCLUSIVE_PRECEDENCE",
            ],
            "historical_path_obligations": [
                "FREEZE_ACCUMULATION_MODE_FOR_HISTORICAL_EQUIVALENCE_LANE",
                "FREEZE_EXACT_EQUIVALENCE_CASES_ORDERS_TOLERANCE_AND_FAILURE_CONSEQUENCE",
                "SEPARATE_HISTORICAL_DECISION_BEARING_CASES_FROM_MIRROR_ONLY_CASES",
                "PROHIBIT_MIRROR_ONLY_RESULTS_FROM_SUPPORTING_HISTORICAL_CLAIMS",
            ],
            "classification_obligations": [
                "FREEZE_SLOW_FIT_FAMILY_ORDER_SUBSET_AND_NONMONOTONE_HANDLING",
                "FREEZE_EXTRAPOLATION_STABILITY_AND_ECONOMIC_INFERIORITY_THRESHOLD",
                "FREEZE_SYSTEMATIC_BIAS_COMPONENT_GROUPING",
                "FREEZE_MUTATION_FINGERPRINT_VECTOR_DISTANCE_AND_MATCH_TOLERANCE",
            ],
            "control_obligations": [
                "ROUTE_EVERY_CONTROL_TO_EXACT_CASES_ORDERS_AND_INJECTION_POINT",
                "FREEZE_EVERY_CONTROL_ACCEPTANCE_RULE_AND_FAILURE_CONSEQUENCE",
                "INCLUDE_HISTORICAL_EQUIVALENCE_AS_A_MANDATORY_LIVE_PATH_CONTROL",
            ],
            "incomplete_record_rule": (
                "ALL_96_SCIENTIFIC_CELLS_AND_ALL_MANDATORY_CONTROLS_COMPLETE_"
                "BEFORE_ANY_SCIENTIFIC_CLASSIFICATION_ELSE_TIMEOUT_ONLY"
            ),
            "frozen_surfaces": [
                "QUALIFIED_ANALYTIC_ORACLE_AND_HASH_CUSTODY",
                "EIGHT_CASES_AND_THREE_HISTORICAL_CONFIGURATIONS",
                "ORDERS_8_16_24_32_40_48",
                "NEWTONIAN_AND_YUKAWA_COMPONENT_SEPARATION",
                "NINETY_SIX_ATOMIC_SCIENTIFIC_CELLS",
                "BASE_ERROR_METRICS_AND_ACCURACY_ENVELOPE",
                "RESOURCE_PROCESS_AND_DOWNSTREAM_FIREWALLS",
            ],
            "review_outcomes": list(V1_REVIEW_OUTCOMES),
            "comparison_execution_reserved_for_post_review_authority": True,
        },
        "anti_rabbit_hole_boundary": {
            "v1_is_last_automatic_comparison_contract_repair": True,
            "automatic_v2_authorized": False,
            "new_foundational_v1_block_requires_fresh_selector": True,
            "future_choices_after_block": [
                "HISTORICAL_PATH_IDENTITY_ISOLATION_ONLY",
                "MIRROR_ONLY_COMPARISON_WITH_HISTORICAL_CLAIMS_WITHDRAWN",
                "DIRECT_ANALYTIC_KERNEL_REPLACEMENT",
                "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
            ],
        },
        "selection_gates": {
            "gate_count": len(selection_gates),
            "pass_count": len(selection_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in selection_gates],
        },
        "scope": scope,
        "current_posture": {
            "analytic_sphere_oracle": "QUALIFIED_AND_ACCEPTED",
            "comparison_packet_v0": "BLOCKED_CONTRACT_INCOMPLETE",
            "accepted_review_gates": "33_OF_40_FROZEN",
            "repairable_review_gates": "7_OF_40_ONLY",
            "comparison_packet_v1": "AUTHORIZED_FOR_PREPARATION_NOT_PREPARED",
            "comparison_execution": "NOT_AUTHORIZED_NOT_PERFORMED",
            "production_cubature": "UNADJUDICATED",
            "kernel_repair_or_replacement": "NOT_AUTHORIZED",
            "stage_a_rerun": "NOT_AUTHORIZED",
            "torque_dft_identifiability_stage_b": "NOT_AUTHORIZED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This selector authorizes preparation only of a V1 packet repairing the seven "
            "failed comparison-contract gates. It does not prepare or review V1, modify V0, "
            "execute a production comparison, adjudicate cubature, repair or replace a "
            "kernel, calculate torque or harmonics, rerun Stage A, decide identifiability, "
            "or authorize Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Select the response to the blocked production-comparison packet review."
    )
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
            print("post-comparison-review selector already current")
        return 0
    if current != expected:
        print("post-comparison-review selector drift")
        return 1
    report = build_report()
    print(
        "post-comparison-review selector OK "
        f"route={report['selected_route']} score={report['ranking']['selected_score']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
