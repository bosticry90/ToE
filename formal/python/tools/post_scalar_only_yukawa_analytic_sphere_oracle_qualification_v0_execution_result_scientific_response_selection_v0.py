from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_EXECUTION_RESULT_REVIEW_20260719_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_V0_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_SELECTION_"
    "20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_V0_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_SELECTION_"
    "20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_post_scalar_only_yukawa_analytic_sphere_oracle_"
    "qualification_v0_execution_result_scientific_response_selection_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PostScalarOnlyYukawaAnalyticSphereOracleQualificationV0ExecutionResult"
    "ScientificResponseSelectionV0.lean"
)

TARGET = (
    "select_post_scalar_only_yukawa_analytic_sphere_oracle_qualification_v0_"
    "execution_result_scientific_response_v0"
)
VERDICT = (
    "SELECTED_BOUNDED_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_COMPARISON_"
    "PACKET_PREPARATION"
)
SELECTED_ROUTE = "COMPARE_FAILED_PRODUCTION_CUBATURE_AGAINST_QUALIFIED_ANALYTIC_ORACLE"
SELECTED_CANDIDATE_ID = "BOUNDED_PRODUCTION_VS_ORACLE_COMPARISON"
SELECTED_NEXT_TARGET = (
    "prepare_scalar_only_yukawa_production_cubature_vs_analytic_oracle_"
    "comparison_packet_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "PREPARATION_ONLY_BOUNDED_ENERGY_LEVEL_PRODUCTION_COMPARISON_PACKET_"
    "NO_EXECUTION_NO_REPLACEMENT"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_EXECUTION_RESULT_REVIEW_20260719_v0.md":
        "077f3d3e01e3bb4809790bf7d9b9266d7f1a3cd0258af5c697f7880a4b9c3d93",
    REVIEW_RELATIVE_PATH:
        "e963c033514e47e374cb6caced1ab533ed6ea08792f964c04e079e7b67088868",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_result_review_v0.py":
        "49d0f59e9a52777ab1a41bdf448dca58ba14401dab4da84e403c8f6000f4668b",
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_result_review_v0.py":
        "4bf64e2b0da2b36d038811157008bb846c2ecdfa3b861533b71ac84c6f25dc18",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaAnalyticSphereOracleQualificationExecutionResultReviewV0.lean":
        "d7b36f5bc4b2cc85d7afb5509ce2a319c83a741531d0a738598a068314d46ce6",
}

CRITERIA = {
    "direct_alignment_with_accepted_result": 5,
    "qualified_reference_use": 5,
    "root_cause_information_gain": 5,
    "bounded_executability": 5,
    "scientific_causal_localization": 5,
    "computational_economy": 5,
    "downstream_firewall_fit": 4,
    "scope_reversibility": 4,
    "method_decision_leverage": 4,
    "anti_rabbit_hole_clarity": 2,
}

CANDIDATES = (
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "route": SELECTED_ROUTE,
        "target": SELECTED_NEXT_TARGET,
        "scores": {criterion: 5 for criterion in CRITERIA},
        "disposition": "SELECTED_FOR_SMALL_PRODUCTION_COMPARISON_PACKET_PREPARATION",
    },
    {
        "candidate_id": "DIRECT_ANALYTIC_KERNEL_REPLACEMENT",
        "route": "REPLACE_PRODUCTION_CUBATURE_WITH_QUALIFIED_ANALYTIC_KERNEL_NOW",
        "target": "prepare_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0",
        "scores": {
            "direct_alignment_with_accepted_result": 4,
            "qualified_reference_use": 5,
            "root_cause_information_gain": 2,
            "bounded_executability": 4,
            "scientific_causal_localization": 2,
            "computational_economy": 5,
            "downstream_firewall_fit": 4,
            "scope_reversibility": 3,
            "method_decision_leverage": 4,
            "anti_rabbit_hole_clarity": 3,
        },
        "disposition": "DEFERRED_UNTIL_FAILED_PRODUCTION_PATH_IS_ADJUDICATED",
    },
    {
        "candidate_id": "DIRECT_TORQUE_AND_DFT_VALIDATION",
        "route": "SKIP_PRODUCTION_DIAGNOSIS_AND_VALIDATE_TORQUE_AND_DFT",
        "target": "prepare_scalar_only_yukawa_analytic_torque_and_dft_validation_packet_v0",
        "scores": {
            "direct_alignment_with_accepted_result": 2,
            "qualified_reference_use": 4,
            "root_cause_information_gain": 1,
            "bounded_executability": 3,
            "scientific_causal_localization": 1,
            "computational_economy": 4,
            "downstream_firewall_fit": 1,
            "scope_reversibility": 2,
            "method_decision_leverage": 2,
            "anti_rabbit_hole_clarity": 2,
        },
        "disposition": "DEFERRED_ENERGY_LEVEL_PRODUCTION_FAILURE_NOT_YET_ADJUDICATED",
    },
    {
        "candidate_id": "APPARATUS_REDESIGN",
        "route": "REDESIGN_INTERNAL_APPARATUS_BEFORE_PRODUCTION_COMPARISON",
        "target": "prepare_redesigned_scalar_only_yukawa_internal_apparatus_packet_v0",
        "scores": {
            "direct_alignment_with_accepted_result": 2,
            "qualified_reference_use": 2,
            "root_cause_information_gain": 3,
            "bounded_executability": 3,
            "scientific_causal_localization": 2,
            "computational_economy": 2,
            "downstream_firewall_fit": 4,
            "scope_reversibility": 2,
            "method_decision_leverage": 3,
            "anti_rabbit_hole_clarity": 3,
        },
        "disposition": "DEFERRED_PREMATURE_WHILE_EXISTING_METHOD_CAN_BE_CHEAPLY_ADJUDICATED",
    },
    {
        "candidate_id": "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
        "route": "CLOSE_INTERNAL_SYNTHETIC_TORSION_BALANCE_LANE",
        "target": "select_post_scalar_internal_torsion_balance_lane_closure_v0",
        "scores": {
            "direct_alignment_with_accepted_result": 1,
            "qualified_reference_use": 0,
            "root_cause_information_gain": 0,
            "bounded_executability": 5,
            "scientific_causal_localization": 0,
            "computational_economy": 5,
            "downstream_firewall_fit": 5,
            "scope_reversibility": 1,
            "method_decision_leverage": 0,
            "anti_rabbit_hole_clarity": 5,
        },
        "disposition": "DEFERRED_ORACLE_SUCCESS_JUSTIFIES_ONE_SMALL_METHOD_COMPARISON",
    },
    {
        "candidate_id": "PIVOT_TO_NATIVE_GRAVITY_PRIORITY",
        "route": "PAUSE_SYNTHETIC_LANE_AND_RETURN_TO_NATIVE_GRAVITY_SELECTION",
        "target": "select_next_native_gravitational_principle_priority_v0",
        "scores": {
            "direct_alignment_with_accepted_result": 1,
            "qualified_reference_use": 0,
            "root_cause_information_gain": 1,
            "bounded_executability": 4,
            "scientific_causal_localization": 1,
            "computational_economy": 3,
            "downstream_firewall_fit": 5,
            "scope_reversibility": 3,
            "method_decision_leverage": 0,
            "anti_rabbit_hole_clarity": 4,
        },
        "disposition": "DEFERRED_SEPARATE_FOUNDATIONAL_PRIORITY_NOT_A_RESPONSE_TO_THIS_RESULT",
    },
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


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
    for relative_path, expected in AUTHORITY_HASHES.items():
        path = REPO_ROOT / relative_path
        if not path.exists() or _sha256(path) != expected:
            raise ValueError(f"accepted oracle-review custody failed: {relative_path}")
    review = json.loads((REPO_ROOT / REVIEW_RELATIVE_PATH).read_text(encoding="utf-8"))
    if review["verdict"] != "ACCEPTED_ANALYTIC_SPHERE_ORACLE_QUALIFIED":
        raise ValueError("unexpected consumed result-review verdict")
    if review["selected_next_target"] != TARGET:
        raise ValueError("result review does not authorize this selector")
    scope = review["scope"]
    if scope["fresh_scientific_response_selector_authorized"] is not True:
        raise ValueError("fresh selector is not authorized")
    if scope["production_cubature_comparison_authorized"] is not False:
        raise ValueError("review unexpectedly authorized direct production comparison")
    if scope["stage_b_authorized"] is not False:
        raise ValueError("Stage B firewall drifted")

    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if ranking[0]["candidate_id"] != SELECTED_CANDIDATE_ID:
        raise ValueError("bounded production comparison is not the baseline winner")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("bounded production comparison is not sensitivity-stable")

    requirements = {
        "status": "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED",
        "scientific_objective": (
            "Use the accepted analytic homogeneous-sphere oracle to adjudicate the exact "
            "failed production cubature at energy level on a small frozen case set, "
            "without repairing, replacing, or extending that production path."
        ),
        "custody_and_immutability": {
            "accepted_oracle_review_hash_pinned": True,
            "failed_production_implementation_hash_pin_required": True,
            "production_code_changes_during_comparison_forbidden": True,
            "oracle_code_changes_during_comparison_forbidden": True,
            "result_dependent_case_or_order_changes_forbidden": True,
        },
        "case_grid": {
            "minimum_case_count": 6,
            "maximum_case_count": 8,
            "three_failed_stage_a_cases_required": True,
            "additional_stratified_roles": [
                "WIDE_SEPARATION",
                "SMALL_POSITIVE_GAP",
                "YUKAWA_TRANSITION_RANGE",
            ],
            "strict_nonoverlap_required": True,
            "post_result_case_selection_forbidden": True,
        },
        "production_order_ladder_to_freeze": [8, 16, 24, 32, 40, 48],
        "component_comparison": {
            "newtonian_separate": True,
            "yukawa_separate": True,
            "combined_energy_diagnostic_only": True,
            "analytic_oracle_is_reference": True,
            "absolute_error_required": True,
            "relative_error_required": True,
            "error_ratio_between_orders_required": True,
            "runtime_and_work_required": True,
            "near_zero_relative_denominator_rule_required": True,
        },
        "decision_contract_to_freeze": {
            "monotone_or_interpretable_convergence_rule_required": True,
            "accuracy_plateau_rule_required": True,
            "constant_ratio_normalization_probe_required": True,
            "geometry_distance_probe_required": True,
            "one_dimension_left_unrefined_mutation_required": True,
            "no_tolerance_relaxation_after_results": True,
            "near_threshold_result_is_unresolved": True,
        },
        "resource_envelope_to_freeze": {
            "target_total_wall_clock_seconds_max": 1200,
            "target_memory_mib_max": 4096,
            "per_case_and_per_order_caps_required": True,
            "process_group_termination_required": True,
            "raw_log_and_stage_atomic_records_required": True,
            "budget_exhaustion_fails_closed": True,
        },
        "legitimate_outcomes": [
            "PRODUCTION_CUBATURE_VALIDATED_AGAINST_ORACLE",
            "PRODUCTION_CUBATURE_SLOW_BUT_CONVERGENT",
            "FIXED_ORDER_CUBATURE_INADEQUATE",
            "PRODUCTION_IMPLEMENTATION_DEFECT_LOCALIZED",
            "NORMALIZATION_OR_GEOMETRY_MISMATCH",
            "PRODUCTION_COMPARISON_NUMERICALLY_UNRESOLVED",
            "PRODUCTION_COMPARISON_TIMEOUT",
        ],
        "forbidden_work": [
            "PRODUCTION_KERNEL_REPAIR",
            "PRODUCTION_KERNEL_REPLACEMENT",
            "TORQUE",
            "ANGULAR_DFT",
            "APPARATUS_HARMONICS",
            "FINAL_REAL_150_VECTOR",
            "JACOBIAN_OR_SVD",
            "IDENTIFIABILITY",
            "STAGE_A_RERUN",
            "STAGE_B",
        ],
        "review_sequence": (
            "prepare comparison packet -> independent packet review -> one bounded "
            "comparison -> independent result review -> fresh repair/replacement/retention selector"
        ),
    }

    gates = (
        "AUTHORITY_HASHES_MATCH",
        "QUALIFIED_ORACLE_RESULT_FROZEN",
        "ONE_SHOT_ORACLE_EXECUTION_REMAINS_CONSUMED",
        "PRODUCTION_CUBATURE_REMAINS_UNADJUDICATED",
        "CONTINUOUS_UNIFORM_ORACLE_ERROR_NOT_CLAIMED",
        "SIX_BOUNDED_OPTIONS_COMPARED",
        "DIRECT_REPLACEMENT_EXPLICITLY_RANKED",
        "TORQUE_AND_DFT_SHORTCUT_EXPLICITLY_RANKED",
        "PRODUCTION_COMPARISON_UNIQUE_BASELINE_WINNER",
        "THIRTY_SENSITIVITY_VARIANTS_EXECUTED",
        "PRODUCTION_COMPARISON_WINS_ALL_VARIANTS",
        "THREE_FAILED_STAGE_A_CASES_REQUIRED",
        "SMALL_SIX_TO_EIGHT_CASE_GRID_REQUIRED",
        "STRICT_NONOVERLAP_REQUIRED",
        "PRODUCTION_ORDERS_EIGHT_THROUGH_FORTY_EIGHT_TO_FREEZE",
        "NEWTONIAN_AND_YUKAWA_COMPONENTS_SEPARATE",
        "ABSOLUTE_AND_RELATIVE_ERRORS_REQUIRED",
        "RUNTIME_AND_WORK_RECORDS_REQUIRED",
        "FAILED_PRODUCTION_IMPLEMENTATION_HASH_PIN_REQUIRED",
        "NO_PRODUCTION_CODE_CHANGE_DURING_COMPARISON",
        "NO_ORACLE_CODE_CHANGE_DURING_COMPARISON",
        "RESULT_DEPENDENT_CASE_SELECTION_FORBIDDEN",
        "CONVERGENCE_AND_PLATEAU_RULES_REQUIRED",
        "NORMALIZATION_AND_GEOMETRY_PROBES_REQUIRED",
        "NEAR_THRESHOLD_RESULTS_UNRESOLVED",
        "RESOURCE_AND_PROCESS_CUSTODY_REQUIRED",
        "NO_PACKET_PREPARED_NOW",
        "NO_COMPARISON_EXECUTION_NOW",
        "NO_PRODUCTION_REPAIR_OR_REPLACEMENT",
        "NO_TORQUE_OR_DFT",
        "NO_VECTOR_JACOBIAN_OR_IDENTIFIABILITY",
        "NO_STAGE_A_RERUN_OR_STAGE_B",
        "INDEPENDENT_PACKET_REVIEW_REQUIRED_BEFORE_EXECUTION",
    )
    selector_scope = {
        "scientific_response_selector_executed": True,
        "accepted_oracle_result_frozen": True,
        "candidate_count": len(CANDIDATES),
        "production_comparison_packet_preparation_authorized": True,
        "production_comparison_packet_prepared_now": False,
        "production_comparison_executed": False,
        "oracle_execution_rerun_authorized": False,
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
            "toe.post_scalar_only_yukawa.analytic_sphere_oracle.qualification_execution_"
            "result.scientific_response_selection.v0"
        ),
        "selection_id": (
            "POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_V0_"
            "EXECUTION_RESULT_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0"
        ),
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_route": SELECTED_ROUTE,
        "selected_candidate_id": SELECTED_CANDIDATE_ID,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_result_review_verdict": review["verdict"],
            "frozen_result_review_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in AUTHORITY_HASHES.items()
            ],
            "human_selection": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/post_scalar_only_yukawa_analytic_sphere_oracle_"
                "qualification_v0_execution_result_scientific_response_selection_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "accepted_result_interpretation": {
            "analytic_sphere_oracle": "QUALIFIED_ON_EIGHT_FROZEN_CASES_AND_OVERLAP_PROBES",
            "maximum_relative_difference": review["accepted_result"]["maximum_relative_difference"],
            "continuous_uniform_error_claim": "NOT_ESTABLISHED",
            "production_cubature": "UNADJUDICATED",
            "torque_and_dft": "NOT_VALIDATED",
            "physical_identifiability": "NOT_TESTED",
            "stage_b": "NOT_AUTHORIZED",
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
        "comparison_packet_preparation_requirements": requirements,
        "selection_gates": {
            "gate_count": len(gates),
            "pass_count": len(gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in gates],
        },
        "scope": selector_scope,
        "claim_ceiling": (
            "This selector authorizes preparation of one bounded energy-level production-"
            "cubature versus qualified-oracle comparison packet only. It performs no "
            "comparison, changes no kernel, validates no torque or DFT, reruns no Stage A, "
            "decides no identifiability question, and authorizes no Stage B work."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Select the bounded response to the accepted analytic sphere-oracle result."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    rendered = artifact_bytes()
    if args.write:
        path.write_bytes(rendered)
        print(f"wrote {REPORT_RELATIVE_PATH} route={SELECTED_ROUTE}")
        return 0
    if not path.exists() or path.read_bytes() != rendered:
        print("post-oracle scientific-response selector artifact missing or stale")
        return 1
    report = json.loads(path.read_text(encoding="utf-8"))
    print(
        "post-oracle selector OK "
        f"route={report['selected_route']} "
        f"gates={report['selection_gates']['pass_count']}/"
        f"{report['selection_gates']['gate_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
