from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_V0_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_V0_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_post_scalar_only_yukawa_analytic_sphere_kernel_"
    "replacement_packet_v0_review_scientific_response_selection_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PostScalarOnlyYukawaAnalyticSphereKernelReplacementPacketV0Review"
    "ScientificResponseSelectionV0.lean"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_REVIEW_20260719_v0.json"
)

TARGET = (
    "select_post_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0_"
    "review_scientific_response_v0"
)
VERDICT = "SELECTED_ANALYTIC_KERNEL_REPLACEMENT_CONTRACT_REPAIR_V1_PREPARATION"
SELECTED_ROUTE = "REPAIR_ANALYTIC_KERNEL_REPLACEMENT_EXECUTION_CONTRACT"
SELECTED_CANDIDATE_ID = "ELEVEN_GATE_REPLACEMENT_CONTRACT_REPAIR_V1"
SELECTED_NEXT_TARGET = (
    "prepare_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1"
)
SELECTED_NEXT_TARGET_KIND = (
    "PREPARATION_ONLY_FINAL_ELEVEN_GATE_CONTRACT_REPAIR_NO_KERNEL_IMPLEMENTATION"
)

REVIEW_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_REVIEW_20260719_v0.md":
        "b3157203008109bbf7945f0bc5a03cafcb28b13c95128f5d3559b8abf65a1553",
    REVIEW_RELATIVE_PATH:
        "6d775002f667a32caed167b1d601dc29cfac34a5b4e498af372676b1ca5cda37",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_review_v0.py":
        "ff47312ebe199ae8f033b96389885fa3acdba5843943ad55bfcaa079620da505",
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_review_v0.py":
        "81b3a3b289a27ddf6d162c86b1d042d24eb1f9cd1c49a0fad504b36b6030cf2e",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaAnalyticSphereKernelReplacementPacketReviewV0.lean":
        "c1a30c10822caaffd036f06a7a5cfe92b4f53ac1d13296314acdcbc4103e52bd",
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

CRITERIA = {
    "accepted_surface_leverage": 5,
    "closes_review_failures": 5,
    "validation_independence": 5,
    "interface_clarity": 5,
    "numerical_reliability": 5,
    "forward_model_recovery": 5,
    "boundedness": 4,
    "computational_economy": 4,
    "authority_clarity": 4,
    "anti_rabbit_hole_control": 4,
}

CANDIDATES = (
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "target": SELECTED_NEXT_TARGET,
        "scores": {
            "accepted_surface_leverage": 5,
            "closes_review_failures": 5,
            "validation_independence": 5,
            "interface_clarity": 5,
            "numerical_reliability": 5,
            "forward_model_recovery": 5,
            "boundedness": 5,
            "computational_economy": 4,
            "authority_clarity": 5,
            "anti_rabbit_hole_control": 5,
        },
        "disposition": "SELECTED_FOR_FINAL_PRE_IMPLEMENTATION_CONTRACT_REPAIR_ONLY",
    },
    {
        "candidate_id": "RETIRE_ANALYTIC_REPLACEMENT_AND_DEFER_TORSION_BALANCE_LANE",
        "target": "select_scalar_only_yukawa_internal_torsion_balance_lane_deferral_v0",
        "scores": {
            "accepted_surface_leverage": 1,
            "closes_review_failures": 5,
            "validation_independence": 5,
            "interface_clarity": 5,
            "numerical_reliability": 5,
            "forward_model_recovery": 0,
            "boundedness": 5,
            "computational_economy": 5,
            "authority_clarity": 5,
            "anti_rabbit_hole_control": 5,
        },
        "disposition": "RUNNER_UP_DEFERRED_ONE_BOUNDED_REPAIR_REMAINS_PROPORTIONATE",
    },
    {
        "candidate_id": "SPLIT_ENERGY_AND_RADIAL_DERIVATIVE_QUALIFICATION",
        "target": "prepare_scalar_only_yukawa_split_energy_derivative_qualification_packet_v0",
        "scores": {
            "accepted_surface_leverage": 4,
            "closes_review_failures": 3,
            "validation_independence": 5,
            "interface_clarity": 3,
            "numerical_reliability": 5,
            "forward_model_recovery": 4,
            "boundedness": 5,
            "computational_economy": 3,
            "authority_clarity": 4,
            "anti_rabbit_hole_control": 4,
        },
        "disposition": "DEFERRED_FRAGMENTS_ONE_LIVE_ENERGY_DERIVATIVE_INTERFACE",
    },
    {
        "candidate_id": "ENERGY_ONLY_SHADOW_QUALIFICATION_WITH_DERIVATIVE_DEFERRED",
        "target": "prepare_scalar_only_yukawa_energy_only_shadow_qualification_packet_v0",
        "scores": {
            "accepted_surface_leverage": 4,
            "closes_review_failures": 2,
            "validation_independence": 4,
            "interface_clarity": 3,
            "numerical_reliability": 4,
            "forward_model_recovery": 3,
            "boundedness": 5,
            "computational_economy": 4,
            "authority_clarity": 3,
            "anti_rabbit_hole_control": 2,
        },
        "disposition": "DEFERRED_CANNOT_QUALIFY_DECISION_BEARING_DU_DD_INTERFACE",
    },
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
    for relative_path, expected in REVIEW_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected:
            raise ValueError(f"replacement review authority drift: {relative_path}")

    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "BLOCKED_ANALYTIC_KERNEL_REPLACEMENT_CONTRACT_INCOMPLETE":
        raise ValueError("replacement review verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("replacement review did not authorize this selector")
    if review.get("principal_review_outcome") != "BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE":
        raise ValueError("replacement review principal outcome mismatch")
    if tuple(review["review_gates"]["failed_gate_ids"]) != FAILED_REVIEW_GATES:
        raise ValueError("replacement review failure set mismatch")
    if review["review_gates"]["pass_count"] != 51 or review["review_gates"]["failure_count"] != 11:
        raise ValueError("replacement review gate counts mismatch")
    if review["scope"]["shadow_kernel_implementation_performed"] is not False:
        raise ValueError("review unexpectedly performed a shadow implementation")

    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if ranking[0]["candidate_id"] != SELECTED_CANDIDATE_ID:
        raise ValueError("selected candidate is not top ranked")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("selected candidate is sensitivity-unstable")

    selection_gates = (
        "EXACT_BLOCKED_REVIEW_AUTHORITY_AND_TARGET",
        "FIFTY_ONE_ACCEPTED_REVIEW_GATES_FROZEN",
        "EXACT_ELEVEN_FAILED_REVIEW_GATES_RECORDED",
        "FORMULAS_EVALUATOR_AND_FIREWALLS_NOT_REOPENED",
        "BLOCK_INTERPRETED_AS_CONTRACT_NOT_PHYSICAL_FAILURE",
        "EXACT_FOUR_BOUNDED_RESPONSE_CANDIDATES",
        "EXACT_TEN_WEIGHTED_CRITERIA",
        "SELECTION_STABLE_IN_THIRTY_SENSITIVITY_VARIANTS",
        "REPAIR_LIMITED_TO_ELEVEN_FAILED_GATES",
        "INDEPENDENT_DU_DD_REFERENCE_REQUIRED",
        "EIGHT_REGRESSION_INPUT_ROWS_REQUIRED",
        "MUTATION_ROUTES_AND_NUMERIC_PREDICATES_REQUIRED",
        "INTERFACE_COMPATIBILITY_MATRIX_REQUIRED",
        "ARRAY_ATOMIC_FAILURE_RULE_REQUIRED",
        "VALIDATION_HOOK_ENFORCEMENT_REQUIRED",
        "LIMIT_AND_BOUNDARY_PROBE_GRID_REQUIRED",
        "RUNTIME_WORKLOAD_VECTOR_REQUIRED",
        "CANONICAL_SERIALIZATION_SCHEMA_REQUIRED",
        "V1_IS_FINAL_AUTOMATIC_REPLACEMENT_CONTRACT_REPAIR",
        "NO_KERNEL_IMPLEMENTATION_OR_EXECUTION_NOW",
        "NO_PRODUCTION_ADOPTION_OR_DISPATCH_CHANGE",
        "NO_OLD_CUBATURE_CALL_OR_ADJUDICATION",
        "NO_TORQUE_DFT_STAGE_A_IDENTIFIABILITY_OR_STAGE_B",
        "FRESH_INDEPENDENT_V1_REVIEW_REQUIRED",
    )

    scope = {
        "scientific_response_selection_executed": True,
        "blocked_v0_review_frozen": True,
        "fifty_one_accepted_review_gates_frozen": True,
        "eleven_failed_gates_selected_for_contract_repair": True,
        "v1_packet_preparation_authorized": True,
        "v1_packet_prepared_now": False,
        "v1_packet_review_authorized_now": False,
        "shadow_kernel_implementation_authorized": False,
        "shadow_kernel_implementation_performed": False,
        "production_kernel_replacement_authorized": False,
        "production_kernel_replacement_performed": False,
        "old_cubature_called": False,
        "old_cubature_adjudicated": False,
        "automatic_v2_authorized": False,
        "torque_or_dft_authorized": False,
        "stage_a_rerun_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_b_authorized": False,
    }

    return {
        "schema_id": (
            "toe.post_scalar_only_yukawa.analytic_sphere_kernel_replacement_packet_v0_"
            "review.scientific_response_selection.v0"
        ),
        "selection_id": (
            "POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_V0_"
            "REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0"
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
                for path, digest in REVIEW_HASHES.items()
            ],
            "human_selection": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/post_scalar_only_yukawa_analytic_sphere_kernel_"
                "replacement_packet_v0_review_scientific_response_selection_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "review_interpretation": {
            "review_verdict": review["verdict"],
            "principal_block": review["principal_review_outcome"],
            "secondary_blocks": review["secondary_review_outcomes"],
            "accepted_review_gates_frozen": 51,
            "failed_review_gates": list(FAILED_REVIEW_GATES),
            "analytic_formula_refuted": False,
            "production_cubature_adjudicated": False,
            "implementation_execution": "NOT_AUTHORIZED_NOT_PERFORMED",
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
        "v1_repair_contract": {
            "status": "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED",
            "accepted_review_gate_count_frozen": 51,
            "repair_gate_count": len(FAILED_REVIEW_GATES),
            "repair_gate_ids": list(FAILED_REVIEW_GATES),
            "all_other_surfaces": "FROZEN_NO_REDESIGN",
            "required_repairs": [
                "EXACT_INTERNAL_FUNCTION_REPLACEMENT_LIST_DISPATCH_SYMBOL_AND_UNCHANGED_CALLERS",
                "CURRENT_VERSUS_PROPOSED_LAMBDA_COMPONENT_COMPATIBILITY_MATRIX",
                "ATOMIC_ARRAY_FAILURE_SEMANTICS",
                "ENFORCEABLE_VALIDATION_ONLY_HOOK_ROUTE",
                "EIGHT_COMPLETE_REGRESSION_INPUT_AND_OUTPUT_ROWS",
                "INDEPENDENT_HIGH_PRECISION_DU_DD_REFERENCE_AND_TOLERANCES",
                "EXACT_LIMIT_BOUNDARY_CASES_LADDERS_EXPECTATIONS_AND_TOLERANCES",
                "TWELVE_MUTATION_CASE_COMPONENT_INJECTION_AND_EXECUTION_ROUTES",
                "TWELVE_NUMERIC_OR_EXCEPTION_DETECTION_PREDICATES",
                "EXACT_TEN_THOUSAND_CALL_RUNTIME_WORKLOAD_AND_COMPONENT_ORDER",
                "CANONICAL_SERIALIZATION_OBJECT_FLOAT_ENCODING_KEY_ORDER_AND_FAILURE_RULE",
            ],
            "derivative_reference_independence_rule": (
                "REFERENCE_MUST_BE_DERIVED_FROM_FROZEN_HIGH_PRECISION_ENERGY_VALUES_OR_AN_"
                "INDEPENDENT_HIGH_PRECISION_RADIAL_DIFFERENTIATION_PATH_AND_MAY_NOT_CALL_"
                "THE_CANDIDATE_DERIVATIVE"
            ),
            "candidate_kernel_creation": "FORBIDDEN_DURING_PACKET_PREPARATION",
            "production_source_change": "FORBIDDEN",
            "automatic_v2": "PROHIBITED",
            "v1_is_final_automatic_contract_repair": True,
        },
        "selection_gates": {
            "gate_count": len(selection_gates),
            "pass_count": len(selection_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in selection_gates],
        },
        "anti_rabbit_hole_boundary": {
            "v1_is_final_automatic_replacement_contract_repair": True,
            "automatic_v2_authorized": False,
            "v1_review_block_requires_fresh_selector": True,
            "lane_deferral_or_closure_remains_available": True,
        },
        "scope": scope,
        "current_posture": {
            "analytic_formula_and_oracle": "ACCEPTED_FROZEN",
            "replacement_contract_v0": "BLOCKED",
            "replacement_contract_v1": "AUTHORIZED_FOR_PREPARATION_NOT_PREPARED",
            "candidate_kernel": "NOT_CREATED_NOT_AUTHORIZED",
            "production_replacement": "NOT_AUTHORIZED_NOT_PERFORMED",
            "historical_cubature": "UNADJUDICATED",
            "stage_a": "NOT_REOPENED",
            "stage_b": "NOT_AUTHORIZED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This selector chooses one final eleven-gate pre-implementation contract repair. "
            "It does not prepare V1, create or execute a candidate kernel, change production "
            "dispatch, call or adjudicate cubature, compute torque, DFT, a real-150 vector, "
            "Jacobian, SVD, or identifiability result, rerun Stage A, or authorize Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Select the response to the blocked analytic-kernel replacement review."
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
            print("post-replacement-review selector already current")
        return 0
    if current != expected:
        print("post-replacement-review selector drift")
        return 1
    report = build_report()
    print(
        "post-replacement-review selector OK "
        f"route={report['selected_route']} score={report['ranking']['selected_score']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
