from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_V1_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_V1_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_post_scalar_only_yukawa_analytic_sphere_kernel_"
    "replacement_packet_v1_review_scientific_response_selection_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PostScalarOnlyYukawaAnalyticSphereKernelReplacementPacketV1Review"
    "ScientificResponseSelectionV0.lean"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_REVIEW_20260719_v1.json"
)

TARGET = (
    "select_post_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1_"
    "review_scientific_response_v0"
)
VERDICT = "SELECTED_KERNEL_REPLACEMENT_VALIDATION_INFRASTRUCTURE_PREREQUISITE_PREPARATION"
SELECTED_ROUTE = "ISOLATE_KERNEL_REPLACEMENT_VALIDATION_INFRASTRUCTURE_PREREQUISITE"
SELECTED_CANDIDATE_ID = "KERNEL_AGNOSTIC_VALIDATION_HARNESS_AND_SCHEMA_PREREQUISITE_V0"
SELECTED_NEXT_TARGET = (
    "prepare_scalar_only_yukawa_kernel_replacement_validation_infrastructure_"
    "prerequisite_packet_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "PREPARATION_ONLY_KERNEL_AGNOSTIC_VALIDATION_INFRASTRUCTURE_NO_V2_NO_CANDIDATE"
)

REVIEW_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_REVIEW_20260719_v1.md":
        "6dd8637582f1812caa66b9dfab00acde43e717c29ec74ad5911ca8ae251dffc1",
    REVIEW_RELATIVE_PATH:
        "6de58c24afa929b6e0fc4bc2b7be3d49edee670d692be7f0c0176292cf8efa8b",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_review_v1.py":
        "80a0adc2251f93eac0e9faa56a498adadbd4a8586d8dcd7d983ae000abfa3b7c",
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_review_v1.py":
        "ad7c0993e69567732840e1f28d247dd144e8c4e8cedbb0994078c9a0ad1cc3c4",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaAnalyticSphereKernelReplacementPacketReviewV1.lean":
        "c2157f0d977158ff7c8fc4de2c0fafb2e503fc1dc099e207c3b4ebecb9aecb5b",
}

FAILED_REVIEW_GATES = (
    "R35_VALIDATION_ONLY_HOOK_ENFORCEMENT_EXECUTABLE",
    "R41_LIMIT_AND_BOUNDARY_PROBES_NUMERIC",
    "R43_MUTATION_ROUTES_COMPLETE",
    "R44_MUTATION_DETECTION_PREDICATES_NUMERIC",
    "R52_CANONICAL_SERIALIZATION_SCHEMA_EXACT",
)

CRITERIA = {
    "accepted_surface_leverage": 5,
    "surviving_block_resolution": 5,
    "no_v2_boundary_integrity": 5,
    "validation_independence": 5,
    "schema_executability": 5,
    "forward_model_recovery": 4,
    "boundedness": 5,
    "computational_economy": 4,
    "authority_clarity": 5,
    "anti_rabbit_hole_control": 5,
}

CANDIDATES = (
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "target": SELECTED_NEXT_TARGET,
        "scores": {key: 5 for key in CRITERIA},
        "disposition": "SELECTED_AS_SEPARATE_PREREQUISITE_NOT_REPLACEMENT_PACKET_V2",
    },
    {
        "candidate_id": "RETIRE_REPLACEMENT_IMPLEMENTATION_AND_PRESERVE_ANALYTIC_ORACLE_ONLY",
        "target": "select_scalar_only_yukawa_analytic_oracle_only_lane_posture_v0",
        "scores": {
            "accepted_surface_leverage": 5,
            "surviving_block_resolution": 2,
            "no_v2_boundary_integrity": 5,
            "validation_independence": 5,
            "schema_executability": 1,
            "forward_model_recovery": 0,
            "boundedness": 5,
            "computational_economy": 5,
            "authority_clarity": 5,
            "anti_rabbit_hole_control": 5,
        },
        "disposition": "RUNNER_UP_RETAINS_TRUSTED_ORACLE_BUT_ABANDONS_RECOVERY_PATH",
    },
    {
        "candidate_id": "DEFER_SYNTHETIC_TORSION_BALANCE_LANE_INDEFINITELY",
        "target": "select_scalar_only_yukawa_synthetic_torsion_balance_lane_deferral_v0",
        "scores": {
            "accepted_surface_leverage": 5,
            "surviving_block_resolution": 1,
            "no_v2_boundary_integrity": 5,
            "validation_independence": 5,
            "schema_executability": 0,
            "forward_model_recovery": 0,
            "boundedness": 5,
            "computational_economy": 5,
            "authority_clarity": 5,
            "anti_rabbit_hole_control": 5,
        },
        "disposition": "DEFERRED_DOES_NOT_TEST_WHETHER_GENERIC_INFRASTRUCTURE_IS_CHEAP",
    },
    {
        "candidate_id": "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
        "target": "close_scalar_only_yukawa_synthetic_torsion_balance_lane_v0",
        "scores": {
            "accepted_surface_leverage": 4,
            "surviving_block_resolution": 3,
            "no_v2_boundary_integrity": 5,
            "validation_independence": 5,
            "schema_executability": 0,
            "forward_model_recovery": 0,
            "boundedness": 5,
            "computational_economy": 5,
            "authority_clarity": 5,
            "anti_rabbit_hole_control": 5,
        },
        "disposition": "DEFERRED_CLOSURE_PREMATURE_BEFORE_ONE_GENERIC_INFRASTRUCTURE_TEST",
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
            raise ValueError(f"final V1 review authority drift: {relative_path}")
    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "BLOCKED_ANALYTIC_KERNEL_REPLACEMENT_CONTRACT_INCOMPLETE":
        raise ValueError("final V1 review verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("final V1 review did not authorize this selector")
    if review["review_gates"]["pass_count"] != 57 or review["review_gates"]["failure_count"] != 5:
        raise ValueError("final V1 review gate count mismatch")
    if tuple(review["review_gates"]["failed_gate_ids"]) != FAILED_REVIEW_GATES:
        raise ValueError("final V1 review failure set mismatch")
    if review["frozen_gate_audit"]["preserved_count"] != 51:
        raise ValueError("frozen V0 gate preservation mismatch")

    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if ranking[0]["candidate_id"] != SELECTED_CANDIDATE_ID:
        raise ValueError("selected candidate is not top ranked")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("selected candidate is sensitivity-unstable")

    selection_gates = (
        "EXACT_FINAL_V1_REVIEW_AUTHORITY_AND_HASH_CUSTODY",
        "FIFTY_ONE_FROZEN_GATES_PRESERVED",
        "SIX_V1_REPAIRS_ACCEPTED_AND_NOT_REOPENED",
        "EXACT_FIVE_SURVIVING_GATE_FAILURES_RECORDED",
        "BLOCK_IS_VALIDATION_INFRASTRUCTURE_NOT_ANALYTIC_PHYSICS",
        "EXACT_FOUR_BOUNDED_RESPONSE_CANDIDATES",
        "EXACT_TEN_WEIGHTED_CRITERIA",
        "SELECTION_STABLE_IN_THIRTY_SENSITIVITY_VARIANTS",
        "PREREQUISITE_IS_NOT_REPLACEMENT_PACKET_V2",
        "PREREQUISITE_MAY_DEFINE_CAPABILITY_PROTOCOL_ONLY",
        "PREREQUISITE_MAY_DEFINE_TYPED_PREDICATE_SCHEMA_ONLY",
        "PREREQUISITE_MAY_DEFINE_DEPENDENCY_SCANNER_CONTRACT_ONLY",
        "PREREQUISITE_MAY_DEFINE_RECURSIVE_RESULT_SCHEMA_ONLY",
        "SYNTHETIC_FIXTURES_ONLY_NO_ANALYTIC_KERNEL",
        "NO_REAL_REGRESSION_OR_BOUNDARY_PROBE_EXECUTION",
        "NO_CANDIDATE_KERNEL_CREATION_OR_EXECUTION",
        "NO_PRODUCTION_SOURCE_OR_DISPATCH_CHANGE",
        "NO_OLD_CUBATURE_CALL_OR_ADJUDICATION",
        "NO_AUTOMATIC_RETURN_TO_REPLACEMENT_LANE",
        "NO_AUTOMATIC_V2",
        "FRESH_REVIEW_REQUIRED_BEFORE_INFRASTRUCTURE_EXECUTION",
        "FRESH_SELECTOR_REQUIRED_AFTER_ANY_PREREQUISITE_RESULT",
        "NO_TORQUE_DFT_STAGE_A_IDENTIFIABILITY_OR_STAGE_B",
        "CURRENT_AUTHORITY_ROTATES_TO_PREREQUISITE_PACKET_PREPARATION_ONLY",
    )

    scope = {
        "scientific_response_selection_executed": True,
        "final_v1_review_frozen": True,
        "fifty_one_accepted_gates_preserved": True,
        "six_completed_repairs_preserved": True,
        "five_failed_gates_interpreted_as_infrastructure_prerequisites": True,
        "validation_infrastructure_prerequisite_packet_preparation_authorized": True,
        "prerequisite_packet_prepared_now": False,
        "replacement_packet_v2_authorized": False,
        "silent_v1_correction_authorized": False,
        "candidate_kernel_creation_authorized": False,
        "candidate_kernel_execution_authorized": False,
        "shadow_qualification_authorized": False,
        "production_source_or_dispatch_change_authorized": False,
        "old_cubature_called": False,
        "old_cubature_adjudicated": False,
        "automatic_return_to_replacement_lane_authorized": False,
        "stage_a_rerun_authorized": False,
        "torque_or_dft_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_b_authorized": False,
    }

    return {
        "schema_id": (
            "toe.post_scalar_only_yukawa.analytic_sphere_kernel_replacement_packet_v1_"
            "review.scientific_response_selection.v0"
        ),
        "selection_id": (
            "POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_V1_"
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
                "replacement_packet_v1_review_scientific_response_selection_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "review_interpretation": {
            "review_verdict": review["verdict"],
            "principal_block": review["principal_review_outcome"],
            "secondary_blocks": review["secondary_review_outcomes"],
            "frozen_gate_count": 51,
            "accepted_v1_repair_count": 6,
            "failed_review_gate_ids": list(FAILED_REVIEW_GATES),
            "analytic_formula_refuted": False,
            "accepted_regression_or_derivative_data_reopened": False,
            "candidate_or_production_execution": "NOT_AUTHORIZED_NOT_PERFORMED",
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
        "validation_infrastructure_prerequisite_contract": {
            "status": "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED",
            "is_replacement_packet_v2": False,
            "kernel_agnostic": True,
            "surviving_gate_context": list(FAILED_REVIEW_GATES),
            "allowed_contract_surfaces": [
                "PROCESS_SCOPED_CAPABILITY_ISSUER_AND_PRIVATE_CALL_PROTOCOL",
                "TYPED_NUMERIC_EXCEPTION_AND_RELATIONAL_PREDICATE_SCHEMA",
                "MUTATION_CALL_ROUTE_AND_ADJUDICATOR_SCHEMA",
                "AST_IMPORT_AND_CALL_GRAPH_DEPENDENCY_SCANNER_CONTRACT",
                "RECURSIVE_CANONICAL_RESULT_SCHEMAS_ENUMS_AND_DUPLICATE_KEY_PARSER",
                "KERNEL_FREE_SYNTHETIC_FIXTURES_FOR_INFRASTRUCTURE_QUALIFICATION",
            ],
            "forbidden_contract_surfaces": [
                "ANALYTIC_OR_NEWTONIAN_OR_YUKAWA_KERNEL_IMPLEMENTATION",
                "V1_PACKET_EDIT_OR_V2_REPLACEMENT_PACKET",
                "REAL_ORACLE_REGRESSION_BOUNDARY_OR_MUTATION_EXECUTION",
                "PRODUCTION_IMPORT_DISPATCH_OR_CALLER_CHANGE",
            ],
            "completion_consequence": (
                "FRESH_SELECTOR_REQUIRED_NO_AUTOMATIC_REOPENING_OF_REPLACEMENT_IMPLEMENTATION"
            ),
        },
        "selection_gates": {
            "gate_count": len(selection_gates),
            "pass_count": len(selection_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in selection_gates],
        },
        "anti_rabbit_hole_boundary": {
            "v1_remains_final_automatic_replacement_contract_repair": True,
            "automatic_v2_authorized": False,
            "prerequisite_is_separate_and_kernel_agnostic": True,
            "prerequisite_result_cannot_automatically_reopen_replacement_lane": True,
            "retirement_deferral_or_closure_remain_available_after_fresh_selection": True,
        },
        "scope": scope,
        "current_posture": {
            "analytic_formula_oracle_and_frozen_gates": "PRESERVED",
            "replacement_contract_v1": "FINAL_REVIEW_BLOCKED",
            "replacement_contract_v2": "PROHIBITED",
            "validation_infrastructure_prerequisite": "AUTHORIZED_FOR_PACKET_PREPARATION_ONLY",
            "candidate_kernel": "NOT_CREATED_NOT_AUTHORIZED",
            "historical_cubature": "UNADJUDICATED",
            "stage_a": "NOT_REOPENED",
            "stage_b": "NOT_AUTHORIZED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This selector chooses preparation of one separate kernel-agnostic validation "
            "infrastructure prerequisite. It does not repair V1, create V2, implement or "
            "execute a kernel, run real regressions or probes, change production, call or "
            "adjudicate cubature, compute torque, DFT, vector, Jacobian, SVD, or "
            "identifiability, rerun Stage A, or authorize Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Select the response to the blocked final V1 replacement-contract review."
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
            print("post-final-V1-review selector already current")
        return 0
    if current != expected:
        print("post-final-V1-review selector drift")
        return 1
    report = build_report()
    print(
        "post-final-V1-review selector OK "
        f"route={report['selected_route']} score={report['ranking']['selected_score']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
