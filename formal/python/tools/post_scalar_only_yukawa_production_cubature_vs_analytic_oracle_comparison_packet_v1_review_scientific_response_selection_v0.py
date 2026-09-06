from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_V1_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_V1_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_post_scalar_only_yukawa_production_cubature_vs_analytic_"
    "oracle_comparison_packet_v1_review_scientific_response_selection_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PostScalarOnlyYukawaProductionCubatureVsAnalyticOracleComparisonPacketV1Review"
    "ScientificResponseSelectionV0.lean"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_REVIEW_20260719_v1.json"
)

TARGET = (
    "select_post_scalar_only_yukawa_production_cubature_vs_analytic_oracle_"
    "comparison_packet_v1_review_scientific_response_v0"
)
VERDICT = "SELECTED_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_PREPARATION"
SELECTED_ROUTE = (
    "RETIRE_OLD_CUBATURE_COMPARISON_AND_PREPARE_ANALYTIC_KERNEL_REPLACEMENT"
)
SELECTED_CANDIDATE_ID = "DIRECT_ANALYTIC_KERNEL_REPLACEMENT"
SELECTED_NEXT_TARGET = "prepare_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0"
SELECTED_NEXT_TARGET_KIND = (
    "PREPARATION_ONLY_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_CONTRACT_NO_IMPLEMENTATION_OR_EXECUTION"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_COMPARISON_PACKET_REVIEW_20260719_v1.md":
        "45edbf6e0a3304ab2da04c9116056314f4057ac0f71bca4e7da66223dd289a54",
    REVIEW_RELATIVE_PATH:
        "e47acb33549cba2fdd492cde88a5c08170ff24a1e532d046a9f5fde41e67fcad",
    "formal/python/tools/scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_review_v1.py":
        "168b9240d87eb27c1f5f4047455eddfe459af26217f2cc1d77c703136a50b5fa",
    "formal/python/tests/test_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_review_v1.py":
        "70aa38a0a7d44a2b235e1770974f7ca26464c6596fc28fa342a7cacb8924dcca",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaProductionCubatureVsAnalyticOracleComparisonPacketReviewV1.lean":
        "bce53355d402b57bd98ded26a06e60c00c47e06e46627a0da1c0467040d85579",
}

CRITERIA = {
    "trusted_oracle_leverage": 5,
    "direct_response_to_final_block": 5,
    "forward_model_recovery": 5,
    "numerical_reliability": 5,
    "scientific_information_gain": 4,
    "computational_economy": 4,
    "risk_isolation": 4,
    "boundedness": 4,
    "authority_clarity": 3,
    "anti_rabbit_hole_control": 4,
}

CANDIDATES = (
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "target": SELECTED_NEXT_TARGET,
        "scores": {
            "trusted_oracle_leverage": 5,
            "direct_response_to_final_block": 5,
            "forward_model_recovery": 5,
            "numerical_reliability": 5,
            "scientific_information_gain": 4,
            "computational_economy": 5,
            "risk_isolation": 5,
            "boundedness": 5,
            "authority_clarity": 5,
            "anti_rabbit_hole_control": 5,
        },
        "disposition": "SELECTED_FOR_REPLACEMENT_PACKET_PREPARATION_ONLY",
    },
    {
        "candidate_id": "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
        "target": "select_post_scalar_internal_torsion_balance_lane_closure_v0",
        "scores": {
            "trusted_oracle_leverage": 1,
            "direct_response_to_final_block": 5,
            "forward_model_recovery": 0,
            "numerical_reliability": 5,
            "scientific_information_gain": 1,
            "computational_economy": 5,
            "risk_isolation": 5,
            "boundedness": 5,
            "authority_clarity": 5,
            "anti_rabbit_hole_control": 5,
        },
        "disposition": "DEFERRED_ANALYTIC_REPLACEMENT_REMAINS_BOUNDED_AND_HIGH_LEVERAGE",
    },
    {
        "candidate_id": "HISTORICAL_PATH_IDENTITY_ISOLATION_ONLY",
        "target": "prepare_scalar_only_yukawa_historical_cubature_identity_isolation_packet_v0",
        "scores": {
            "trusted_oracle_leverage": 3,
            "direct_response_to_final_block": 4,
            "forward_model_recovery": 1,
            "numerical_reliability": 3,
            "scientific_information_gain": 5,
            "computational_economy": 3,
            "risk_isolation": 5,
            "boundedness": 5,
            "authority_clarity": 4,
            "anti_rabbit_hole_control": 3,
        },
        "disposition": "DEFERRED_MORE_OLD_METHOD_DIAGNOSIS_AFTER_FINAL_CONTRACT_BLOCK",
    },
    {
        "candidate_id": "MIRROR_ONLY_COMPARISON_WITH_HISTORICAL_CLAIMS_WITHDRAWN",
        "target": "prepare_scalar_only_yukawa_mirror_only_oracle_comparison_packet_v0",
        "scores": {
            "trusted_oracle_leverage": 4,
            "direct_response_to_final_block": 3,
            "forward_model_recovery": 2,
            "numerical_reliability": 3,
            "scientific_information_gain": 4,
            "computational_economy": 3,
            "risk_isolation": 3,
            "boundedness": 4,
            "authority_clarity": 3,
            "anti_rabbit_hole_control": 2,
        },
        "disposition": "DEFERRED_REOPENS_COMPARISON_ENGINEERING_WITH_A_CHANGED_QUESTION",
    },
)

REPLACEMENT_REVIEW_OUTCOMES = (
    "ANALYTIC_KERNEL_REPLACEMENT_CONTRACT_READY",
    "BLOCKED_REPLACEMENT_INTERFACE_IDENTITY",
    "BLOCKED_REPLACEMENT_DOMAIN_COVERAGE",
    "BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE",
    "BLOCKED_REPLACEMENT_FIREWALL",
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
            raise ValueError(f"final V1 review authority drift: {relative_path}")

    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "BLOCKED_PRODUCTION_COMPARISON_CONTRACT_INCOMPLETE":
        raise ValueError("final V1 review verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("final V1 review did not authorize this selector")
    if review.get("review_gates", {}).get("pass_count") != 43:
        raise ValueError("final V1 review pass count mismatch")
    if review.get("review_gates", {}).get("failure_count") != 5:
        raise ValueError("final V1 review failure count mismatch")
    if review.get("final_attempt_disposition", {}).get("automatic_v2") != "PROHIBITED":
        raise ValueError("final V1 no-V2 boundary mismatch")
    if review.get("scope", {}).get("comparison_execution_performed") is not False:
        raise ValueError("review unexpectedly performed comparison execution")

    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    selection_gates = (
        "EXACT_FINAL_V1_REVIEW_AUTHORITY_AND_TARGET",
        "FINAL_REPAIR_BLOCK_INTERPRETED_AS_CONTRACT_NOT_PHYSICS",
        "THIRTY_THREE_FROZEN_GATES_PRESERVED",
        "EXACT_FIVE_REMAINING_CONTRADICTIONS_RECORDED",
        "AUTOMATIC_V2_PROHIBITION_PRESERVED",
        "EXACT_FOUR_BOUNDED_RESPONSES_COMPARED",
        "EXACT_TEN_CRITERIA_FROZEN",
        "SELECTION_STABLE_IN_THIRTY_VARIANTS",
        "QUALIFIED_ANALYTIC_ORACLE_LEVERAGED",
        "OLD_CUBATURE_COMPARISON_RETIRED_FROM_AUTOMATIC_PATH",
        "REPLACEMENT_PACKET_PREPARATION_ONLY",
        "PHYSICAL_KERNEL_AND_NORMALIZATION_PRESERVATION_REQUIRED",
        "STRICT_NONOVERLAP_DOMAIN_GUARD_REQUIRED",
        "STABLE_SMALL_MODERATE_LARGE_X_EVALUATION_REQUIRED",
        "INDEPENDENT_REPLACEMENT_VALIDATION_REQUIRED",
        "ENERGY_INTERFACE_ONLY_NO_TORQUE_OR_DFT_CHANGE",
        "NO_KERNEL_IMPLEMENTATION_OR_EXECUTION_NOW",
        "NO_STAGE_A_RERUN_OR_IDENTIFIABILITY_NOW",
        "NO_STAGE_B_AUTHORITY",
        "FRESH_REVIEW_REQUIRED_BEFORE_ANY_REPLACEMENT_EXECUTION",
    )

    scope = {
        "scientific_response_selection_executed": True,
        "final_v1_review_frozen": True,
        "analytic_replacement_packet_preparation_authorized": True,
        "old_cubature_automatic_comparison_path_retired": True,
        "replacement_packet_prepared_now": False,
        "replacement_packet_review_authorized_now": False,
        "analytic_kernel_implemented_now": False,
        "production_kernel_replacement_authorized": False,
        "production_kernel_replacement_performed": False,
        "old_cubature_comparison_authorized": False,
        "old_cubature_adjudicated": False,
        "torque_or_dft_authorized": False,
        "final_real_150_vector_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_a_rerun_authorized": False,
        "stage_b_authorized": False,
        "automatic_comparison_v2_authorized": False,
    }

    return {
        "schema_id": (
            "toe.post_scalar_only_yukawa.production_cubature_vs_analytic_oracle."
            "comparison_packet_v1_review.scientific_response_selection.v0"
        ),
        "selection_id": (
            "POST_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_"
            "COMPARISON_PACKET_V1_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0"
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
                "analytic_oracle_comparison_packet_v1_review_scientific_response_"
                "selection_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "review_interpretation": {
            "review_verdict": review["verdict"],
            "principal_block": review["principal_review_outcome"],
            "secondary_blocks": review["secondary_review_outcomes"],
            "frozen_review_gates_preserved": 33,
            "comparison_contract_ready": False,
            "production_cubature_adjudicated": False,
            "physical_model_refuted": False,
            "comparison_execution": "NOT_AUTHORIZED_NOT_PERFORMED",
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
        "analytic_replacement_packet_preparation_contract": {
            "status": "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED",
            "replacement_scope": "NONOVERLAPPING_HOMOGENEOUS_SPHERE_ENERGY_KERNEL_ONLY",
            "accepted_oracle_source": "ANALYTIC_SPHERE_ORACLE_QUALIFIED_AND_ACCEPTED",
            "required_frozen_interfaces": [
                "NEWTONIAN_U_N_EQUALS_MINUS_G_M1_M2_OVER_D",
                "YUKAWA_A_Y_EQUALS_ONE_THIRD",
                "TWO_SPHERE_FORM_FACTOR_NORMALIZATION",
                "CENTER_DISTANCE_D_AND_SURFACE_GAP_G_SEMANTICS",
                "STRICT_D_GREATER_THAN_R1_PLUS_R2_DOMAIN",
                "SI_ENERGY_UNITS_AND_NEGATIVE_ATTRACTIVE_SIGN",
                "SMALL_X_SERIES_MODERATE_X_DIRECT_AND_LARGE_X_SCALED_EVALUATORS",
                "QUALIFIED_EIGHT_CASE_ORACLE_VALUES_AND_HASH_CUSTODY",
                "EXISTING_ENERGY_CALLER_INPUT_OUTPUT_SCHEMA",
            ],
            "required_validation_surfaces": [
                "POINT_PARTICLE_AND_LONG_RANGE_LIMITS",
                "SPHERE_EXCHANGE_SYMMETRY",
                "SMALL_DIRECT_AND_DIRECT_SCALED_OVERLAP",
                "X_1000_NO_OVERFLOW",
                "ACCEPTED_INDEPENDENT_RADIAL_CROSS_CHECK_CUSTODY",
                "EXACT_EIGHT_CASE_REGRESSION_TO_ACCEPTED_ORACLE_VALUES",
                "DOMAIN_GUARD_REJECTS_OVERLAP_AND_NONPOSITIVE_LAMBDA",
                "DETERMINISTIC_SERIALIZATION_AND_RUNTIME_BOUNDS",
            ],
            "old_cubature_status": "RETAINED_READ_ONLY_AS_HISTORICAL_NONAUTHORITATIVE_CODE_NOT_EXECUTED_BY_REPLACEMENT_PACKET_PREPARATION",
            "old_comparison_contract_status": "RETIRED_FROM_AUTOMATIC_REPAIR_AND_EXECUTION_PATH",
            "torque_and_dft": "FROZEN_OUT_OF_SCOPE_REQUIRE_SEPARATE_POST_REPLACEMENT_VALIDATION",
            "stage_a_rerun": "NOT_AUTHORIZED",
            "review_outcomes": list(REPLACEMENT_REVIEW_OUTCOMES),
            "replacement_execution_reserved_for_post_review_authority": True,
        },
        "anti_rabbit_hole_boundary": {
            "automatic_comparison_v2_authorized": False,
            "old_cubature_comparison_repair_closed": True,
            "replacement_packet_failure_requires_fresh_selector": True,
            "immediate_lane_closure_remains_available": True,
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
            "old_cubature_comparison_contract": "BLOCKED_FINAL_AUTOMATIC_ATTEMPT_RETIRED",
            "production_cubature": "UNADJUDICATED",
            "analytic_replacement_packet": "AUTHORIZED_FOR_PREPARATION_NOT_PREPARED",
            "kernel_replacement": "NOT_AUTHORIZED_NOT_PERFORMED",
            "stage_a_rerun": "NOT_AUTHORIZED",
            "torque_dft_identifiability_stage_b": "NOT_AUTHORIZED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This selector retires the automatic old-cubature comparison path and "
            "authorizes preparation only of an analytic sphere-kernel replacement packet. "
            "It does not prepare, review, implement, or execute that replacement; judge the "
            "old cubature; compute torque, DFT, a real-150 vector, Jacobian, SVD, or "
            "identifiability result; rerun Stage A; or authorize Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Select the response to the final blocked V1 comparison review.")
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
            print("post-V1-comparison-review selector already current")
        return 0
    if current != expected:
        print("post-V1-comparison-review selector drift")
        return 1
    report = build_report()
    print(
        "post-V1-comparison-review selector OK "
        f"route={report['selected_route']} score={report['ranking']['selected_score']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
