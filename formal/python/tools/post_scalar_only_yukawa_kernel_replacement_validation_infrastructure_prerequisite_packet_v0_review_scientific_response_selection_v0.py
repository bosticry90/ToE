from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_"
    "INFRASTRUCTURE_PREREQUISITE_PACKET_V0_REVIEW_SCIENTIFIC_RESPONSE_"
    "SELECTION_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_"
    "INFRASTRUCTURE_PREREQUISITE_PACKET_V0_REVIEW_SCIENTIFIC_RESPONSE_"
    "SELECTION_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_post_scalar_only_yukawa_kernel_replacement_validation_"
    "infrastructure_prerequisite_packet_v0_review_scientific_response_selection_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PostScalarOnlyYukawaKernelReplacementValidationInfrastructurePrerequisitePacketV0"
    "ReviewScientificResponseSelectionV0.lean"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_"
    "INFRASTRUCTURE_PREREQUISITE_PACKET_REVIEW_20260719_v0.json"
)

TARGET = (
    "select_post_scalar_only_yukawa_kernel_replacement_validation_infrastructure_"
    "prerequisite_packet_v0_review_scientific_response_v0"
)
VERDICT = "SELECTED_ISOLATED_NON_DECISION_BEARING_ANALYTIC_KERNEL_SANDBOX_EXECUTION"
SELECTED_ROUTE = "AUTHORIZE_ISOLATED_NON_DECISION_BEARING_SANDBOX_IMPLEMENTATION"
SELECTED_CANDIDATE_ID = "ANALYTIC_SPHERE_KERNEL_EXPLORATORY_SANDBOX_V0_ONCE"
SELECTED_NEXT_TARGET = (
    "execute_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_v0_once"
)
SELECTED_NEXT_TARGET_KIND = (
    "ONE_ISOLATED_IMPLEMENTATION_AND_EXECUTION_NON_PRODUCTION_NON_ADJUDICATIVE_"
    "NO_SCIENTIFIC_CLAIM"
)

REVIEW_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_INFRASTRUCTURE_PREREQUISITE_PACKET_REVIEW_20260719_v0.md":
        "9b48ed6ae7fe193eb1baf952b314e557120b9759c9d7ab60d9d7421ed1996b11",
    REVIEW_RELATIVE_PATH:
        "729f86d0b1f2ab1ed475b073017fff8f47f4768720c4fab0d65b00c7652c668a",
    "formal/python/tools/scalar_only_yukawa_kernel_replacement_validation_infrastructure_prerequisite_packet_review_v0.py":
        "3926cbfd8d54b67f8f72c1b5924b8461d445fdb4f87aad2f72f74f66e293e326",
    "formal/python/tests/test_scalar_only_yukawa_kernel_replacement_validation_infrastructure_prerequisite_packet_review_v0.py":
        "015a400d91dadea94f15e17a05218c48dc314e5f0c20c5886d415258f5187a16",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaKernelReplacementValidationInfrastructurePrerequisitePacketReviewV0.lean":
        "050daa36ce6d574f71e49e666cce5f17b7c225acb95ae3cced7d0dffce088fed",
}

EXACT_SELECTOR_OPTIONS = (
    "AUTHORIZE_ISOLATED_NON_DECISION_BEARING_SANDBOX_IMPLEMENTATION",
    "RETIRE_OR_DEFER_ANALYTIC_REPLACEMENT_LANE",
)

EXPLORATORY_LABELS = (
    "EXPLORATORY_IMPLEMENTATION_RESULT",
    "NON_PRODUCTION",
    "NON_ADJUDICATIVE",
    "NO_SCIENTIFIC_CLAIM",
)

CRITERIA = {
    "scientific_learning": 5,
    "accepted_evidence_leverage": 5,
    "sandbox_isolation": 5,
    "boundedness": 5,
    "computational_economy": 4,
    "terminal_convergence": 5,
    "production_safety": 5,
    "reversibility": 5,
    "anti_rabbit_hole_control": 5,
    "authority_clarity": 5,
}

CANDIDATES = (
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "route": EXACT_SELECTOR_OPTIONS[0],
        "target": SELECTED_NEXT_TARGET,
        "scores": {key: 5 for key in CRITERIA},
        "disposition": "SELECTED_ONE_SHOT_EXPLORATORY_IMPLEMENTATION_AND_EXECUTION",
    },
    {
        "candidate_id": "RETIRE_OR_DEFER_ANALYTIC_REPLACEMENT_LANE",
        "route": EXACT_SELECTOR_OPTIONS[1],
        "target": "retire_or_defer_scalar_only_yukawa_analytic_replacement_lane_v0",
        "scores": {
            "scientific_learning": 0,
            "accepted_evidence_leverage": 2,
            "sandbox_isolation": 5,
            "boundedness": 5,
            "computational_economy": 5,
            "terminal_convergence": 5,
            "production_safety": 5,
            "reversibility": 3,
            "anti_rabbit_hole_control": 5,
            "authority_clarity": 5,
        },
        "disposition": "RUNNER_UP_SAFE_BUT_FORGOES_BOUNDED_EXPLORATORY_EVIDENCE",
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
            raise ValueError(f"terminal prerequisite review authority drift: {relative_path}")
    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "VALIDATION_INFRASTRUCTURE_PREREQUISITE_READY":
        raise ValueError("terminal prerequisite review verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("terminal prerequisite review did not authorize this selector")
    if review["review_gates"]["pass_count"] != 48:
        raise ValueError("terminal prerequisite review pass count mismatch")
    if review["review_gates"]["failure_count"] != 0:
        raise ValueError("terminal prerequisite review must be failure-free")
    if tuple(review["terminal_consequence"]["current_selector_options_exact"]) != EXACT_SELECTOR_OPTIONS:
        raise ValueError("terminal prerequisite review two-option boundary mismatch")
    if review["scope"]["validation_infrastructure_contract_ready"] is not True:
        raise ValueError("validation infrastructure contract not READY")

    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if len(CANDIDATES) != 2:
        raise ValueError("terminal selector must contain exactly two candidates")
    if tuple(candidate["route"] for candidate in CANDIDATES) != EXACT_SELECTOR_OPTIONS:
        raise ValueError("candidate routes differ from terminal selector options")
    if ranking[0]["candidate_id"] != SELECTED_CANDIDATE_ID:
        raise ValueError("sandbox candidate is not top ranked")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("sandbox selection is sensitivity-unstable")

    selection_gates = (
        "EXACT_TERMINAL_REVIEW_AUTHORITY_AND_HASH_CUSTODY",
        "READY_VERDICT_AND_FORTY_EIGHT_PASSES_FROZEN",
        "EXACT_TWO_OPTION_TERMINAL_BOUNDARY_PRESERVED",
        "NO_THIRD_ROUTE_OR_REPAIR_PATH",
        "EXACT_TEN_WEIGHTED_CRITERIA",
        "SANDBOX_WINS_ALL_THIRTY_SENSITIVITY_VARIANTS",
        "ONE_IMPLEMENTATION_AND_ONE_EXECUTION_ONLY",
        "NO_AUTOMATIC_RETRY_OR_RERUN",
        "KERNEL_AGNOSTIC_INFRASTRUCTURE_IMPLEMENTATION_ISOLATED",
        "TWELVE_SYNTHETIC_CONTROLS_MANDATORY",
        "EIGHT_FROZEN_KERNEL_REGRESSION_CASES_ONLY",
        "ENERGY_AND_RADIAL_DERIVATIVE_EXPLORATORY_CHECKS_ONLY",
        "EXACT_FOUR_EXPLORATORY_LABELS_MANDATORY",
        "NON_PRODUCTION_AND_NON_ADJUDICATIVE",
        "NO_SCIENTIFIC_CLAIM",
        "NO_HISTORICAL_CUBATURE_CALL_OR_ADJUDICATION",
        "NO_PRODUCTION_IMPORT_DISPATCH_OR_SOURCE_CHANGE",
        "NO_SHADOW_QUALIFICATION_ADOPTION_OR_ROLLBACK",
        "NO_TORQUE_DFT_REAL150_JACOBIAN_SVD_OR_IDENTIFIABILITY",
        "NO_STAGE_A_RERUN_OR_STAGE_B",
        "FAILURE_CANNOT_CREATE_REPAIR_OR_PREREQUISITE_SUCCESSOR",
        "RESULT_STOPS_FOR_INDEPENDENT_EXPLORATORY_REVIEW",
        "SELECTION_ARTIFACT_ONLY_NO_SANDBOX_IMPLEMENTATION_NOW",
        "CURRENT_AUTHORITY_ROTATES_TO_ONE_SHOT_SANDBOX_EXECUTION",
    )

    scope = {
        "scientific_response_selection_executed": True,
        "terminal_ready_review_frozen": True,
        "exact_two_option_constraint_preserved": True,
        "isolated_sandbox_implementation_authorized": True,
        "one_sandbox_execution_authorized": True,
        "sandbox_implemented_now": False,
        "sandbox_executed_now": False,
        "automatic_retry_or_rerun_authorized": False,
        "production_source_or_dispatch_change_authorized": False,
        "historical_cubature_call_authorized": False,
        "historical_cubature_adjudication_authorized": False,
        "shadow_qualification_authorized": False,
        "production_adoption_authorized": False,
        "stage_a_rerun_authorized": False,
        "torque_or_dft_authorized": False,
        "real_150_vector_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_b_authorized": False,
        "scientific_claim_authorized": False,
    }

    return {
        "schema_id": (
            "toe.post_scalar_only_yukawa.kernel_replacement.validation_infrastructure_"
            "prerequisite_packet_v0_review.scientific_response_selection.v0"
        ),
        "selection_id": (
            "POST_SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_INFRASTRUCTURE_"
            "PREREQUISITE_PACKET_V0_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0"
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
                "formal/python/tools/post_scalar_only_yukawa_kernel_replacement_"
                "validation_infrastructure_prerequisite_packet_v0_review_scientific_"
                "response_selection_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "review_interpretation": {
            "review_verdict": review["verdict"],
            "review_pass_count": review["review_gates"]["pass_count"],
            "review_failure_count": review["review_gates"]["failure_count"],
            "contract_ready_for_exploratory_sandbox": True,
            "infrastructure_implemented_or_qualified": False,
            "analytic_kernel_scientifically_validated": False,
            "historical_cubature_adjudicated": False,
            "production_replacement_warranted": False,
        },
        "selection_policy": {
            "candidate_count": len(CANDIDATES),
            "options_exact": list(EXACT_SELECTOR_OPTIONS),
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
        "sandbox_execution_contract": {
            "status": "ONE_ISOLATED_IMPLEMENTATION_AND_EXECUTION_AUTHORIZED_NOT_PERFORMED",
            "execution_count_authorized": 1,
            "implementation_location": (
                "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
                "exploratory_sandbox_v0.py"
            ),
            "result_location": (
                "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
                "EXPLORATORY_SANDBOX_20260719_v0.json"
            ),
            "mandatory_result_labels": list(EXPLORATORY_LABELS),
            "infrastructure_control_count": 12,
            "kernel_regression_case_count": 8,
            "kernel_outputs_per_case": [
                "NEWTONIAN_ENERGY", "YUKAWA_ENERGY",
                "NEWTONIAN_RADIAL_DERIVATIVE", "YUKAWA_RADIAL_DERIVATIVE",
            ],
            "resource_envelope": {
                "synthetic_infrastructure_stage_timeout_seconds": 60,
                "synthetic_infrastructure_stage_memory_mib": 256,
                "total_timeout_seconds": 300,
                "total_memory_mib": 1024,
            },
            "result_interpretation": (
                "EXPLORATORY_AGREEMENT_OR_DISAGREEMENT_ONLY_NOT_KERNEL_QUALIFICATION_"
                "NOT_CUBATURE_ADJUDICATION_NOT_SCIENTIFIC_EVIDENCE"
            ),
            "completion_consequence": (
                "STOP_FOR_INDEPENDENT_EXPLORATORY_RESULT_REVIEW_NO_AUTOMATIC_RETRY_"
                "REPAIR_PRODUCTION_OR_SCIENTIFIC_ADVANCEMENT"
            ),
        },
        "forbidden_during_sandbox": [
            "IMPORT_OR_MODIFY_PRODUCTION_KERNEL_OR_DISPATCH",
            "CALL_OR_ADJUDICATE_HISTORICAL_CUBATURE",
            "SHADOW_QUALIFICATION_ADOPTION_OR_ROLLBACK",
            "TORQUE_DFT_REAL150_JACOBIAN_SVD_IDENTIFIABILITY_STAGE_A_OR_STAGE_B",
            "SCIENTIFIC_OR_PRODUCTION_CLAIM",
        ],
        "selection_gates": {
            "gate_count": len(selection_gates),
            "pass_count": len(selection_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in selection_gates],
        },
        "terminal_boundary": {
            "governance_spiral_closed": True,
            "infrastructure_v1_authorized": False,
            "repair_packet_authorized": False,
            "prerequisite_to_prerequisite_authorized": False,
            "sandbox_preparation_packet_authorized": False,
            "automatic_retry_authorized": False,
            "sandbox_failure_successor": "FRESH_SELECTOR_OR_RETIRE_DEFER_ONLY",
            "sandbox_success_successor": "INDEPENDENT_EXPLORATORY_RESULT_REVIEW_ONLY",
        },
        "scope": scope,
        "current_posture": {
            "validation_infrastructure_contract": "READY_NOT_IMPLEMENTED_OR_QUALIFIED",
            "analytic_kernel": "AUTHORIZED_FOR_ISOLATED_EXPLORATORY_IMPLEMENTATION_ONLY",
            "historical_cubature": "UNADJUDICATED_AND_FORBIDDEN_IN_SANDBOX",
            "production": "UNCHANGED_NOT_AUTHORIZED",
            "stage_a": "NOT_REOPENED",
            "stage_b": "NOT_AUTHORIZED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This terminal selector authorizes one isolated implementation and one "
            "non-decision-bearing sandbox execution using the accepted validation "
            "infrastructure contract, twelve synthetic controls, and eight frozen analytic "
            "kernel regression cases. It does not implement or execute the sandbox in this "
            "selection, qualify or adopt a kernel, call or adjudicate historical cubature, "
            "change production, rerun Stage A, compute torque, DFT, vector, Jacobian, SVD, "
            "or identifiability, authorize Stage B, or permit a scientific claim."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Select sandbox execution or retirement after the terminal READY review."
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
            print("terminal sandbox selector already current")
        return 0
    if current != expected:
        print("terminal sandbox selector drift")
        return 1
    report = build_report()
    print(
        "terminal sandbox selector OK "
        f"route={report['selected_route']} score={report['ranking']['selected_score']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
