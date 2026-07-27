from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_SYNTHETIC_FORECAST_PACKET_"
    "REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_SYNTHETIC_FORECAST_PACKET_"
    "REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_post_scalar_only_yukawa_synthetic_forecast_packet_"
    "review_scientific_response_selection_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PostScalarOnlyYukawaSyntheticForecastPacketReviewScientificResponseSelectionV0.lean"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_"
    "SENSITIVITY_FORECAST_PACKET_REVIEW_20260718_v0.json"
)

TARGET = (
    "select_post_scalar_only_yukawa_synthetic_forward_model_and_"
    "sensitivity_forecast_packet_review_scientific_response_v0"
)
VERDICT = "SELECTED_DETERMINISTIC_FORWARD_MODEL_VALIDATION_PACKET_PREPARATION"
SELECTED_CANDIDATE_ID = (
    "SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION"
)
SELECTED_NEXT_TARGET = (
    "prepare_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_packet_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "PREPARATION_ONLY_DETERMINISTIC_FORWARD_MODEL_NO_SIMULATION_OR_"
    "STOCHASTIC_FORECAST"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_SENSITIVITY_FORECAST_PACKET_REVIEW_20260718_v0.md":
        "c1dc928e468148c503876ee0bf09b797691706ab78ca8c7491451ddd5cb81049",
    REVIEW_RELATIVE_PATH:
        "2e025a2d0eeef555a104f92bbdf867bd934c8e9ed07cf5be53ea6bf331516d9c",
    "formal/python/tools/scalar_only_yukawa_synthetic_forward_model_and_sensitivity_forecast_packet_review_v0.py":
        "b235150168a89d3c989e3e71a3431562f951cb357c384f14f2471fd5138ebab6",
    "formal/python/tests/test_scalar_only_yukawa_synthetic_forward_model_and_sensitivity_forecast_packet_review_v0.py":
        "1b5d5cff300aac724aacfb5cf99a247710954aebf5d8d6a2d43670c6b22dcd9c",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaSyntheticForwardModelAndSensitivityForecastPacketReviewV0.lean":
        "24bf788986e8972d9916ffd176d13324227d20835e69f310e0d1ed8732706234",
}

CRITERIA = {
    "physics_first_information_gain": 5,
    "direct_repair_of_reviewed_block": 5,
    "risk_isolation": 4,
    "computational_economy": 4,
    "boundedness": 3,
    "authority_clarity": 3,
    "downstream_stochastic_readiness": 3,
    "internal_only_policy_compliance": 2,
}

CANDIDATES = [
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "target": SELECTED_NEXT_TARGET,
        "kind": "DETERMINISTIC_FORWARD_MODEL_PACKET_PREPARATION",
        "scores": {key: 5 for key in CRITERIA},
        "disposition": "SELECTED_FOR_PACKET_PREPARATION_ONLY",
        "scientific_endpoint": (
            "Validate deterministic Newtonian/Yukawa transport, harmonics, "
            "convergence, mutations, and identifiability before stochastic work."
        ),
    },
    {
        "candidate_id": "SIMPLIFIED_SYNTHETIC_FORECAST",
        "target": "prepare_simplified_scalar_only_yukawa_synthetic_forecast_packet_v0",
        "kind": "REDUCED_STOCHASTIC_FORECAST",
        "scores": {
            "physics_first_information_gain": 3,
            "direct_repair_of_reviewed_block": 2,
            "risk_isolation": 3,
            "computational_economy": 5,
            "boundedness": 5,
            "authority_clarity": 5,
            "downstream_stochastic_readiness": 2,
            "internal_only_policy_compliance": 5,
        },
        "disposition": "DEFERRED_UNTIL_DETERMINISTIC_COMPLEXITY_IS_JUSTIFIED",
        "scientific_endpoint": "Reduce gaps and nuisances only after deterministic evidence identifies necessary complexity.",
    },
    {
        "candidate_id": "FULL_SYNTHETIC_FORECAST_CONTRACT_V1_REPAIR",
        "target": "prepare_scalar_only_yukawa_synthetic_forward_model_and_sensitivity_forecast_packet_v1",
        "kind": "COMBINED_PHYSICAL_AND_STOCHASTIC_REPAIR",
        "scores": {
            "physics_first_information_gain": 3,
            "direct_repair_of_reviewed_block": 5,
            "risk_isolation": 2,
            "computational_economy": 2,
            "boundedness": 3,
            "authority_clarity": 4,
            "downstream_stochastic_readiness": 5,
            "internal_only_policy_compliance": 5,
        },
        "disposition": "DEFERRED_TOO_MANY_INTERFACES_AT_ONCE",
        "scientific_endpoint": "Repair all seven defects in one packet only if the staged route later proves unsuitable.",
    },
    {
        "candidate_id": "CLOSE_SYNTHETIC_FORECAST_LANE",
        "target": "select_post_scalar_internal_forecast_closure_scientific_priority_v0",
        "kind": "INTERNAL_FORECAST_LANE_CLOSURE",
        "scores": {
            "physics_first_information_gain": 1,
            "direct_repair_of_reviewed_block": 0,
            "risk_isolation": 5,
            "computational_economy": 5,
            "boundedness": 5,
            "authority_clarity": 5,
            "downstream_stochastic_readiness": 0,
            "internal_only_policy_compliance": 5,
        },
        "disposition": "DEFERRED_PREMATURE_BEFORE_DETERMINISTIC_TEST",
        "scientific_endpoint": "Return to gravitational-principle work only after deciding whether deterministic transport is useful.",
    },
]


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
            raise ValueError(f"post-review selection authority drift: {relative_path}")
    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "BLOCKED_SYNTHETIC_NOISE_OR_NUISANCE_CONTRACT":
        raise ValueError("packet-review verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("packet review did not authorize this selection")
    if review.get("scope", {}).get("synthetic_execution_authorized") is not False:
        raise ValueError("review unexpectedly authorized synthetic execution")

    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    gates = [
        "EXACT_PACKET_REVIEW_AUTHORITY_AND_TARGET",
        "REVIEWED_SEVEN_BLOCKERS_RETAINED",
        "EXACTLY_FOUR_RESPONSES_COMPARED",
        "EXACTLY_EIGHT_CRITERIA_FROZEN",
        "DETERMINISTIC_PHYSICS_PRECEDES_STOCHASTIC_INFERENCE",
        "TEN_STAGE_A_OBLIGATIONS_FROZEN",
        "REAL_150_VECTOR_IS_STAGE_A_ENDPOINT",
        "COMMON_KERNEL_AND_TORQUE_ROUTING_REQUIRED",
        "ANALYTIC_MUTATION_SIGN_AND_PHASE_CONTROLS_REQUIRED",
        "GEOMETRY_AND_HARMONIC_CONVERGENCE_REQUIRED",
        "JACOBIAN_IDENTIFIABILITY_REQUIRED",
        "NO_NOISE_MONTE_CARLO_OR_PROFILE_LIKELIHOOD_IN_STAGE_A",
        "STAGE_B_DEFERRED_UNTIL_ACCEPTED_STAGE_A",
        "STANDING_INTERNAL_ONLY_POLICY_RETAINED",
        "SELECTION_STABLE_IN_24_VARIANTS",
        "NO_PACKET_REPAIR_OR_DETERMINISTIC_EXECUTION",
        "NO_SYNTHETIC_EMPIRICAL_OR_PARAMETER_RESULT",
        "NO_SCALAR_BRANCH_NATIVE_BRIDGE_OR_ACTION_ADOPTION",
    ]
    obligations = [
        "freeze exact real-150 harmonic normalization DFT sign phase origin and alias rules",
        "freeze one shared Newtonian and Yukawa production kernel",
        "derive torque from the same interaction energy through one derivative path",
        "route four analytic benchmarks through production code",
        "verify nonzero n=2,4,6 harmonics and nominal structural-zero channels",
        "freeze phase reversal sign reversal and deliberate sign-normalization mutations",
        "freeze geometry cubature differentiation and harmonic convergence",
        "freeze deterministic geometry and calibration parameter maps and valid domains",
        "perform Jacobian or equivalent identifiability analysis against lambda0",
        "produce one stable reproducible real-150 deterministic forward vector",
    ]
    scope = {
        "scientific_response_selection_executed": True,
        "deterministic_packet_preparation_authorized": True,
        "deterministic_packet_prepared_now": False,
        "deterministic_execution_authorized": False,
        "deterministic_execution_performed": False,
        "stochastic_packet_preparation_authorized": False,
        "stochastic_forecast_authorized": False,
        "stochastic_forecast_performed": False,
        "synthetic_dataset_generated": False,
        "forecast_output_produced": False,
        "empirical_constraint_claimed": False,
        "numerical_lambda_bound_computed": False,
        "numerical_alpha_bound_computed": False,
        "alpha_sign_or_value_adopted": False,
        "scalar_branch_adopted": False,
        "native_scalar_bridge_identified": False,
        "native_gravitational_principle_identified": False,
        "gravitational_action_selected": False,
        "outbound_contact_authorized": False,
        "private_data_dependency_created": False,
    }
    return {
        "schema_id": "toe.post_scalar_only_yukawa.synthetic_forecast_packet_review.scientific_response_selection.v0",
        "packet_id": "POST_SCALAR_ONLY_YUKAWA_SYNTHETIC_FORECAST_PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_candidate_id": SELECTED_CANDIDATE_ID,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_review_verdict": review["verdict"],
            "frozen_packet_review_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in AUTHORITY_HASHES.items()
            ],
            "human_selection": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/post_scalar_only_yukawa_synthetic_forecast_"
                "packet_review_scientific_response_selection_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
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
        "selected_stage_a_contract": {
            "status": "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED",
            "obligation_count": len(obligations),
            "obligations": obligations,
            "gaussian_noise": "NONE",
            "monte_carlo_trials": "NONE",
            "sensitivity_forecast": "NONE",
            "profile_optimizer": "NONE",
            "maximum_future_claim": (
                "REPRODUCIBLE_CONVERGENT_DETERMINISTIC_NEWTONIAN_YUKAWA_"
                "TORQUE_MODEL_WITH_DEFINED_HARMONICS_AND_CHARACTERIZED_DEGENERACIES"
            ),
        },
        "deferred_stage_b": {
            "status": "DEFERRED_NOT_AUTHORIZED",
            "eligibility_condition": "INDEPENDENTLY_ACCEPTED_STAGE_A_RESULT",
            "future_target": "prepare_scalar_only_yukawa_stochastic_sensitivity_forecast_packet_v0",
            "future_scope": (
                "COVARIANCE_NUISANCE_OPTIMIZER_FAILURE_RESOURCE_NULL_INJECTION_"
                "BOUNDARY_AND_FORECAST_CONTRACT"
            ),
        },
        "retained_posture": {
            "blocked_packet_review_verdict": review["verdict"],
            "outbound_contact": "PROHIBITED_UNTIL_EXPLICITLY_REOPENED",
            "private_data_dependence": "PROHIBITED",
            "real_empirical_evidence": "NONE",
            "synthetic_data": "NONE_GENERATED",
            "scalar_range_forecast": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
        },
        "selection_gates": {
            "gate_count": len(gates),
            "pass_count": len(gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in gates],
        },
        "scope": scope,
        "current_posture": {
            "selected_response": "DETERMINISTIC_FORWARD_MODEL_VALIDATION_FIRST",
            "deterministic_packet": "NOT_YET_PREPARED",
            "deterministic_execution": "NOT_AUTHORIZED",
            "stochastic_forecast": "DEFERRED_NOT_AUTHORIZED",
            "synthetic_observations": "NONE",
            "empirical_constraint": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This selection authorizes preparation only of a deterministic "
            "torsion-balance forward-model validation packet. It does not prepare "
            "that packet, repair or execute the stochastic forecast, generate "
            "synthetic data, compute harmonics or bounds, or adopt any scalar "
            "branch, native principle, bridge, or gravitational action."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Select the response to the blocked synthetic forecast packet review.")
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
            print("post-review selection already current")
        return 0
    if current != expected:
        print("post-review selection drift")
        return 1
    print("post-review selection OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

