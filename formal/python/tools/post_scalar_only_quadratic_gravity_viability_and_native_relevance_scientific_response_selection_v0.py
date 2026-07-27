from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_"
    "SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "POST_SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_"
    "SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_post_scalar_only_quadratic_gravity_viability_and_native_relevance_"
    "scientific_response_selection_v0.py"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_"
    "RESULT_REVIEW_20260718_v0.json"
)
TARGET = (
    "select_post_scalar_only_quadratic_gravity_viability_and_native_"
    "relevance_scientific_response_v0"
)
VERDICT = (
    "SELECTED_SCALAR_ONLY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_PREPARATION"
)
SELECTED_CANDIDATE_ID = "BOUND_SCALAR_ONLY_RANGE_AND_WEAK_FIELD_PHENOMENOLOGY"
SELECTED_NEXT_TARGET = (
    "prepare_scalar_only_quadratic_gravity_range_and_weak_field_constraint_"
    "packet_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "PREPARATION_ONLY_COMPARISON_PHENOMENOLOGY_NO_PARAMETER_OR_ACTION_SELECTION"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_RESULT_REVIEW_20260718_v0.md":
        "83251dcff6410749736a353bc1798fea57ce889b019b8dcedb44fa9517e9dc26",
    REVIEW_RELATIVE_PATH:
        "278c9ad0d765891c92b6bfca2c5d50993c3d9ecee200657f44ac772d3f5057e9",
    "formal/python/tools/scalar_only_quadratic_gravity_viability_and_native_relevance_result_review_v0.py":
        "66d09b7cc3ce2443f32c5b019575d5a34fe4872bf90c06ef7d46e412a6dd7fee",
    "formal/python/tests/test_scalar_only_quadratic_gravity_viability_and_native_relevance_result_review_v0.py":
        "436a0895111d8874951555ab02d3e4844e5f248b193bad031a0576f4fbaeb7ff",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyQuadraticGravityViabilityAndNativeRelevanceResultReviewV0.lean":
        "346e9c42238e7ff741afb4d8b9ab00bac060fad337e643aee7a43efc765701e8",
}

CRITERIA = {
    "direct_use_of_accepted_scalar_result": 4,
    "immediate_empirical_discriminability": 4,
    "information_gain_about_branch_viability": 4,
    "information_gain_about_missing_native_principle": 3,
    "boundedness": 3,
    "non_circularity": 3,
    "authority_clarity": 2,
    "stopping_rule_precision": 2,
}

CANDIDATES = [
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "target": SELECTED_NEXT_TARGET,
        "kind": "COMPARISON_PHENOMENOLOGY_PACKET_PREPARATION_ONLY",
        "scores": {
            "direct_use_of_accepted_scalar_result": 5,
            "immediate_empirical_discriminability": 5,
            "information_gain_about_branch_viability": 5,
            "information_gain_about_missing_native_principle": 3,
            "boundedness": 5,
            "non_circularity": 5,
            "authority_clarity": 5,
            "stopping_rule_precision": 5,
        },
        "disposition": "SELECTED_FOR_PACKET_PREPARATION_ONLY",
        "scientific_endpoint": (
            "Determine whether the fixed-strength finite-range scalar response "
            "has a bounded observationally allowed comparison region, without "
            "selecting alpha or adopting the branch."
        ),
    },
    {
        "candidate_id": "SUPPLIED_0I_TO_ORBIT_COMPARATOR",
        "target": "prepare_supplied_scalar_comparison_0i_to_orbit_packet_v0",
        "kind": "DOWNSTREAM_COMPARISON_TRANSPORT",
        "scores": {
            "direct_use_of_accepted_scalar_result": 4,
            "immediate_empirical_discriminability": 4,
            "information_gain_about_branch_viability": 3,
            "information_gain_about_missing_native_principle": 1,
            "boundedness": 5,
            "non_circularity": 5,
            "authority_clarity": 5,
            "stopping_rule_precision": 5,
        },
        "disposition": "DEFERRED_NOT_REJECTED",
        "scientific_endpoint": (
            "Complete supplied metric-to-orbit transport while retaining the "
            "accepted absence of a direct scalar stationary 0i correction."
        ),
    },
    {
        "candidate_id": "NATIVE_SCALAR_POSTULATE_REQUIREMENTS",
        "target": "prepare_native_gravitational_scalar_postulate_requirements_packet_v0",
        "kind": "NATIVE_PRINCIPLE_REQUIREMENTS_ANALYSIS",
        "scores": {
            "direct_use_of_accepted_scalar_result": 4,
            "immediate_empirical_discriminability": 1,
            "information_gain_about_branch_viability": 2,
            "information_gain_about_missing_native_principle": 5,
            "boundedness": 4,
            "non_circularity": 3,
            "authority_clarity": 5,
            "stopping_rule_precision": 4,
        },
        "disposition": "DEFERRED_NOT_REJECTED",
        "scientific_endpoint": (
            "Determine what explanatory and falsifiable obligations a genuine "
            "ToE-native scalar postulate would need to satisfy."
        ),
    },
    {
        "candidate_id": "MINIMAL_MODE_REQUIREMENTS",
        "target": "prepare_minimal_mode_gravitational_requirements_packet_v0",
        "kind": "MINIMAL_SPECTRUM_REQUIREMENTS_ANALYSIS",
        "scores": {
            "direct_use_of_accepted_scalar_result": 3,
            "immediate_empirical_discriminability": 1,
            "information_gain_about_branch_viability": 2,
            "information_gain_about_missing_native_principle": 5,
            "boundedness": 4,
            "non_circularity": 2,
            "authority_clarity": 5,
            "stopping_rule_precision": 4,
        },
        "disposition": "DEFERRED_NOT_REJECTED",
        "scientific_endpoint": (
            "Test whether minimal gravitational mode content can be justified "
            "without assuming the Einstein spectrum it would select."
        ),
    },
]


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _weighted_score(scores: dict[str, int], weights: dict[str, int]) -> int:
    if set(scores) != set(weights):
        raise ValueError("candidate score criteria mismatch")
    if any(score < 0 or score > 5 for score in scores.values()):
        raise ValueError("candidate score outside 0..5")
    return sum(scores[key] * weights[key] for key in weights)


def _rank(weights: dict[str, int]) -> list[dict[str, Any]]:
    rows = []
    for candidate in CANDIDATES:
        row = dict(candidate)
        row["weighted_score"] = _weighted_score(candidate["scores"], weights)
        rows.append(row)
    return sorted(
        rows, key=lambda row: (-row["weighted_score"], row["candidate_id"])
    )


def _sensitivity() -> dict[str, Any]:
    rows = []
    for omitted in CRITERIA:
        weights = dict(CRITERIA)
        weights[omitted] = 0
        ranking = _rank(weights)
        rows.append({
            "variant": f"omit_{omitted}",
            "selected_candidate_id": ranking[0]["candidate_id"],
            "selected_score": ranking[0]["weighted_score"],
            "runner_up_candidate_id": ranking[1]["candidate_id"],
            "runner_up_score": ranking[1]["weighted_score"],
        })
    for criterion, baseline in CRITERIA.items():
        for delta in (-1, 1):
            weights = dict(CRITERIA)
            weights[criterion] = max(1, baseline + delta)
            ranking = _rank(weights)
            rows.append({
                "variant": f"{criterion}_{delta:+d}",
                "selected_candidate_id": ranking[0]["candidate_id"],
                "selected_score": ranking[0]["weighted_score"],
                "runner_up_candidate_id": ranking[1]["candidate_id"],
                "runner_up_score": ranking[1]["weighted_score"],
            })
    return {
        "variant_count": len(rows),
        "rows": rows,
        "selected_candidate_stable_in_all_variants": all(
            row["selected_candidate_id"] == SELECTED_CANDIDATE_ID
            for row in rows
        ),
        "minimum_winning_margin": min(
            row["selected_score"] - row["runner_up_score"] for row in rows
        ),
    }


def _validate_authority() -> tuple[list[dict[str, str]], dict[str, Any]]:
    custody = []
    for relative_path, expected in AUTHORITY_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"scalar-only result-review drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})
    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "ACCEPTED_BOUNDED_SCALAR_ONLY_COMPARISON_RESULT":
        raise ValueError("scalar-only result was not accepted")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("result review did not authorize this selector")
    scope = review["scope"]
    if scope.get("scientific_response_selection_authorized") is not True:
        raise ValueError("scientific response selection is not authorized")
    if scope.get("scientific_response_selection_executed") is not False:
        raise ValueError("scientific response selection was already executed")
    claim = review["accepted_bounded_claim"]
    if claim.get("native_bridge_count") != 0:
        raise ValueError("accepted result unexpectedly identifies a native bridge")
    if any(scope[key] for key in (
        "beta_zero_adopted",
        "alpha_sign_or_value_adopted",
        "scalar_branch_adopted",
        "gravitational_action_selected",
    )):
        raise ValueError("accepted result unexpectedly adopted a branch or action")
    return custody, review


def build_selection() -> dict[str, Any]:
    custody, review = _validate_authority()
    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if ranking[0]["candidate_id"] != SELECTED_CANDIDATE_ID:
        raise ValueError("unexpected post-scalar response-selection winner")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("post-scalar response-selection winner is unstable")
    human = REPO_ROOT / HUMAN_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    if not human.is_file() or not test.is_file():
        raise ValueError("selection human record or focused test missing")

    gates = [
        "ACCEPTED_SCALAR_RESULT_CUSTODY_AND_TARGET",
        "EXACTLY_FOUR_AUTHORIZED_ROUTES_COMPARED",
        "BOUNDED_VIABILITY_AND_ZERO_NATIVE_BRIDGES_RETAINED",
        "NO_BETA_ALPHA_BRANCH_OR_ACTION_ADOPTION",
        "PHENOMENOLOGY_REMAINS_COMPARISON_ONLY",
        "YUKAWA_RANGE_MAP_RETAINED_WITHOUT_PARAMETER_SELECTION",
        "NO_SCREENING_OR_EMPIRICAL_RESULT_PRELOADED",
        "NO_DATASET_OR_NUMERICAL_BOUND_SELECTED",
        "AT_MOST_TWO_OBSERVABLE_CLASSES_IN_FUTURE_PACKET",
        "SOURCE_UNITS_UNCERTAINTY_AND_COVARIANCE_OBLIGATIONS",
        "OTHER_THREE_ROUTES_DEFERRED_NOT_REJECTED",
        "RANKING_CRITERIA_AND_SCORES_EXPLICIT",
        "WINNER_STABLE_UNDER_24_SENSITIVITY_VARIANTS",
        "PACKET_PREPARATION_ONLY_WITH_INDEPENDENT_REVIEW_STOP",
    ]

    return {
        "schema_id": (
            "POST_SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_"
            "RELEVANCE_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_candidate_id": SELECTED_CANDIDATE_ID,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_result_review_verdict": review["verdict"],
            "consumed_review_gate_count": review["review_gates"]["pass_count"],
            "frozen_result_review_artifacts": custody,
            "human_selection": {
                "relative_path": HUMAN_RELATIVE_PATH,
                "sha256": _sha256(human),
            },
            "generator": {
                "relative_path": Path(__file__).resolve().relative_to(
                    REPO_ROOT
                ).as_posix(),
                "sha256": _sha256(Path(__file__).resolve()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test),
            },
        },
        "selection_policy": {
            "criterion_scale": "0..5_RESEARCH_PRIORITY_NOT_TRUTH_PROBABILITY",
            "weights": CRITERIA,
            "criterion_count": len(CRITERIA),
            "candidate_count": len(CANDIDATES),
            "maximum_weighted_score": 5 * sum(CRITERIA.values()),
        },
        "ranking": {
            "rows": ranking,
            "selected_candidate_id": ranking[0]["candidate_id"],
            "selected_score": ranking[0]["weighted_score"],
            "runner_up_candidate_id": ranking[1]["candidate_id"],
            "runner_up_score": ranking[1]["weighted_score"],
        },
        "sensitivity_analysis": sensitivity,
        "retained_scalar_comparison": {
            "status": "SUPPLIED_COMPARISON_SUBFAMILY_NOT_ADOPTED",
            "mass_squared": "m0^2=-1/(6 alpha)",
            "packet_non_tachyonic_stratum": "alpha<0 NOT_SELECTED",
            "range": "lambda0=1/m0=sqrt(-6 alpha)",
            "stationary_point_source_response": (
                "h00=-(2GM/(c^2 r))[1+(1/3)exp(-r/lambda0)]"
            ),
            "Yukawa_relative_strength": "1/3 IN_FROZEN_POINT_SOURCE_MODEL",
            "intrinsic_environmental_screening": "NOT_IDENTIFIED",
            "native_scalar_bridge_count": 0,
        },
        "selected_packet_contract": {
            "status": "COMPARISON_PHENOMENOLOGY_PREPARATION_ONLY",
            "observable_class_cap": 2,
            "candidate_observable_classes_not_yet_selected": [
                "INVERSE_SQUARE_OR_FIFTH_FORCE_RANGE_TEST",
                "SOLAR_SYSTEM_WEAK_FIELD_TEST",
            ],
            "required_obligations": [
                "exact alpha-mass-range and SI convention map",
                "accepted Yukawa coefficient and source-domain verification",
                "at most two independent observable classes",
                "primary-source data identity and custody",
                "units uncertainties nuisance parameters and covariance",
                "likelihood or exclusion rule frozen before execution",
                "Einstein and infinite-mass controls",
                "one bounded execution followed by independent result review",
            ],
            "dataset_selected_now": False,
            "numerical_alpha_or_mass_bound_computed_now": False,
            "execution_authorized": False,
            "independent_packet_review_required": True,
        },
        "selection_rationale": [
            "directly tests the accepted unscreened finite-range scalar response",
            "uses an exact mass-range map without selecting alpha",
            "can determine whether the comparison branch has meaningful empirical room",
            "produces a bounded constraint rather than a native theory claim",
            "precedes postulate design with empirical exposure",
            "is more scalar-relevant than stationary 0i orbital transport at accepted order",
        ],
        "preparation_gates": {
            "gate_count": len(gates),
            "pass_count": len(gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in gates],
        },
        "post_selection_oracles": [
            {
                "source": "https://arxiv.org/abs/0805.1726",
                "role": "METRIC_F_R_VIABILITY_AND_CONSTRAINT_ORACLE",
            },
            {
                "source": "https://arxiv.org/abs/1002.4928",
                "role": "LOCAL_GRAVITY_AND_SCREENING_ORACLE",
            },
            {
                "source": "https://arxiv.org/abs/2305.06752",
                "role": "PROSPECTIVE_SOLAR_SYSTEM_YUKAWA_OBSERVABLE_ORACLE",
            },
        ],
        "claim_ceiling": (
            "Scientific-response selection and packet-preparation authorization "
            "only. No beta=0 law, alpha value or bound, scalar branch, R+alpha "
            "R^2 action, native scalar bridge, native principle, matter sector, "
            "dataset, empirical result, minimal-mode condition, orbital result, "
            "frame-dragging result, V2 cell, or master-action change is selected, "
            "computed, established, or authorized here."
        ),
        "scope": {
            "scientific_response_selection_executed": True,
            "range_and_weak_field_packet_preparation_authorized": True,
            "range_and_weak_field_packet_prepared_now": False,
            "phenomenology_execution_authorized": False,
            "dataset_selected": False,
            "numerical_bound_computed": False,
            "beta_zero_adopted": False,
            "alpha_selected": False,
            "scalar_branch_adopted": False,
            "native_scalar_bridge_identified": False,
            "native_gravitational_principle_identified": False,
            "gravitational_action_selected": False,
            "matter_sector_selected": False,
            "new_postulate_proposed_or_authorized": False,
            "minimal_mode_condition_adopted": False,
            "orbital_transport_authorized": False,
            "frame_dragging_reopened": False,
            "authoritative_V2_population_authorized": False,
            "master_action_mutated": False,
        },
        "current_posture": {
            "scalar_only_result": "COMPLETED_AND_ACCEPTED",
            "native_scalar_bridges": 0,
            "selected_response": (
                "PREPARE_SCALAR_ONLY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET"
            ),
            "selected_packet_prepared": False,
            "beta_zero": "COMPARISON_RESTRICTION_ONLY",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_selection(), indent=2, sort_keys=True) + "\n").encode(
        "utf-8"
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Select the post-scalar-only scientific response."
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if args.write:
        path.write_bytes(expected)
        print("post_scalar_scientific_response_selection_v0: wrote selection")
        return 0
    if not path.is_file() or path.read_bytes() != expected:
        print("post_scalar_scientific_response_selection_v0: FAILED artifact drift")
        return 1
    report = json.loads(expected)
    print(json.dumps({
        "gates": report["preparation_gates"]["pass_count"],
        "minimum_sensitivity_margin": report["sensitivity_analysis"][
            "minimum_winning_margin"
        ],
        "selected": report["selected_candidate_id"],
        "status": "CHECKED",
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
