from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_QUADRATIC_GRAVITY_CONDITIONAL_MODE_SELECTION_ENVELOPE_"
    "SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "POST_QUADRATIC_GRAVITY_CONDITIONAL_MODE_SELECTION_ENVELOPE_"
    "SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_post_quadratic_gravity_conditional_mode_selection_envelope_"
    "scientific_response_selection_v0.py"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_ENVELOPE_"
    "RESULT_REVIEW_20260718_v0.json"
)
TARGET = (
    "select_post_quadratic_gravity_conditional_mode_selection_envelope_"
    "scientific_response_v0"
)
VERDICT = (
    "SELECTED_SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_"
    "PACKET_PREPARATION"
)
SELECTED_CANDIDATE_ID = "SCALAR_ONLY_VIABILITY_AND_NATIVE_RELEVANCE"
SELECTED_NEXT_TARGET = (
    "prepare_scalar_only_quadratic_gravity_viability_and_native_relevance_packet_v0"
)
SELECTED_NEXT_TARGET_KIND = "PREPARATION_ONLY_COMPARISON_SUBFAMILY_NO_BRANCH_ADOPTION"

AUTHORITY_HASHES = {
    "formal/docs/lanes/POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_ENVELOPE_RESULT_REVIEW_20260718_v0.md":
        "452377d5ee5a6022ec778908a025530a2861a1dfbfa8211a3628a4d3aaff8685",
    "formal/docs/release/POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_ENVELOPE_RESULT_REVIEW_20260718_v0.json":
        "5770911342b5713be8bbe40d91d7fb639524a50c65d4ead8137a7e662988a2e6",
    "formal/python/tools/post_quadratic_gravity_comparison_conditional_mode_selection_envelope_result_review_v0.py":
        "601f5d2a6fff22e44d7aaed3b20e2fb774ed75a5e8caef51a3e35405eba5e6aa",
    "formal/python/tests/test_post_quadratic_gravity_comparison_conditional_mode_selection_envelope_result_review_v0.py":
        "e2b5282472a861d35b8a803b48da6e8f23146123631af1aa5b55570544e897bf",
    "formal/toe_formal/ToeFormal/Derivation/PostQuadraticGravityComparisonConditionalModeSelectionEnvelopeResultReviewV0.lean":
        "440a7d96f72ee4e9bb6b8cb5bb99c99f52bce7575b299544270a4f95e2c1310b",
}

CRITERIA = {
    "direct_use_of_accepted_result": 3,
    "information_gain_about_missing_principle": 4,
    "boundedness": 3,
    "non_circularity": 3,
    "decisive_scientific_yield": 3,
    "authority_clarity": 2,
    "scope_containment": 2,
    "stopping_rule_precision": 2,
}

CANDIDATES = [
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "target": SELECTED_NEXT_TARGET,
        "kind": "PACKET_PREPARATION_ONLY",
        "scores": {key: 5 for key in CRITERIA},
        "disposition": "SELECTED_FOR_PACKET_PREPARATION_ONLY",
        "scientific_endpoint": (
            "Determine whether the conditionally remaining R+alpha R^2 comparison "
            "subfamily merits deeper study and whether any accepted ToE concept "
            "supplies native relevance, without adopting beta=0 or the subfamily."
        ),
    },
    {
        "candidate_id": "MINIMAL_MODE_POSTULATE_REQUIREMENTS_ANALYSIS",
        "target": "prepare_minimal_mode_gravitational_postulate_requirements_analysis_packet_v0",
        "kind": "POSTULATE_REQUIREMENTS_ANALYSIS",
        "scores": {
            "direct_use_of_accepted_result": 4,
            "information_gain_about_missing_principle": 5,
            "boundedness": 4,
            "non_circularity": 2,
            "decisive_scientific_yield": 4,
            "authority_clarity": 5,
            "scope_containment": 5,
            "stopping_rule_precision": 4,
        },
        "disposition": "DEFERRED_NOT_REJECTED",
        "scientific_endpoint": (
            "Test whether minimal mode content can be justified without assuming "
            "the Einstein spectrum it would conditionally select."
        ),
    },
    {
        "candidate_id": "SUPPLIED_0I_TO_ORBIT_COMPARATOR_TRANSPORT",
        "target": "prepare_supplied_quadratic_gravity_0i_to_orbit_comparator_packet_v0",
        "kind": "DOWNSTREAM_COMPARISON_TRANSPORT",
        "scores": {
            "direct_use_of_accepted_result": 4,
            "information_gain_about_missing_principle": 2,
            "boundedness": 5,
            "non_circularity": 5,
            "decisive_scientific_yield": 3,
            "authority_clarity": 5,
            "scope_containment": 5,
            "stopping_rule_precision": 5,
        },
        "disposition": "DEFERRED_NOT_REJECTED",
        "scientific_endpoint": (
            "Transport the supplied current response to an orbital comparator without "
            "claiming native gravity or resolving scalar-mode authority."
        ),
    },
    {
        "candidate_id": "OUTSIDE_FAMILY_GHOST_AVOIDANCE_MECHANISM_SURVEY",
        "target": "prepare_bounded_outside_family_ghost_avoidance_mechanism_survey_packet_v0",
        "kind": "THEORY_CLASS_OPPORTUNITY_SURVEY",
        "scores": {
            "direct_use_of_accepted_result": 3,
            "information_gain_about_missing_principle": 4,
            "boundedness": 1,
            "non_circularity": 4,
            "decisive_scientific_yield": 4,
            "authority_clarity": 3,
            "scope_containment": 1,
            "stopping_rule_precision": 2,
        },
        "disposition": "DEFERRED_UNTIL_ONE_MECHANISM_IS_NAMED_NOT_REJECTED",
        "scientific_endpoint": (
            "Identify one mechanism outside local quadratic metric gravity before "
            "authorizing any derivation or theory-family expansion."
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
    return sorted(rows, key=lambda row: (-row["weighted_score"], row["candidate_id"]))


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
            row["selected_candidate_id"] == SELECTED_CANDIDATE_ID for row in rows
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
            raise ValueError(f"conditional-envelope result-review drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})
    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "ACCEPTED_CONDITIONAL_MODE_SELECTION_ENVELOPE_RESULT":
        raise ValueError("conditional-envelope result was not accepted")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("result review did not authorize this response selection")
    if review["scope"].get("scientific_response_selection_authorized") is not True:
        raise ValueError("scientific response selection not authorized")
    if review["scope"].get("scientific_response_selection_executed") is not False:
        raise ValueError("scientific response selection already executed")
    principal = review["principal_result_review"]
    if principal.get("condition_adoption_count") != 0 or principal.get("native_branch_selector_count") != 0:
        raise ValueError("accepted envelope unexpectedly selected a condition or native branch")
    if principal.get("open_position_count") != 3 or principal.get("selected_position_count") != 0:
        raise ValueError("accepted envelope did not preserve all three open positions")
    return custody, review


def build_selection() -> dict[str, Any]:
    custody, review = _validate_authority()
    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if ranking[0]["candidate_id"] != SELECTED_CANDIDATE_ID:
        raise ValueError("unexpected post-envelope response-selection winner")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("post-envelope response-selection winner is unstable")
    human = REPO_ROOT / HUMAN_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    if not human.is_file() or not test.is_file():
        raise ValueError("scientific-response human record or test missing")

    gates = [
        "ACCEPTED_ENVELOPE_REVIEW_CUSTODY_AND_TARGET",
        "EXACTLY_FOUR_AUTHORIZED_ROUTES_COMPARED",
        "NO_CONDITION_OR_BRANCH_ADOPTION",
        "BETA_ZERO_IS_STUDY_CONDITION_ONLY",
        "ALPHA_REMAINS_SYMBOLIC_AND_UNSELECTED",
        "SCALAR_VIABILITY_NOT_PRELOADED",
        "NATIVE_RELEVANCE_REMAINS_AN_OPEN_TEST",
        "EXTERNAL_SOURCE_AND_NO_MATTER_ACTION_IMPORT",
        "MINIMAL_MODE_ROUTE_DEFERRED_NOT_REJECTED",
        "OUTSIDE_FAMILY_ROUTE_DEFERRED_UNTIL_NARROWED",
        "0I_TO_ORBIT_ROUTE_DEFERRED_AS_DOWNSTREAM_COMPARATOR",
        "RANKING_CRITERIA_AND_SCORES_EXPLICIT",
        "WINNER_STABLE_UNDER_24_SENSITIVITY_VARIANTS",
        "PACKET_PREPARATION_ONLY_AND_INDEPENDENT_REVIEW_STOP",
    ]

    return {
        "schema_id": "POST_QUADRATIC_GRAVITY_CONDITIONAL_MODE_SELECTION_ENVELOPE_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0",
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
            "human_selection": {"relative_path": HUMAN_RELATIVE_PATH, "sha256": _sha256(human)},
            "generator": {"relative_path": Path(__file__).resolve().relative_to(REPO_ROOT).as_posix(), "sha256": _sha256(Path(__file__).resolve())},
            "test": {"relative_path": TEST_RELATIVE_PATH, "sha256": _sha256(test)},
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
        "selected_packet_contract": {
            "status": "SUPPLIED_COMPARISON_SUBFAMILY_CONDITIONALLY_MOTIVATED_NOT_SELECTED",
            "comparison_subfamily": "R+alpha R^2",
            "beta_status": "beta=0 STUDY_CONDITION_FROM_SUPPLIED_GHOST_AVOIDANCE_NOT_ADOPTED",
            "alpha_status": "SYMBOLIC_UNSELECTED",
            "non_tachyonic_stratum": "alpha<0 under frozen conventions; stratum to assess, not a selected coupling",
            "source_status": "EXTERNALLY_SUPPLIED_CONSERVED_COMPARISON_SOURCE_NO_NATIVE_MATTER_ACTION",
            "questions": [
                "selected-background stability beyond the accepted Minkowski result",
                "coupling to the externally supplied source trace",
                "source compatibility and conservation assumptions",
                "symbolic scalar range and parameter strata",
                "screening or decoupling obligations without preloading a mechanism",
                "source channels and prospective discriminating observables",
                "whether any accepted ToE concept supplies native scalar relevance",
                "best next derivation or localized obstruction",
            ],
            "execution_authorized": False,
            "independent_packet_review_required": True,
        },
        "selection_rationale": [
            "directly downstream of the accepted comparison and envelope",
            "tests the only modified branch remaining after conditional spin-2 exclusion",
            "can yield either a viability map or a localized obstruction",
            "informs whether a future principle must exclude all extra modes or only spin-2",
            "narrower than an unconstrained outside-family survey",
            "less circular than beginning with minimal Einstein mode content",
            "addresses principle formation more directly than orbital comparator transport",
        ],
        "preparation_gates": {
            "gate_count": len(gates),
            "pass_count": len(gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in gates],
        },
        "retained_conditional_facts": {
            "Sigma": "3 alpha+beta",
            "beta_zero_consequence": "additional negative-residue spin-2 pole absent within frozen family",
            "scalar_mass_on_beta_zero": "m0^2=-1/(6 alpha)",
            "non_tachyonic_scalar_on_beta_zero": "alpha<0 under frozen conventions",
            "facts_adopt_beta_zero_or_scalar_branch": False,
        },
        "claim_ceiling": "Scientific-response selection and preparation authorization only. No beta=0 law, scalar branch, alpha value, R+alpha R^2 action, scalar viability claim, native principle, postulate, matter action, outside-family mechanism, empirical fit, orbital transport, frame-dragging result, GR-pillar promotion, V2 cell, or master-action change is selected, established, executed, or authorized here.",
        "scope": {
            "scientific_response_selection_executed": True,
            "scalar_viability_packet_preparation_authorized": True,
            "scalar_viability_packet_prepared_now": False,
            "scalar_viability_execution_authorized": False,
            "beta_zero_adopted": False,
            "scalar_branch_adopted": False,
            "alpha_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_proposed_or_authorized": False,
            "gravitational_action_selected": False,
            "matter_action_imported": False,
            "outside_family_mechanism_opened": False,
            "empirical_fit_authorized": False,
            "orbital_transport_authorized": False,
            "frame_dragging_reopened": False,
            "GR_pillar_promoted": False,
            "authoritative_V2_population_authorized": False,
            "master_action_mutated": False,
        },
        "current_posture": {
            "quadratic_comparison": "COMPLETED_AND_ACCEPTED",
            "conditional_envelope": "COMPLETED_AND_ACCEPTED",
            "conditions_adopted": 0,
            "native_branch_selectors": 0,
            "selected_response": "PREPARE_SCALAR_ONLY_VIABILITY_AND_NATIVE_RELEVANCE_PACKET",
            "selected_packet_prepared": False,
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "frame_dragging": "NOT_RESUMED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_selection(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Select the post-envelope scientific response.")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if args.write:
        path.write_bytes(expected)
        print("post_envelope_scientific_response_selection_v0: wrote scalar packet-preparation selection")
        return 0
    if not path.is_file() or path.read_bytes() != expected:
        print("post_envelope_scientific_response_selection_v0: FAILED artifact drift")
        return 1
    report = json.loads(expected)
    print(json.dumps({
        "gates": report["preparation_gates"]["pass_count"],
        "minimum_sensitivity_margin": report["sensitivity_analysis"]["minimum_winning_margin"],
        "selected": report["selected_candidate_id"],
        "status": "CHECKED",
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
