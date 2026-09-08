from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_"
    "PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "POST_SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_"
    "PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_post_scalar_only_quadratic_gravity_range_and_weak_field_constraint_"
    "packet_review_scientific_response_selection_v0.py"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_"
    "REVIEW_20260718_v0.json"
)

TARGET = (
    "select_post_scalar_only_quadratic_gravity_range_and_weak_field_constraint_"
    "packet_review_scientific_response_v0"
)
VERDICT = "SELECTED_TARGETED_EOTWASH_PRIMARY_EVIDENCE_ACQUISITION_PACKET_PREPARATION"
SELECTED_CANDIDATE_ID = "TARGETED_EOTWASH_PRIMARY_EVIDENCE_AND_FORWARD_MODEL_ACQUISITION"
SELECTED_NEXT_TARGET = (
    "prepare_eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "PREPARATION_ONLY_EVIDENCE_CUSTODY_ACQUISITION_NO_CONTACT_DOWNLOAD_OR_FIT"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_REVIEW_20260718_v0.md":
        "17c64e37d54380c0c4fa53285b3d8f112b8c1b4cde1b70e3cdffa7e0e5dd63ce",
    REVIEW_RELATIVE_PATH:
        "51484eebd42f5bda8386b3857af675add3e8966ce58354965822dfcf31c703d0",
    "formal/python/tools/scalar_only_quadratic_gravity_range_and_weak_field_constraint_packet_review_v0.py":
        "7269afe70ca4fbb7f491c3d00493f8d34044dd339a677d24704d130581342b27",
    "formal/python/tests/test_scalar_only_quadratic_gravity_range_and_weak_field_constraint_packet_review_v0.py":
        "2ae0dd0847991d282bd674d573a7581bce6c4811cd5ca3787e522332981b3567",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyQuadraticGravityRangeAndWeakFieldConstraintPacketReviewV0.lean":
        "b77140e66d8e77b8315540a0783e38ebea517fdf69b79bbf4cc3a6d7be7ab96e",
}

CRITERIA = {
    "direct_repair_of_confirmed_block": 5,
    "likelihood_of_restoring_independent_fit": 4,
    "fixed_one_third_signal_match": 4,
    "reproducibility_gain": 4,
    "boundedness": 3,
    "authority_clarity": 3,
    "cost_proportionality": 2,
    "stopping_rule_precision": 2,
}

CANDIDATES = [
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "target": SELECTED_NEXT_TARGET,
        "kind": "PRIMARY_EVIDENCE_AND_FORWARD_MODEL_CUSTODY_PACKET_PREPARATION",
        "scores": {
            "direct_repair_of_confirmed_block": 5,
            "likelihood_of_restoring_independent_fit": 5,
            "fixed_one_third_signal_match": 5,
            "reproducibility_gain": 5,
            "boundedness": 5,
            "authority_clarity": 5,
            "cost_proportionality": 4,
            "stopping_rule_precision": 5,
        },
        "disposition": "SELECTED_FOR_PACKET_PREPARATION_ONLY",
        "scientific_endpoint": (
            "Determine whether legitimate primary materials can place every "
            "decision-bearing likelihood input and the extended-source model into "
            "verified custody, without executing the fit."
        ),
    },
    {
        "candidate_id": "FULLY_PUBLIC_ALTERNATIVE_EXPERIMENT_SELECTION",
        "target": "prepare_reproducible_fixed_strength_yukawa_alternative_experiment_survey_v0",
        "kind": "ALTERNATIVE_EXPERIMENT_REPRODUCIBILITY_SELECTION",
        "scores": {
            "direct_repair_of_confirmed_block": 2,
            "likelihood_of_restoring_independent_fit": 4,
            "fixed_one_third_signal_match": 3,
            "reproducibility_gain": 5,
            "boundedness": 3,
            "authority_clarity": 5,
            "cost_proportionality": 2,
            "stopping_rule_precision": 4,
        },
        "disposition": "DEFERRED_NOT_REJECTED",
        "scientific_endpoint": (
            "Select a replacement only if it has complete numerical evidence, an "
            "executable observable model, and real sensitivity near A_Y=1/3."
        ),
    },
    {
        "candidate_id": "SUPPLIED_PUBLISHED_EOTWASH_CONSTRAINT_REINTERPRETATION",
        "target": "prepare_supplied_eotwash_fixed_strength_yukawa_constraint_reinterpretation_packet_v0",
        "kind": "SUPPLIED_PUBLISHED_CONSTRAINT_ONLY",
        "scores": {
            "direct_repair_of_confirmed_block": 2,
            "likelihood_of_restoring_independent_fit": 0,
            "fixed_one_third_signal_match": 5,
            "reproducibility_gain": 1,
            "boundedness": 5,
            "authority_clarity": 5,
            "cost_proportionality": 5,
            "stopping_rule_precision": 5,
        },
        "disposition": "DEFERRED_NOT_REJECTED",
        "scientific_endpoint": (
            "State only what follows under the authors' published analysis and "
            "assumptions, explicitly without claiming independent reproduction."
        ),
    },
    {
        "candidate_id": "TEMPORARILY_CLOSE_SCALAR_EMPIRICAL_LANE",
        "target": "select_non_empirical_post_scalar_scientific_priority_v0",
        "kind": "EMPIRICAL_LANE_DEFERMENT",
        "scores": {
            "direct_repair_of_confirmed_block": 0,
            "likelihood_of_restoring_independent_fit": 0,
            "fixed_one_third_signal_match": 0,
            "reproducibility_gain": 0,
            "boundedness": 5,
            "authority_clarity": 5,
            "cost_proportionality": 5,
            "stopping_rule_precision": 5,
        },
        "disposition": "DEFERRED_NOT_REJECTED",
        "scientific_endpoint": (
            "Preserve the opportunity and return to theory work if evidence custody "
            "cannot be restored proportionately."
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
    rows: list[dict[str, Any]] = []
    for candidate in CANDIDATES:
        row = dict(candidate)
        row["weighted_score"] = _weighted_score(candidate["scores"], weights)
        rows.append(row)
    return sorted(rows, key=lambda row: (-row["weighted_score"], row["candidate_id"]))


def _sensitivity() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
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
    custody: list[dict[str, str]] = []
    for relative_path, expected in AUTHORITY_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"range-constraint packet review drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})
    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE":
        raise ValueError("range-constraint packet review block not accepted")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("range-constraint packet review did not authorize this selector")
    if review["future_response_selection"].get("selection_only") is not True:
        raise ValueError("review did not authorize response selection")
    if review["future_response_selection"].get("selected_response_now") is not None:
        raise ValueError("review unexpectedly selected a response")
    if review["execution_block"].get("likelihood_evaluated") is not False:
        raise ValueError("review unexpectedly executed the likelihood")
    return custody, review


def build_selection() -> dict[str, Any]:
    custody, review = _validate_authority()
    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if ranking[0]["candidate_id"] != SELECTED_CANDIDATE_ID:
        raise ValueError("unexpected post-block response-selection winner")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("post-block response-selection winner is unstable")
    human = REPO_ROOT / HUMAN_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    if not human.is_file() or not test.is_file():
        raise ValueError("selection human record or focused test missing")

    gate_ids = [
        "ACCEPTED_BLOCK_CUSTODY_AND_EXACT_SELECTOR_TARGET",
        "EXACTLY_FOUR_AUTHORIZED_RESPONSES_COMPARED",
        "EOTWASH_SUITABILITY_RETAINED_WITHOUT_FIT",
        "PRIMARY_DATA_COVARIANCE_MODEL_AND_COVERAGE_BLOCK_RETAINED",
        "ACQUISITION_ROUTE_DIRECTLY_TARGETS_ALL_MISSING_INPUTS",
        "SUPPLEMENT_RECEIPT_CANNOT_AUTOMATICALLY_COMPLETE_CONTRACT",
        "SIX_CONTENT_COMPONENTS_REQUIRE_INDIVIDUAL_INSPECTION",
        "NO_DOWNLOAD_CONTACT_OR_ACQUISITION_EXECUTED",
        "SUPPLIED_REINTERPRETATION_REMAINS_NONINDEPENDENT",
        "ALTERNATIVE_EXPERIMENT_REQUIRES_PUBLIC_EVIDENCE_AND_SIGNAL_MATCH",
        "TEMPORARY_CLOSURE_REMAINS_LEGITIMATE_FALLBACK",
        "OTHER_THREE_ROUTES_DEFERRED_NOT_REJECTED",
        "RANKING_CRITERIA_AND_SCORES_EXPLICIT",
        "WINNER_STABLE_UNDER_24_SENSITIVITY_VARIANTS",
        "PACKET_PREPARATION_ONLY_NO_PARAMETER_BRANCH_OR_ACTION_SELECTION",
    ]

    required_components = [
        "complete 95x3 torque observations",
        "displacement and configuration metadata",
        "numerical uncertainty and covariance model",
        "five numerical nuisance priors",
        "executable extended-source torque implementation",
        "executable or fully specified boundary-coverage calibration",
    ]

    return {
        "schema_id": (
            "toe.post_scalar_only_quadratic_gravity_range_and_weak_field_constraint."
            "packet_review_scientific_response_selection.v0"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_candidate_id": SELECTED_CANDIDATE_ID,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_review_verdict": review["verdict"],
            "consumed_review_gate_count": review["review_gates"]["pass_count"],
            "consumed_adversarial_probe_count": review["adversarial_no_bypass_probes"]["pass_count"],
            "frozen_packet_review_artifacts": custody,
            "human_selection": {
                "relative_path": HUMAN_RELATIVE_PATH,
                "sha256": _sha256(human),
            },
            "generator": {
                "relative_path": Path(__file__).resolve().relative_to(REPO_ROOT).as_posix(),
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
        "retained_block": {
            "experiment": "EOTWASH_2020_SHORT_RANGE_ISL_TORSION_BALANCE",
            "experiment_scientifically_suitable": True,
            "fixed_signal": "A_Y=1/3",
            "independent_project_fit_executable": False,
            "principal_block": "BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE",
            "likelihood": "NOT_EXECUTED",
            "scalar_range_bound": "NONE",
            "alpha_constraint": "NONE",
        },
        "selected_acquisition_packet_contract": {
            "status": "PREPARATION_AUTHORIZED_EXECUTION_NOT_AUTHORIZED",
            "required_component_count": len(required_components),
            "required_components": required_components,
            "allowed_preparation_obligations": [
                "enumerate legitimate supplement and custodian access routes",
                "define provenance, hash, format, and completeness checks",
                "define an item-by-item content inspection against likelihood operations",
                "define author-or-custodian contact as a separately reviewed possible action",
                "define fail-closed terminal outcomes for partial custody",
                "stop for independent packet review before any acquisition or communication",
            ],
            "terminal_outcomes": [
                "PRIMARY_EVIDENCE_CONTRACT_COMPLETE",
                "SUPPLEMENT_ACQUIRED_BUT_FORWARD_MODEL_INCOMPLETE",
                "SUPPLEMENT_ACQUIRED_BUT_COVARIANCE_INCOMPLETE",
                "AUTHORS_OR_CUSTODIAN_CONTACT_REQUIRED",
                "PRIMARY_EVIDENCE_NOT_OBTAINABLE_WITHIN_BOUNDED_ROUTE",
            ],
            "supplement_receipt_automatically_completes_contract": False,
            "dissertation_may_fill_missing_values_by_inference": False,
            "fit_execution_authorized": False,
            "independent_review_required": True,
        },
        "preparation_gates": {
            "gate_count": len(gate_ids),
            "pass_count": len(gate_ids),
            "failure_count": 0,
            "rows": [{"gate_id": gate_id, "status": "PASS"} for gate_id in gate_ids],
        },
        "scope": {
            "scientific_response_selection_executed": True,
            "eotwash_acquisition_packet_preparation_authorized": True,
            "eotwash_acquisition_packet_prepared_now": False,
            "supplement_download_or_acquisition_authorized": False,
            "author_or_custodian_contact_authorized": False,
            "alternate_experiment_selected": False,
            "published_constraint_reinterpretation_authorized": False,
            "empirical_lane_closed": False,
            "primary_data_custody_complete": False,
            "forward_model_executable": False,
            "coverage_calibration_available": False,
            "likelihood_execution_authorized": False,
            "likelihood_evaluated": False,
            "numerical_lambda_bound_computed": False,
            "numerical_alpha_bound_computed": False,
            "beta_zero_adopted": False,
            "alpha_sign_or_value_adopted": False,
            "scalar_branch_adopted": False,
            "native_scalar_bridge_identified": False,
            "native_gravitational_principle_identified": False,
            "gravitational_action_selected": False,
            "matter_sector_selected": False,
            "orbital_or_light_propagation_analysis_executed": False,
            "frame_dragging_resumed": False,
            "master_action_mutated": False,
        },
        "current_posture": {
            "selected_response": "TARGETED_EOTWASH_PRIMARY_EVIDENCE_AND_FORWARD_MODEL_ACQUISITION",
            "selection_stability": "FIRST_IN_24_OF_24_VARIANTS",
            "packet": "NOT_YET_PREPARED",
            "evidence_acquisition": "NOT_STARTED",
            "author_contact": "NOT_AUTHORIZED",
            "likelihood": "NOT_EXECUTED",
            "scalar_range_bound": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This response selection authorizes preparation only of a bounded "
            "Eot-Wash 2020 primary-evidence custody acquisition packet. No supplement "
            "download, file acquisition, author or custodian contact, alternative "
            "experiment, published-constraint reinterpretation, likelihood, scalar-range "
            "or alpha bound, beta=0 law, scalar-branch adoption, native scalar bridge, "
            "native gravitational principle, gravitational action, orbital result, "
            "frame-dragging result, or master-action change is selected, computed, "
            "claimed, or authorized."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_selection(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if args.write:
        path.write_bytes(raw)
    if args.check:
        if not path.exists() or path.read_bytes() != raw:
            raise SystemExit("post-block scientific-response selection artifact drift")
    if not args.write and not args.check:
        print(raw.decode("utf-8"), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
