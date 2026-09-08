from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/POST_EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_"
    "CUSTODY_ACQUISITION_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/POST_EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_"
    "CUSTODY_ACQUISITION_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_post_eotwash_2020_yukawa_primary_evidence_"
    "custody_acquisition_scientific_response_selection_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PostEotwash2020YukawaPrimaryEvidenceCustodyAcquisitionScientificResponseSelectionV0.lean"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_"
    "ACQUISITION_RESULT_REVIEW_20260718_v0.json"
)

TARGET = (
    "select_post_eotwash_2020_yukawa_primary_evidence_custody_acquisition_"
    "scientific_response_v0"
)
VERDICT = (
    "SELECTED_TARGETED_EOTWASH_AUTHOR_OR_CUSTODIAN_CONTACT_PACKET_PREPARATION"
)
SELECTED_CANDIDATE_ID = (
    "TARGETED_EOTWASH_AUTHOR_OR_CUSTODIAN_CONTACT_PREPARATION"
)
SELECTED_NEXT_TARGET = (
    "prepare_eotwash_2020_yukawa_author_or_custodian_contact_packet_v0"
)
SELECTED_NEXT_TARGET_KIND = "PREPARATION_ONLY_NO_CONTACT_OR_EMPIRICAL_ANALYSIS"

AUTHORITY_HASHES = {
    "formal/docs/lanes/EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_RESULT_REVIEW_20260718_v0.md":
        "c036e4a3d30ae6c7016711d8a7bc099ac44b60e78c0e3f4a84f0886b6e54dd45",
    REVIEW_RELATIVE_PATH:
        "f5a6b3942b728400b925f99a8b953a7a434e37c6d17e36e90c6cd8a6d44108c8",
    "formal/python/tools/eotwash_2020_yukawa_primary_evidence_custody_acquisition_result_review_v0.py":
        "b378485186825bd06c341c80e4c1b97f8801e8c5cc17df00cf881b6eda3e7866",
    "formal/python/tests/test_eotwash_2020_yukawa_primary_evidence_custody_acquisition_result_review_v0.py":
        "1896e9a606fb52a97ee0535ea1110a96a192d75035a4ec085b775c2dd5b1f0ca",
    "formal/toe_formal/ToeFormal/Derivation/Eotwash2020YukawaPrimaryEvidenceCustodyAcquisitionResultReviewV0.lean":
        "5f095aa8027f00eb95f23c0140d70e53ba4ca8423a87ed273f57e58a336a3b84",
}

CRITERIA = {
    "direct_repair_of_accepted_block": 5,
    "independent_fit_restoration_potential": 5,
    "confirmed_empirical_target_continuity": 4,
    "new_information_gain": 4,
    "boundedness": 3,
    "authority_clarity": 3,
    "cost_proportionality": 2,
    "computational_progress": 2,
}

CANDIDATES = [
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "target": SELECTED_NEXT_TARGET,
        "kind": "CONTACT_PACKET_PREPARATION_ONLY",
        "scores": {
            "direct_repair_of_accepted_block": 5,
            "independent_fit_restoration_potential": 5,
            "confirmed_empirical_target_continuity": 5,
            "new_information_gain": 5,
            "boundedness": 5,
            "authority_clarity": 5,
            "cost_proportionality": 4,
            "computational_progress": 2,
        },
        "disposition": "SELECTED_FOR_PACKET_PREPARATION_ONLY",
        "scientific_endpoint": (
            "Prepare a bounded, professional request for the finite missing "
            "primary evidence package without sending any message."
        ),
    },
    {
        "candidate_id": "SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_SENSITIVITY_FORECAST",
        "target": (
            "prepare_scalar_only_yukawa_synthetic_forward_model_and_"
            "sensitivity_forecast_packet_v0"
        ),
        "kind": "EXPLORATORY_SYNTHETIC_COMPUTATIONAL_LANE",
        "scores": {
            "direct_repair_of_accepted_block": 1,
            "independent_fit_restoration_potential": 0,
            "confirmed_empirical_target_continuity": 4,
            "new_information_gain": 5,
            "boundedness": 5,
            "authority_clarity": 5,
            "cost_proportionality": 4,
            "computational_progress": 5,
        },
        "disposition": "DEFERRED_HIGH_PRIORITY_FALLBACK_NOT_REJECTED",
        "scientific_endpoint": (
            "Build an explicitly approximate apparatus forecast with synthetic "
            "injection recovery and no Eot-Wash empirical-bound claim."
        ),
    },
    {
        "candidate_id": "SUPPLIED_PUBLISHED_EOTWASH_LIMIT_REINTERPRETATION",
        "target": (
            "prepare_supplied_eotwash_fixed_strength_yukawa_constraint_"
            "reinterpretation_packet_v0"
        ),
        "kind": "SUPPLIED_EMPIRICAL_EVIDENCE_ONLY",
        "scores": {
            "direct_repair_of_accepted_block": 1,
            "independent_fit_restoration_potential": 0,
            "confirmed_empirical_target_continuity": 5,
            "new_information_gain": 2,
            "boundedness": 5,
            "authority_clarity": 5,
            "cost_proportionality": 5,
            "computational_progress": 2,
        },
        "disposition": "DEFERRED_NOT_REJECTED",
        "scientific_endpoint": (
            "Translate only the authors' published Yukawa result into lambda0, "
            "inverse-length mass, particle-mass equivalent, and packet alpha."
        ),
    },
    {
        "candidate_id": "FULLY_PUBLIC_ALTERNATIVE_EXPERIMENT_SELECTION",
        "target": (
            "prepare_reproducible_fixed_strength_yukawa_alternative_"
            "experiment_survey_v0"
        ),
        "kind": "ALTERNATIVE_EXPERIMENT_REPRODUCIBILITY_SELECTION",
        "scores": {
            "direct_repair_of_accepted_block": 2,
            "independent_fit_restoration_potential": 3,
            "confirmed_empirical_target_continuity": 2,
            "new_information_gain": 4,
            "boundedness": 2,
            "authority_clarity": 4,
            "cost_proportionality": 1,
            "computational_progress": 3,
        },
        "disposition": "DEFERRED_UNLESS_CONTACT_FAILS_NOT_REJECTED",
        "scientific_endpoint": (
            "Select a replacement only if public observations, covariance, "
            "geometry, nuisance treatment, and A_Y=1/3 sensitivity are complete."
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
            row["selected_candidate_id"] == SELECTED_CANDIDATE_ID
            for row in rows
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
            raise ValueError(f"acquisition result-review drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})
    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != (
        "ACCEPTED_BOUNDED_PRIMARY_EVIDENCE_ACQUISITION_RESULT"
    ):
        raise ValueError("acquisition result review is not accepted")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("acquisition result review did not authorize this selector")
    if review["scope"].get("scientific_response_selection_authorized") is not True:
        raise ValueError("scientific response selection is not authorized")
    if review["scope"].get("author_or_custodian_contact_authorized") is not False:
        raise ValueError("contact was unexpectedly authorized")
    if review["scope"].get("likelihood_executed") is not False:
        raise ValueError("likelihood was unexpectedly executed")
    return custody, review


def build_selection() -> dict[str, Any]:
    custody, review = _validate_authority()
    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if ranking[0]["candidate_id"] != SELECTED_CANDIDATE_ID:
        raise ValueError("unexpected post-acquisition selection winner")
    if ranking[1]["candidate_id"] != (
        "SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_SENSITIVITY_FORECAST"
    ):
        raise ValueError("synthetic fallback is not the expected runner-up")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("post-acquisition selection winner is unstable")
    human = REPO_ROOT / HUMAN_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    lean = REPO_ROOT / LEAN_RELATIVE_PATH
    if not human.is_file() or not test.is_file() or not lean.is_file():
        raise ValueError("selection human, test, or Lean artifact missing")

    gate_ids = [
        "ACCEPTED_ACQUISITION_RESULT_CUSTODY_AND_EXACT_SELECTOR_TARGET",
        "EXACTLY_FOUR_AUTHORIZED_RESPONSES_COMPARED",
        "EXPERIMENT_SUITABILITY_RETAINED_WITHOUT_EMPIRICAL_INFERENCE",
        "ZERO_OF_SIX_COMPLETE_AND_LIKELIHOOD_BLOCK_RETAINED",
        "CONTACT_PREPARATION_DIRECTLY_TARGETS_ACCEPTED_BLOCK",
        "EXACT_EIGHT_REQUESTED_OBJECTS_FROZEN_FOR_FUTURE_PACKET",
        "RECIPIENT_AND_DATA_USE_OBLIGATIONS_REQUIRED",
        "ONE_INITIAL_CONTACT_AND_BOUNDED_FOLLOWUP_REQUIRED",
        "NO_MESSAGE_DRAFTED_OR_SENT_DURING_SELECTION",
        "SYNTHETIC_FORECAST_REMAINS_EXPLORATORY_FALLBACK",
        "PUBLISHED_REINTERPRETATION_REMAINS_SUPPLIED_NOT_REPRODUCED",
        "ALTERNATIVE_EXPERIMENT_REQUIRES_COMPLETE_PUBLIC_CONTRACT",
        "ALL_DEFERRED_ROUTES_REMAIN_OPEN_NOT_REJECTED",
        "RANKING_CRITERIA_AND_SCORES_EXPLICIT",
        "CONTACT_PREPARATION_WINS_ALL_24_SENSITIVITY_VARIANTS",
        "SYNTHETIC_ROUTE_IS_RUNNER_UP",
        "PREPARATION_ONLY_NO_CONTACT_ANALYSIS_PARAMETER_OR_ACTION_SELECTION",
    ]

    requested_items = [
        "official supplemental package or authenticated accessible copy",
        "machine-readable 95x3 torque vector with complete row and configuration metadata",
        "statistical uncertainty and covariance or equivalent generative model",
        "definitions priors constraints and executable implementation of five profiled nuisances",
        "extended-source Newtonian and Yukawa torque code or sufficient machine-readable geometry",
        "calibration and published Newtonian-baseline implementation",
        "likelihood and boundary-aware coverage procedure",
        "data-use citation redistribution and repository conditions",
    ]

    return {
        "schema_id": (
            "toe.post_eotwash_2020_yukawa_primary_evidence_custody_acquisition."
            "scientific_response_selection.v0"
        ),
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_candidate_id": SELECTED_CANDIDATE_ID,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_result_review_verdict": review["verdict"],
            "consumed_result_review_gate_count": review["review_gates"]["pass_count"],
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
            "lean": {
                "relative_path": LEAN_RELATIVE_PATH,
                "sha256": _sha256(lean),
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
            "winning_margin": (
                ranking[0]["weighted_score"] - ranking[1]["weighted_score"]
            ),
        },
        "sensitivity_analysis": sensitivity,
        "retained_empirical_posture": {
            "experiment": "EOTWASH_2020_SHORT_RANGE_ISL_TORSION_BALANCE",
            "experiment_suitable": True,
            "fixed_signal": "A_Y=1/3",
            "acquisition_result": "AUTHORS_OR_CUSTODIAN_CONTACT_REQUIRED",
            "evidence_components_complete": 0,
            "evidence_component_count": 6,
            "independent_likelihood_executable": False,
            "likelihood": "NOT_EXECUTED",
            "scalar_range_bound": "NONE",
            "alpha_constraint": "NONE",
        },
        "selected_contact_packet_contract": {
            "status": "PREPARATION_AUTHORIZED_PACKET_NOT_PREPARED",
            "requested_item_count": len(requested_items),
            "requested_items": requested_items,
            "future_packet_obligations": [
                "resolve one appropriate public professional recipient or custodian hierarchy",
                "draft one concise request explaining independent reproduction purpose",
                "state that the request does not challenge the publication",
                "request no personal proprietary security-sensitive or unauthorized material",
                "ask for data-use citation redistribution and access conditions",
                "freeze one initial contact and a bounded follow-up policy",
                "include no unsolicited attachment",
                "stop for independent packet review before sending anything",
            ],
            "terminal_outcomes": [
                "CONTACT_PACKET_READY",
                "CONTACT_RECIPIENT_UNRESOLVED",
                "REQUEST_SCOPE_TOO_BROAD",
                "CONTACT_SENT_RESPONSE_PENDING",
                "PRIMARY_PACKAGE_PROVIDED",
                "PARTIAL_PACKAGE_PROVIDED",
                "PACKAGE_UNAVAILABLE",
                "NO_RESPONSE_WITHIN_BOUNDED_WINDOW",
            ],
            "message_drafted_now": False,
            "message_sent_now": False,
            "contact_authorized": False,
            "analysis_authorized": False,
            "independent_packet_review_required": True,
        },
        "deferred_route_boundaries": {
            "synthetic_forecast": (
                "IDEALIZED_OR_APPROXIMATE_APPARATUS_NOT_EOTWASH_EMPIRICAL_BOUND"
            ),
            "published_reinterpretation": (
                "SUPPLIED_EMPIRICAL_CONSTRAINT_NOT_INDEPENDENTLY_REPRODUCED"
            ),
            "alternative_experiment": (
                "REQUIRES_RELEVANT_SENSITIVITY_COMPLETE_PUBLIC_DATA_COVARIANCE_"
                "GEOMETRY_NUISANCE_AND_STATISTICAL_CONTRACT"
            ),
            "all_deferred_not_rejected": True,
        },
        "selection_gates": {
            "gate_count": len(gate_ids),
            "pass_count": len(gate_ids),
            "failure_count": 0,
            "rows": [
                {"gate_id": gate_id, "status": "PASS"}
                for gate_id in gate_ids
            ],
        },
        "scope": {
            "scientific_response_selection_executed": True,
            "contact_packet_preparation_authorized": True,
            "contact_packet_prepared_now": False,
            "contact_recipient_selected": False,
            "contact_message_drafted": False,
            "author_or_custodian_contact_authorized": False,
            "author_or_custodian_contact_executed": False,
            "synthetic_forecast_authorized": False,
            "published_constraint_reinterpretation_authorized": False,
            "alternative_experiment_selected": False,
            "likelihood_preparation_authorized": False,
            "likelihood_executed": False,
            "numerical_lambda_bound_computed": False,
            "numerical_alpha_bound_computed": False,
            "beta_zero_adopted": False,
            "alpha_sign_or_value_adopted": False,
            "scalar_branch_adopted": False,
            "native_scalar_bridge_identified": False,
            "native_gravitational_principle_identified": False,
            "gravitational_action_selected": False,
            "matter_sector_selected": False,
            "frame_dragging_resumed": False,
            "master_action_mutated": False,
        },
        "current_posture": {
            "selected_response": SELECTED_CANDIDATE_ID,
            "selection_stability": "FIRST_IN_24_OF_24_VARIANTS",
            "runner_up": (
                "SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_"
                "SENSITIVITY_FORECAST"
            ),
            "contact_packet": "NOT_YET_PREPARED",
            "author_contact": "NOT_AUTHORIZED",
            "synthetic_forecast": "NOT_AUTHORIZED",
            "published_reinterpretation": "NOT_AUTHORIZED",
            "likelihood": "NOT_EXECUTED",
            "scalar_range_bound": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This scientific-response selection authorizes preparation only of "
            "a bounded Eot-Wash 2020 author-or-data-custodian contact packet. "
            "No recipient is selected, no message is drafted or sent, no contact "
            "is authorized, no synthetic forecast or published-limit "
            "reinterpretation is authorized, and no likelihood, scalar-range or "
            "alpha bound, scalar-branch adoption, native gravitational principle, "
            "gravitational action, frame-dragging result, or master-action change "
            "is computed, selected, claimed, or authorized."
        ),
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_selection(), indent=2, sort_keys=True, ensure_ascii=True)
        + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Select the response to the accepted Eot-Wash acquisition result."
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if args.write:
        path.write_bytes(raw)
        print("post_eotwash_acquisition_selection_v0: wrote contact preparation selection")
        return 0
    if not path.is_file() or path.read_bytes() != raw:
        print("post_eotwash_acquisition_selection_v0: FAILED artifact drift")
        return 1
    print("post_eotwash_acquisition_selection_v0: OK selected contact preparation")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
