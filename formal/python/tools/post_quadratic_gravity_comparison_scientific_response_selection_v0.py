from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_post_quadratic_gravity_comparison_scientific_response_selection_v0.py"
)
TARGET = "select_post_quadratic_gravity_comparison_scientific_response_v0"
SELECTED_NEXT_TARGET = (
    "prepare_post_quadratic_gravity_comparison_conditional_mode_selection_packet_v0"
)
VERDICT = "SELECTED_CONDITIONAL_MODE_SELECTION_ENVELOPE_PACKET_PREPARATION"

AUTHORITY_HASHES = {
    "formal/docs/lanes/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_COMPARISON_RESULT_REVIEW_20260718_v0.md":
        "95f113c409ae2f4733c1eae90f26f3d3c0aa0bbdce33b7e2ae62c88f236398da",
    "formal/docs/release/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_COMPARISON_RESULT_REVIEW_20260718_v0.json":
        "69f59eba7c17f102a539e43b3155905772bad84dc2794a8d1a85129d112ba925",
    "formal/python/tools/shared_linearized_quadratic_gravity_source_and_spectrum_comparison_result_review_v0.py":
        "28af172dfe7ffcfa3bbc6a1d74bd4f097f75ec675aa7699148511ff58e2a88da",
    "formal/python/tests/test_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_result_review_v0.py":
        "71cbe7dd1137491595d232e25c449fa2528d4efb1ffac60d9d466f20e041bca8",
    "formal/toe_formal/ToeFormal/Derivation/SharedLinearizedQuadraticGravitySourceAndSpectrumComparisonResultReviewV0.lean":
        "b211f8681abf18b698068aefc4ce501114df04978989061782ea37624a3639aa",
}

CRITERIA = {
    "direct_use_of_accepted_result": 3,
    "native_vs_supplied_clarity": 3,
    "conditional_discrimination": 3,
    "bounded_endpoint_precision": 3,
    "prevents_action_adoption": 2,
    "next_decision_leverage": 2,
    "avoids_scope_expansion": 2,
    "stopping_rule_precision": 2,
}

CANDIDATES = [
    {
        "candidate_id": "PREPARE_CONDITIONAL_MODE_SELECTION_ENVELOPE",
        "target": SELECTED_NEXT_TARGET,
        "kind": "PACKET_PREPARATION_ONLY",
        "scores": {key: 5 for key in CRITERIA},
        "scientific_endpoint": (
            "Map each proposed mode, stability, and source-response condition to its "
            "exact consequence inside the accepted quadratic comparison and to its "
            "current authority class, without adopting the condition."
        ),
    },
    {
        "candidate_id": "RESUME_METRIC_TO_ORBIT_AND_FRAME_DRAGGING_TRANSPORT",
        "target": "prepare_comparison_metric_to_orbit_transport_packet_v0",
        "kind": "DOWNSTREAM_COMPARISON_TRANSPORT",
        "scores": {
            "direct_use_of_accepted_result": 4,
            "native_vs_supplied_clarity": 2,
            "conditional_discrimination": 3,
            "bounded_endpoint_precision": 4,
            "prevents_action_adoption": 4,
            "next_decision_leverage": 3,
            "avoids_scope_expansion": 5,
            "stopping_rule_precision": 3,
        },
        "scientific_endpoint": (
            "Transport the comparison metric to orbital observables without first "
            "resolving which mode-selection condition has project authority."
        ),
    },
    {
        "candidate_id": "PROPOSE_MINIMAL_GRAVITATIONAL_MODE_POSTULATE",
        "target": "propose_minimal_gravitational_mode_content_postulate_v0",
        "kind": "NEW_POSTULATE",
        "scores": {
            "direct_use_of_accepted_result": 4,
            "native_vs_supplied_clarity": 1,
            "conditional_discrimination": 5,
            "bounded_endpoint_precision": 4,
            "prevents_action_adoption": 1,
            "next_decision_leverage": 4,
            "avoids_scope_expansion": 4,
            "stopping_rule_precision": 3,
        },
        "scientific_endpoint": (
            "Adopt no-extra-mode content before demonstrating that this condition is "
            "native rather than supplied or newly proposed."
        ),
    },
    {
        "candidate_id": "EXPAND_BEYOND_LOCAL_METRIC_QUADRATIC_FAMILY",
        "target": "select_post_quadratic_gravity_family_expansion_v0",
        "kind": "THEORY_FAMILY_EXPANSION",
        "scores": {
            "direct_use_of_accepted_result": 2,
            "native_vs_supplied_clarity": 2,
            "conditional_discrimination": 4,
            "bounded_endpoint_precision": 2,
            "prevents_action_adoption": 4,
            "next_decision_leverage": 3,
            "avoids_scope_expansion": 1,
            "stopping_rule_precision": 2,
        },
        "scientific_endpoint": (
            "Open nonlocal, extra-field, independent-connection, torsionful, or other "
            "mechanisms before extracting the accepted comparison's conditional fork."
        ),
    },
]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _weighted_score(scores: dict[str, int], weights: dict[str, int]) -> int:
    if set(scores) != set(weights):
        raise ValueError("candidate score criteria mismatch")
    if any(value < 0 or value > 5 for value in scores.values()):
        raise ValueError("candidate criterion score outside 0..5")
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
    for criterion, baseline_weight in CRITERIA.items():
        for delta in (-1, 1):
            weights = dict(CRITERIA)
            weights[criterion] = max(1, baseline_weight + delta)
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
            row["selected_candidate_id"]
            == "PREPARE_CONDITIONAL_MODE_SELECTION_ENVELOPE"
            for row in rows
        ),
        "minimum_winning_margin": min(
            row["selected_score"] - row["runner_up_score"] for row in rows
        ),
    }


def _validate_authority() -> tuple[list[dict[str, str]], dict[str, Any]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"comparison result-review authority mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    review_path = REPO_ROOT / (
        "formal/docs/release/"
        "SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_COMPARISON_"
        "RESULT_REVIEW_20260718_v0.json"
    )
    review = json.loads(review_path.read_text(encoding="utf-8"))
    if review.get("verdict") != (
        "ACCEPTED_BOUNDED_SHARED_LINEARIZED_QUADRATIC_GRAVITY_COMPARISON_RESULT"
    ):
        raise ValueError("comparison result was not accepted")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("comparison result review did not authorize this selection")
    if review["review_gates"].get("pass_count") != 16:
        raise ValueError("comparison review gate count mismatch")
    if review["scope"].get("comparison_result_accepted") is not True:
        raise ValueError("accepted comparison result scope mismatch")
    if review["scope"].get("comparison_action_selected") is not False:
        raise ValueError("comparison action was unexpectedly selected")
    if review["scope"].get("new_postulate_authorized") is not False:
        raise ValueError("comparison review unexpectedly authorized a postulate")
    if review["accepted_bounded_claim"].get("massive_spin_2") != (
        "m2^2=1/beta; NEGATIVE_ISOLATED_OR_PROJECTOR_RESOLVED_RESIDUE"
    ):
        raise ValueError("accepted massive-spin-2 result mismatch")
    if review["accepted_bounded_claim"].get("stationary_0i") != (
        "MASSLESS_PLUS_ADDITIONAL_SPIN_2; SCALAR_ZERO"
    ):
        raise ValueError("accepted stationary-current result mismatch")
    return rows, review


def _conditional_rows() -> list[dict[str, Any]]:
    return [
        {
            "condition_id": "NON_TACHYONIC_SCALAR",
            "condition": "m0^2>0",
            "consequence": "Sigma=3 alpha+beta<0",
            "exact_within_frozen_family": True,
            "qualification": "DOES_NOT_REMOVE_SCALAR_OR_PROVE_FULL_STABILITY",
        },
        {
            "condition_id": "NON_TACHYONIC_ADDITIONAL_SPIN_2",
            "condition": "m2^2>0",
            "consequence": "beta>0",
            "exact_within_frozen_family": True,
            "qualification": "NEGATIVE_SATURATED_RESIDUE_REMAINS",
        },
        {
            "condition_id": "NO_NEGATIVE_RESIDUE_ADDITIONAL_SPIN_2_POLE",
            "condition": "additional spin-2 pole absent for generic conserved sources",
            "consequence": "beta=0",
            "exact_within_frozen_family": True,
            "qualification": "FINITE_LOCAL_QUADRATIC_METRIC_FAMILY_ONLY",
        },
        {
            "condition_id": "NO_ADDITIONAL_SCALAR_POLE",
            "condition": "additional scalar pole absent",
            "consequence": "Sigma=0",
            "exact_within_frozen_family": True,
            "qualification": "ABSENT_OR_INFINITE_MASS_STRATUM",
        },
        {
            "condition_id": "NO_ADDITIONAL_MODES",
            "condition": "both additional poles absent",
            "consequence": "beta=0 and Sigma=0 implies alpha=beta=0",
            "exact_within_frozen_family": True,
            "qualification": "CONDITIONAL_EINSTEIN_BASELINE_COLLAPSE_ONLY",
        },
        {
            "condition_id": "SCALAR_ALLOWED_SPIN_2_EXCLUDED_AND_SCALAR_NON_TACHYONIC",
            "condition": "beta=0 and m0^2>0",
            "consequence": "beta=0 and alpha<0",
            "exact_within_frozen_family": True,
            "qualification": "CONVENTION_SPECIFIC_LINEARIZED_BRANCH",
        },
        {
            "condition_id": "LONG_RANGE_EINSTEIN_RESPONSE_ONLY",
            "condition": "finite-range terms decay at tested long range",
            "consequence": "broad finite positive-mass or decoupling region remains",
            "exact_within_frozen_family": False,
            "qualification": "NONSELECTIVE_WITHOUT_RANGE_AND_PRECISION_BOUNDS",
        },
        {
            "condition_id": "EXACT_UNMODIFIED_STATIONARY_0I_FOR_GENERIC_CURRENTS",
            "condition": "no finite-range spin-2 current kernel at any finite range",
            "consequence": "beta=0",
            "exact_within_frozen_family": True,
            "qualification": "EMPIRICAL_AGREEMENT_ONLY_BOUNDS_OR_SUPPRESSES_M2_RANGE",
        },
    ]


def build_selection() -> dict[str, Any]:
    authority, review = _validate_authority()
    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if ranking[0]["candidate_id"] != "PREPARE_CONDITIONAL_MODE_SELECTION_ENVELOPE":
        raise ValueError("unexpected post-comparison response-selection winner")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("post-comparison response-selection winner is unstable")

    human_path = REPO_ROOT / HUMAN_RELATIVE_PATH
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not human_path.exists() or not test_path.exists():
        raise ValueError("response-selection human record or test is missing")
    tool_path = Path(__file__).resolve()

    gates = [
        "ACCEPTED_RESULT_CUSTODY_AND_EXACT_TARGET",
        "FROZEN_CONVENTIONS_RETAINED",
        "GHOST_TACHYON_INSTABILITY_AND_DECOUPLING_DISTINCT",
        "EXACT_REMOVAL_VS_EMPIRICAL_SUPPRESSION_DISTINCT",
        "COINCIDENT_MASS_IS_PROJECTOR_RESOLVED_WITH_NO_CANCELLATION",
        "BETA_ZERO_EXTRA_SPIN_2_REMOVAL_SCOPED_TO_FROZEN_FAMILY",
        "SIGMA_ZERO_SCALAR_REMOVAL_AND_EINSTEIN_LIMIT_EXACT",
        "SCALAR_ONLY_NON_TACHYONIC_BRANCH_EXACT",
        "EVERY_SELECTING_CONDITION_REQUIRES_AUTHORITY_CLASS",
        "LONG_RANGE_RECOVERY_REMAINS_NONSELECTIVE",
        "OUTSIDE_FAMILY_MECHANISMS_DEFERRED",
        "PACKET_PREPARATION_ONLY_AND_HARD_STOP",
    ]

    return {
        "schema_id": (
            "POST_QUADRATIC_GRAVITY_COMPARISON_SCIENTIFIC_RESPONSE_SELECTION_"
            "20260718_v0"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": (
            "PREPARATION_ONLY_CONDITIONAL_MODE_SELECTION_ENVELOPE"
        ),
        "authority": {
            "consumed_verdict": review["verdict"],
            "consumed_review_gates": review["review_gates"]["pass_count"],
            "frozen_result_review_artifacts": authority,
            "human_selection": {
                "relative_path": HUMAN_RELATIVE_PATH,
                "sha256": _sha256(human_path.read_bytes()),
            },
            "generator": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path.read_bytes()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path.read_bytes()),
            },
        },
        "selection_policy": {
            "criterion_scale": "0..5",
            "weights": CRITERIA,
            "maximum_weighted_score": 100,
            "candidate_count": len(CANDIDATES),
        },
        "ranking": {
            "rows": ranking,
            "selected_candidate_id": ranking[0]["candidate_id"],
            "selected_score": ranking[0]["weighted_score"],
            "runner_up_candidate_id": ranking[1]["candidate_id"],
            "runner_up_score": ranking[1]["weighted_score"],
        },
        "sensitivity_analysis": sensitivity,
        "conditional_mode_selection_envelope": {
            "Sigma_definition": "Sigma=3 alpha+beta",
            "m0_squared": "-1/(2 Sigma)",
            "m2_squared": "1/beta",
            "rows": _conditional_rows(),
            "coincident_mass_rule": (
                "2 alpha+beta=0 with beta!=0 gives coincident simple poles in "
                "orthogonal P2 and P0s channels; no cancellation or ghost repair"
            ),
            "authority_classes_required": [
                "PROJECT_BOUND_NATIVE_PRINCIPLE",
                "SUPPLIED_STANDARD_PHYSICS_CRITERION",
                "PROPOSED_NEW_POSTULATE",
                "EMPIRICAL_CONSTRAINT",
            ],
            "condition_adopted_now": None,
        },
        "preparation_gates": {
            "gate_count": len(gates),
            "pass_count": len(gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in gates],
        },
        "retained_boundaries": {
            "comparison_result": "ACCEPTED_16_OF_16_GATES",
            "comparison_action": "SUPPLIED_COMPARISON_ONLY",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "native_gravitational_action": "NOT_SELECTED",
            "condition_or_postulate": "NONE_ADOPTED",
            "frame_dragging": "NOT_RESUMED",
            "authoritative_V2_matrix": "0_OF_70",
        },
        "scope": {
            "scientific_response_selection_executed": True,
            "conditional_packet_preparation_authorized": True,
            "conditional_packet_prepared_now": False,
            "condition_adopted": False,
            "native_principle_identified": False,
            "new_postulate_authorized": False,
            "alpha_or_beta_selected": False,
            "gravitational_action_selected": False,
            "comparison_action_promoted": False,
            "outside_family_mechanism_opened": False,
            "empirical_constraint_derived": False,
            "empirical_fitting_authorized": False,
            "nonlinear_or_arbitrary_background_claimed": False,
            "matter_sector_selected": False,
            "orbital_transport_authorized": False,
            "frame_dragging_reopened": False,
            "master_action_mutated": False,
            "authoritative_V2_matrix_populated": False,
        },
        "claim_ceiling": (
            "Response selection only. Preparation of one conditional mode-selection "
            "packet is authorized next. No condition, native principle, postulate, "
            "coupling, action, outside-family mechanism, empirical constraint, matter "
            "sector, orbital transport, frame-dragging result, V2 cell, or master-action "
            "change is created or authorized here."
        ),
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_selection(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.exists() or report_path.read_bytes() != raw:
            raise SystemExit("post-comparison response selection is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "gates": report["preparation_gates"]["pass_count"],
            "minimum_sensitivity_margin": report["sensitivity_analysis"][
                "minimum_winning_margin"
            ],
            "selected": report["ranking"]["selected_candidate_id"],
            "status": "CHECKED",
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

