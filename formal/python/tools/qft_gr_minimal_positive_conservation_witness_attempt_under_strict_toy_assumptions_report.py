from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions_result_review_report import (
    CANONICAL_OBSTRUCTION_ID,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OBSTRUCTION_STATUS,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-14T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_UNDER_STRICT_TOY_"
    "ASSUMPTIONS_20260614_v0"
)
ATTEMPT_ID = (
    "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_UNDER_STRICT_TOY_"
    "ASSUMPTIONS_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_UNDER_STRICT_TOY_"
    "ASSUMPTIONS_EXECUTED_WITH_NO_SOURCE_ADMISSIBILITY_OR_QFT_GR_CLOSURE"
)
RESULT_CLASSIFICATION = (
    "qft_gr_minimal_positive_conservation_witness_under_strict_toy_"
    "assumptions_achieved_pending_result_review"
)
FAILED_CLASSIFICATION = (
    "qft_gr_minimal_positive_conservation_witness_under_strict_toy_"
    "assumptions_failed_requires_countermodel_packet"
)
INCONCLUSIVE_CLASSIFICATION = (
    "qft_gr_minimal_positive_conservation_witness_under_strict_toy_"
    "assumptions_inconclusive_requires_assumption_stabilization"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "review_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_"
    "toy_assumptions_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_"
    "assumptions_result_review"
)
COUNTERMODEL_TARGET = (
    "prepare_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_"
    "obstruction"
)
ASSUMPTION_STABILIZATION_TARGET = (
    "prepare_qft_gr_minimal_positive_conservation_witness_assumption_"
    "stabilization_packet_under_strict_toy_assumptions"
)
IMMEDIATE_RETEST_TARGET = (
    "execute_qft_gr_minimal_working_model_conservation_retest_attempt_after_"
    "post_retest_refinement_conservation_retest_refinement_refinement"
)
ORDINARY_REFINEMENT_TARGET = (
    "prepare_qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_refinement"
)
LEAN_ATTEMPT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalPositiveConservationWitnessAttemptUnderStrictToyAssumptions.lean"
)
LEAN_NAMESPACE = (
    "ToeFormal.Derivation."
    "QFTGRMinimalPositiveConservationWitnessAttemptUnderStrictToyAssumptions"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_UNDER_STRICT_"
        "TOY_ASSUMPTIONS_20260614_v0.json"
    )
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _classification_options() -> list[str]:
    return [
        RESULT_CLASSIFICATION,
        FAILED_CLASSIFICATION,
        INCONCLUSIVE_CLASSIFICATION,
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The strict toy Lean implication theorem was constructed, so "
                "the only authorized next action is bounded result review."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The bounded witness attempt target is consumed here.",
        },
        {
            "target": COUNTERMODEL_TARGET,
            "decision": "not_selected_unless_result_review_rejects_or_fails",
            "reason": (
                "Countermodel/no-go work remains the fail route, but this "
                "attempt is classified achieved pending review."
            ),
        },
        {
            "target": ASSUMPTION_STABILIZATION_TARGET,
            "decision": "not_selected_because_attempt_classified_achieved",
            "reason": (
                "Assumption stabilization is the inconclusive route, not the "
                "selected route for this theorem-bearing attempt."
            ),
        },
        {
            "target": IMMEDIATE_RETEST_TARGET,
            "decision": "not_authorized",
            "reason": "The QFT-GR pivot still forbids immediate broad conservation retest.",
        },
        {
            "target": ORDINARY_REFINEMENT_TARGET,
            "decision": "not_authorized",
            "reason": "Ordinary same-shaped model refinement remains out of scope.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "Strict toy weak conservation is not source admissibility.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": "Bianchi compatibility remains unclaimed.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "reason": "No semiclassical Einstein equation is derived.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "The strict toy witness does not close QFT-GR.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
        {
            "target": "promote_master_action",
            "decision": "not_authorized",
            "reason": "The master action is not promoted by this checkpoint.",
        },
    ]


def _validation_policy(result_review: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_positive_conservation_witness_attempt_execution",
        "routine_attempt_uses_bounded_target_relevant_validation_only": True,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_aggregate_lean_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
        "long_running_validation_escalation_authorized": False,
        "timeout_rerun_loop_authorized": False,
        "timeout_recorded_as_caveat_not_rerun_instruction": True,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_timeout_caveat_preserved": True,
        "aggregate_lean_health_claimed": False,
        "inherited_packet_result_review_validation_policy": result_review.get(
            "validation_policy", {}
        ),
    }


def build_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    lean_attempt_path: Path = LEAN_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    lean_text = _read_text(lean_attempt_path)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(result_review)
    lean_theorem_names = [
        "strict_toy_weak_conservation_witness",
        "strict_toy_witness_attempt_is_theorem_bearing",
        "strict_toy_witness_attempt_does_not_claim_source_admissibility",
        "strict_toy_witness_attempt_does_not_claim_bianchi_or_semiclassical_einstein",
        "strict_toy_witness_attempt_does_not_close_qft_gr",
        "strict_toy_witness_attempt_no_empirical_or_public_submission",
        "strict_toy_witness_attempt_no_master_action_promotion",
    ]

    lean_contains_required_shape = all(
        marker in lean_text
        for marker in [
            "structure StrictToyConservationData",
            "def weakConservationAgainstAllowedTests",
            "theorem strict_toy_weak_conservation_witness",
            "divergenceIdentityImpliesWeakConservation",
            "fieldEquationResidualZero",
            "divergenceIdentityAvailable",
            "allowedWeakPairingAvailable",
            "compactSupportNoBoundary",
        ]
    )

    acceptance_criteria = {
        "consumes_expected_packet_result_review": (
            result_review.get("schema_id") == EXPECTED_RESULT_REVIEW_SCHEMA_ID
            and result_review.get("review_id") == EXPECTED_RESULT_REVIEW_ID
            and result_review.get("outcome_id") == EXPECTED_RESULT_REVIEW_OUTCOME
            and result_review.get("result_review_classification")
            == EXPECTED_RESULT_REVIEW_CLASSIFICATION
        ),
        "packet_result_review_authorized_this_attempt_only": (
            result_review.get("accepted") is True
            and result_review.get("selected_next_target") == CONSUMED_TARGET
            and result_review.get("positive_witness_attempt_authorized") is True
            and result_review.get("bounded_witness_attempt_authorized_only") is True
            and result_review.get("positive_witness_attempt_executed") is False
        ),
        "lean_attempt_file_is_theorem_bearing": lean_contains_required_shape
        and all(f"theorem {name}" in lean_text for name in lean_theorem_names),
        "attempt_selects_exactly_one_classification": (
            _classification_options().count(RESULT_CLASSIFICATION) == 1
            and RESULT_CLASSIFICATION not in [FAILED_CLASSIFICATION, INCONCLUSIVE_CLASSIFICATION]
        ),
        "attempt_classified_achieved_pending_review": (
            RESULT_CLASSIFICATION
            == (
                "qft_gr_minimal_positive_conservation_witness_under_strict_toy_"
                "assumptions_achieved_pending_result_review"
            )
        ),
        "strict_toy_witness_fields_are_bounded": (
            result_review.get("strict_toy_assumptions_only") is True
            and result_review.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
            and result_review.get("dominant_obstruction_candidate")
            == DOMINANT_OBSTRUCTION_CANDIDATE
            and result_review.get("canonical_obstruction_id")
            == CANONICAL_OBSTRUCTION_ID
            and result_review.get("obstruction_status") == OBSTRUCTION_STATUS
        ),
        "review_selects_attempt_result_review_only": _selected_targets(
            candidate_next_targets
        )
        == [NEXT_TARGET],
        "no_immediate_retest_or_ordinary_refinement": (
            result_review.get("immediate_retest_authorized") is False
            and result_review.get("conservation_retest_rerun_authorized") is False
            and result_review.get("ordinary_model_refinement_authorized") is False
        ),
        "no_source_admissibility_bianchi_or_qft_gr_closure": (
            result_review.get("source_admissibility_claimed") is False
            and result_review.get("stress_energy_source_admissibility_claimed")
            is False
            and result_review.get("Bianchi_compatibility_claimed") is False
            and result_review.get("semiclassical_einstein_equation_derived") is False
            and result_review.get("qft_gr_seam_closed") is False
            and result_review.get("qft_gr_source_map_closure_claimed") is False
        ),
        "no_empirical_public_or_master_action_promotion": (
            result_review.get("empirical_validation_claimed") is False
            and result_review.get("public_submission_authorized") is False
            and result_review.get("master_action_promoted") is False
            and result_review.get("master_action_promotion_authorized") is False
        ),
        "routine_validation_policy_preserves_non_escalation": all(
            validation_policy[key] is False
            for key in [
                "full_pytest_required",
                "full_governance_suite_required",
                "full_aggregate_lean_required",
                "full_ci_parity_required",
                "full_security_scan_required",
                "long_running_validation_escalation_authorized",
                "timeout_rerun_loop_authorized",
                "aggregate_lean_health_claimed",
            ]
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_"
            "UNDER_STRICT_TOY_ASSUMPTIONS"
        )
    )

    return {
        "schema_id": SCHEMA_ID,
        "attempt_id": ATTEMPT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "executed": accepted,
        "accepted": accepted,
        "attempt_decision": "executed" if accepted else "requires_remediation",
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_UNDER_"
            "STRICT_TOY_ASSUMPTIONS_REQUIRES_REMEDIATION"
        ),
        "result_classification": RESULT_CLASSIFICATION
        if accepted
        else INCONCLUSIVE_CLASSIFICATION,
        "selected_classification": RESULT_CLASSIFICATION
        if accepted
        else INCONCLUSIVE_CLASSIFICATION,
        "classification_options": _classification_options(),
        "result_classification_count": 1 if accepted else 0,
        "selected_classification_count": 1 if accepted else 0,
        "failed_classification_not_selected": True,
        "inconclusive_classification_not_selected": True,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_positive_conservation_witness_packet_result_review": (
            EXPECTED_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_minimal_positive_conservation_witness_packet_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "packet_result_review_accepted": result_review.get("accepted"),
        "positive_witness_packet_result_review_accepted": result_review.get(
            "positive_witness_packet_result_review_accepted"
        ),
        "positive_witness_attempt_authorized": result_review.get(
            "positive_witness_attempt_authorized"
        ),
        "bounded_witness_attempt_authorized_only": result_review.get(
            "bounded_witness_attempt_authorized_only"
        ),
        "strict_toy_assumptions_only": True,
        "theorem_bearing_attempt": accepted,
        "strict_toy_weak_conservation_witness_achieved": accepted,
        "strict_toy_weak_conservation_theorem_constructed": accepted,
        "weak_conservation_against_allowed_tests_proved": accepted,
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "theorem_shape": (
            "field_equation_residual_zero + divergence_identity + "
            "allowed_weak_pairing + compact_support/no_boundary => "
            "weak_conservation_against_allowed_tests"
        ),
        "proof_strategy": (
            "The Lean theorem packages the strict toy data with a supplied "
            "divergence identity, then applies that identity to residual zero, "
            "divergence identity availability, allowed weak pairing, and "
            "compact-support/no-boundary assumptions for each allowed test."
        ),
        "lean_theorem_file": _ptr(lean_attempt_path),
        "lean_theorem_namespace": LEAN_NAMESPACE,
        "lean_theorem_names": lean_theorem_names,
        "lean_contains_required_shape": lean_contains_required_shape,
        "allowed_weak_test_class_id": result_review.get("allowed_weak_test_class_id"),
        "weak_pairing_id": result_review.get("weak_pairing_id"),
        "source_object_id": result_review.get("source_object_id"),
        "divergence_pairing_id": result_review.get("divergence_pairing_id"),
        "field_equation_residual_id": result_review.get("field_equation_residual_id"),
        "divergence_identity_id": result_review.get("divergence_identity_id"),
        "no_boundary_condition_id": result_review.get("no_boundary_condition_id"),
        "pass_fail_inconclusive_criteria": result_review.get(
            "pass_fail_inconclusive_criteria"
        ),
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": OBSTRUCTION_STATUS,
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "positive_witness_attempt_executed": accepted,
        "positive_witness_attempt_result_reviewed": False,
        "strict_toy_witness_attempt_result_review_pending": accepted,
        "countermodel_lane_retained_as_follow_on": True,
        "countermodel_packet_authorized": False,
        "assumption_stabilization_packet_authorized": False,
        "source_map_ladder_lane_retained_as_follow_on": True,
        "source_map_ladder_packet_authorized": False,
        "immediate_retest_authorized": False,
        "conservation_retest_rerun_authorized": False,
        "ordinary_model_refinement_authorized": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "physical_source_claimed": False,
        "conservation_claimed": False,
        "conservation_proved": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "full_qft_gr_conservation_claimed": False,
        "unbounded_conservation_proved": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_claimed": False,
        "empirical_validation_claimed": False,
        "scientific_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "public_submission_authorized": False,
        "publication_authorized": False,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_timeout_caveat_preserved": True,
        "aggregate_lean_health_claimed": False,
        "validation_policy": validation_policy,
        "validation_posture": {
            "focused_attempt_current_target_registry_gate": "required_for_checkpoint",
            "adjacent_minimal_model_nonclaim_gates": "required_bounded_subset",
            "targeted_lean_attempt_frontier_import_checks": "required_for_checkpoint",
            "git_diff_check": "required_for_checkpoint",
            "full_pytest": "not_required_for_checkpoint",
            "full_governance_suite": "not_required_for_checkpoint",
            "full_aggregate_lean": "not_required_for_checkpoint_preserved_caveat",
            "release_index_lean_path": "not_freshly_validated_preserved_caveat",
            "full_ci_parity": "not_required_for_checkpoint",
            "security_scan": "not_required_for_checkpoint",
        },
        "validation_caveat": (
            "Full pytest, full governance suite, full aggregate Lean, release-"
            "index Lean validation, CI parity, and security scans are not "
            "required for this routine bounded witness-attempt checkpoint. "
            "The release-index path remains not freshly Lean-validated, "
            "aggregate Lean is not run, and no aggregate Lean health claim is "
            "made."
        ),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "attempt_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_"
            "UNDER_STRICT_TOY_ASSUMPTIONS_RESULT_ONLY_NO_IMMEDIATE_RETEST_NO_"
            "ORDINARY_MODEL_REFINEMENT_NO_SOURCE_ADMISSIBILITY_NO_BIANCHI_"
            "SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_"
            "PUBLIC_SUBMISSION_OR_MASTER_ACTION_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This attempt constructs only a strict toy theorem-shaped weak "
            "conservation witness: residual zero plus a supplied divergence "
            "identity plus allowed weak pairing plus compact-support/no-"
            "boundary assumptions imply weak conservation against allowed "
            "tests. It preserves no broad QFT-GR conservation claim, no "
            "source admissibility, no Bianchi compatibility, no semiclassical "
            "Einstein equation, no QFT-GR closure, no empirical validation, "
            "no public submission, and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    lean_attempt_path: Path = LEAN_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions(
        result_review_path=result_review_path,
        lean_attempt_path=lean_attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal positive conservation witness attempt "
            "report under strict toy assumptions."
        )
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument("--lean-attempt", type=Path, default=LEAN_ATTEMPT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review
        if ns.result_review.is_absolute()
        else (REPO_ROOT / ns.result_review)
    )
    lean_attempt_path = (
        ns.lean_attempt if ns.lean_attempt.is_absolute() else (REPO_ROOT / ns.lean_attempt)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions(
        result_review_path=result_review_path,
        lean_attempt_path=lean_attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "attempt_id": payload["attempt_id"],
                "outcome_id": payload["outcome_id"],
                "selected_next_target": payload["selected_next_target"],
                "result_classification": payload["result_classification"],
                "executed": payload["executed"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
