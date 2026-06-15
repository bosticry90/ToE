from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    CANONICAL_OBSTRUCTION_ID,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    FAILED_CLASSIFICATION,
    INCONCLUSIVE_CLASSIFICATION,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OBSTRUCTION_STATUS,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_CLASSIFICATION as EXPECTED_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-14T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_UNDER_STRICT_TOY_"
    "ASSUMPTIONS_RESULT_REVIEW_20260614_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_UNDER_STRICT_TOY_"
    "ASSUMPTIONS_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_UNDER_STRICT_TOY_"
    "ASSUMPTIONS_RESULT_REVIEW_ACCEPTS_STRICT_TOY_WITNESS_AND_AUTHORIZES_"
    "WITNESS_MATURATION_PACKET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_"
    "assumptions_result_review_accepts_strict_toy_witness_and_authorizes_"
    "witness_maturation_packet_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "prepare_qft_gr_minimal_positive_conservation_witness_maturation_packet"
NEXT_TARGET_KIND = "qft_gr_minimal_positive_conservation_witness_maturation_packet"
COUNTERMODEL_TARGET = (
    "prepare_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_"
    "obstruction"
)
ASSUMPTION_STABILIZATION_TARGET = (
    "prepare_qft_gr_minimal_positive_conservation_witness_assumption_"
    "stabilization_packet_under_strict_toy_assumptions"
)
SOURCE_MAP_LADDER_TARGET = (
    "prepare_qft_gr_source_map_ladder_packet_from_candidate_source_to_"
    "admissible_source"
)
IMMEDIATE_RETEST_TARGET = (
    "execute_qft_gr_minimal_working_model_conservation_retest_attempt_after_"
    "post_retest_refinement_conservation_retest_refinement_refinement"
)
ORDINARY_REFINEMENT_TARGET = (
    "prepare_qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_refinement"
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / (
        "QFTGRMinimalPositiveConservationWitnessAttemptUnderStrictToyAssumptions"
        "ResultReview.lean"
    )
)
LEAN_REVIEW_NAMESPACE = (
    "ToeFormal.Derivation."
    "QFTGRMinimalPositiveConservationWitnessAttemptUnderStrictToyAssumptions"
    "ResultReview"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_UNDER_STRICT_"
        "TOY_ASSUMPTIONS_RESULT_REVIEW_20260614_v0.json"
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


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The strict toy local conservation bridge witness is accepted "
                "pending maturation; the next packet must analyze how to "
                "mature or discharge its assumptions."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The witness attempt result-review target is consumed here.",
        },
        {
            "target": COUNTERMODEL_TARGET,
            "decision": "retained_follow_on_not_authorized_by_this_review",
            "reason": (
                "Countermodel pressure remains useful if maturation fails or "
                "exposes a no-go route, but it is not selected here."
            ),
        },
        {
            "target": ASSUMPTION_STABILIZATION_TARGET,
            "decision": "subsumed_by_witness_maturation_packet_not_selected",
            "reason": (
                "The accepted witness shifts the burden to maturation of its "
                "assumptions rather than a standalone inconclusive-assumption "
                "stabilization packet."
            ),
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_after_maturation_or_countermodel_pressure",
            "reason": "Source-map ladder reconstruction remains a later follow-on.",
        },
        {
            "target": IMMEDIATE_RETEST_TARGET,
            "decision": "not_authorized",
            "reason": "No broad conservation retest is authorized by this local witness review.",
        },
        {
            "target": ORDINARY_REFINEMENT_TARGET,
            "decision": "not_authorized",
            "reason": "Ordinary same-shaped model refinement remains out of scope.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The accepted strict toy witness is not source admissibility.",
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
            "reason": "The local strict toy witness does not close QFT-GR.",
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


def _validation_policy(attempt: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_positive_conservation_witness_attempt_result_review",
        "routine_attempt_review_uses_bounded_target_relevant_validation_only": True,
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
        "inherited_attempt_validation_policy": attempt.get("validation_policy", {}),
    }


def build_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    lean_review_path: Path = LEAN_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    lean_text = _read_text(lean_review_path)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(attempt)
    lean_result_review_theorem_names = [
        "strict_toy_witness_result_review_accepts_bridge_theorem",
        "strict_toy_witness_result_review_accepts_local_witness_only",
        "strict_toy_witness_result_review_authorizes_maturation_packet_only",
        "strict_toy_witness_result_review_does_not_claim_source_admissibility",
        "strict_toy_witness_result_review_does_not_claim_bianchi_or_semiclassical_einstein",
        "strict_toy_witness_result_review_does_not_close_qft_gr",
        "strict_toy_witness_result_review_no_empirical_public_or_master_action_promotion",
    ]
    lean_review_confirms_theorem = all(
        marker in lean_text
        for marker in [
            "import ToeFormal.Derivation.QFTGRMinimalPositiveConservationWitnessAttemptUnderStrictToyAssumptions",
            "theorem strict_toy_witness_result_review_accepts_bridge_theorem",
            "strict_toy_weak_conservation_witness",
            "weakConservationAgainstAllowedTests",
            "selectedMinimalPositiveConservationWitnessMaturationPacketTarget",
        ]
    )

    acceptance_criteria = {
        "consumes_expected_strict_toy_witness_attempt": (
            attempt.get("schema_id") == EXPECTED_ATTEMPT_SCHEMA_ID
            and attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID
            and attempt.get("outcome_id") == EXPECTED_ATTEMPT_OUTCOME
            and attempt.get("result_classification") == EXPECTED_ATTEMPT_CLASSIFICATION
            and attempt.get("selected_next_target") == CONSUMED_TARGET
        ),
        "attempt_classification_is_achieved_not_failed_or_inconclusive": (
            attempt.get("result_classification") == EXPECTED_ATTEMPT_CLASSIFICATION
            and attempt.get("selected_classification") == EXPECTED_ATTEMPT_CLASSIFICATION
            and FAILED_CLASSIFICATION in attempt.get("classification_options", [])
            and INCONCLUSIVE_CLASSIFICATION in attempt.get("classification_options", [])
            and attempt.get("failed_classification_not_selected") is True
            and attempt.get("inconclusive_classification_not_selected") is True
        ),
        "attempt_is_theorem_bearing_strict_toy_witness": (
            attempt.get("theorem_bearing_attempt") is True
            and attempt.get("strict_toy_weak_conservation_witness_achieved") is True
            and attempt.get("strict_toy_weak_conservation_theorem_constructed") is True
            and attempt.get("weak_conservation_against_allowed_tests_proved") is True
            and attempt.get("lean_contains_required_shape") is True
        ),
        "result_review_lean_reuses_attempt_theorem": lean_review_confirms_theorem
        and all(f"theorem {name}" in lean_text for name in lean_result_review_theorem_names),
        "bridge_scope_is_local_and_strict_toy_only": (
            attempt.get("strict_toy_assumptions_only") is True
            and attempt.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
            and attempt.get("dominant_obstruction_candidate")
            == DOMINANT_OBSTRUCTION_CANDIDATE
            and attempt.get("canonical_obstruction_id") == CANONICAL_OBSTRUCTION_ID
            and attempt.get("obstruction_status") == OBSTRUCTION_STATUS
            and attempt.get("dominant_obstruction_resolved") is False
        ),
        "review_selects_maturation_packet_only": _selected_targets(
            candidate_next_targets
        )
        == [NEXT_TARGET],
        "no_immediate_retest_countermodel_or_source_map_selected": (
            all(
                row["decision"] != "selected"
                for row in candidate_next_targets
                if row["target"]
                in {
                    IMMEDIATE_RETEST_TARGET,
                    ORDINARY_REFINEMENT_TARGET,
                    COUNTERMODEL_TARGET,
                    SOURCE_MAP_LADDER_TARGET,
                    ASSUMPTION_STABILIZATION_TARGET,
                }
            )
        ),
        "no_broad_conservation_or_source_admissibility_claim": (
            attempt.get("conservation_claimed") is False
            and attempt.get("conservation_proved") is False
            and attempt.get("conservation_proof_object_constructed") is False
            and attempt.get("conservation_witness_constructed") is False
            and attempt.get("full_qft_gr_conservation_claimed") is False
            and attempt.get("unbounded_conservation_proved") is False
            and attempt.get("source_admissibility_claimed") is False
            and attempt.get("stress_energy_source_admissibility_claimed") is False
        ),
        "no_bianchi_semiclassical_qft_gr_closure_empirical_or_promotion": (
            attempt.get("Bianchi_compatibility_claimed") is False
            and attempt.get("semiclassical_einstein_equation_derived") is False
            and attempt.get("qft_gr_seam_closed") is False
            and attempt.get("qft_gr_source_map_closure_claimed") is False
            and attempt.get("empirical_validation_claimed") is False
            and attempt.get("public_submission_authorized") is False
            and attempt.get("master_action_promoted") is False
            and attempt.get("master_action_promotion_authorized") is False
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
            "RESULT_REVIEW_UNDER_STRICT_TOY_ASSUMPTIONS"
        )
    )

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accepted" if accepted else "requires_remediation",
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_UNDER_"
            "STRICT_TOY_ASSUMPTIONS_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_positive_conservation_witness_attempt_under_strict_"
            "toy_assumptions_result_review_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_positive_conservation_witness_attempt": (
            EXPECTED_ATTEMPT_ID
        ),
        "consumes_qft_gr_minimal_positive_conservation_witness_attempt_pointer": _ptr(
            attempt_path
        ),
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_classification": attempt.get("result_classification"),
        "strict_toy_witness_attempt_result_review_accepted": accepted,
        "strict_toy_witness_accepted": accepted,
        "local_conservation_bridge_witness_accepted": accepted,
        "local_conservation_bridge_witness_constructed": attempt.get(
            "strict_toy_weak_conservation_witness_achieved"
        ),
        "strict_toy_weak_conservation_witness_achieved": attempt.get(
            "strict_toy_weak_conservation_witness_achieved"
        ),
        "strict_toy_weak_conservation_theorem_constructed": attempt.get(
            "strict_toy_weak_conservation_theorem_constructed"
        ),
        "weak_conservation_against_allowed_tests_proved": attempt.get(
            "weak_conservation_against_allowed_tests_proved"
        ),
        "theorem_bearing_attempt": attempt.get("theorem_bearing_attempt"),
        "theorem_bearing_result_review": lean_review_confirms_theorem,
        "lean_result_review_file": _ptr(lean_review_path),
        "lean_result_review_namespace": LEAN_REVIEW_NAMESPACE,
        "lean_result_review_theorem_names": lean_result_review_theorem_names,
        "strict_toy_assumptions_only": True,
        "local_witness_scope": "strict_toy_local_weak_conservation_bridge_witness_only",
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "theorem_shape": attempt.get("theorem_shape"),
        "proof_strategy": attempt.get("proof_strategy"),
        "allowed_weak_test_class_id": attempt.get("allowed_weak_test_class_id"),
        "weak_pairing_id": attempt.get("weak_pairing_id"),
        "source_object_id": attempt.get("source_object_id"),
        "divergence_pairing_id": attempt.get("divergence_pairing_id"),
        "field_equation_residual_id": attempt.get("field_equation_residual_id"),
        "divergence_identity_id": attempt.get("divergence_identity_id"),
        "no_boundary_condition_id": attempt.get("no_boundary_condition_id"),
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": OBSTRUCTION_STATUS,
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "maturation_packet_authorized": accepted,
        "witness_maturation_packet_authorized_only": accepted,
        "maturation_packet_prepared": False,
        "positive_witness_attempt_executed": True,
        "positive_witness_attempt_result_reviewed": accepted,
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
            "focused_result_review_current_target_registry_gate": (
                "required_for_checkpoint"
            ),
            "adjacent_minimal_model_nonclaim_gates": "required_bounded_subset",
            "targeted_lean_result_review_frontier_import_checks": (
                "required_for_checkpoint"
            ),
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
            "required for this routine bounded witness-attempt result-review "
            "checkpoint. The release-index path remains not freshly Lean-"
            "validated, aggregate Lean is not run, and no aggregate Lean health "
            "claim is made."
        ),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_MATURATION_"
            "PACKET_ONLY_NO_IMMEDIATE_RETEST_NO_COUNTERMODEL_SELECTION_NO_SOURCE_"
            "ADMISSIBILITY_NO_BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_"
            "EMPIRICAL_VALIDATION_PUBLIC_SUBMISSION_OR_MASTER_ACTION_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the strict toy local weak-"
            "conservation bridge witness. It confirms that the theorem-shaped "
            "strict toy implication was constructed, then routes only to a "
            "witness maturation packet. It preserves no broad QFT-GR "
            "conservation claim, no source admissibility, no Bianchi "
            "compatibility, no semiclassical Einstein equation, no QFT-GR "
            "closure, no empirical validation, no public submission, and no "
            "master-action promotion."
        ),
    }


def write_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    lean_review_path: Path = LEAN_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_result_review(
        attempt_path=attempt_path,
        lean_review_path=lean_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal positive conservation witness attempt "
            "result review under strict toy assumptions."
        )
    )
    parser.add_argument("--attempt", type=Path, default=DEFAULT_ATTEMPT_PATH)
    parser.add_argument("--lean-review", type=Path, default=LEAN_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    attempt_path = ns.attempt if ns.attempt.is_absolute() else (REPO_ROOT / ns.attempt)
    lean_review_path = (
        ns.lean_review if ns.lean_review.is_absolute() else (REPO_ROOT / ns.lean_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_result_review(
        attempt_path=attempt_path,
        lean_review_path=lean_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "review_id": payload["review_id"],
                "outcome_id": payload["outcome_id"],
                "selected_next_target": payload["selected_next_target"],
                "accepted": payload["accepted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
