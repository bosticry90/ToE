from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_refinement_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OBSTRUCTION_CLASS,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    REFINEMENT_OBJECTIVE,
    RESULT_CLASSIFICATION as EXPECTED_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-14T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_POST_RETEST_"
    "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_20260614_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_POST_RETEST_"
    "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_POST_RETEST_"
    "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_ACCEPTS_REFINED_CANDIDATE_"
    "AND_AUTHORIZES_BOUNDED_CONSERVATION_RETEST_PACKET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_working_model_refinement_attempt_after_post_retest_"
    "refinement_conservation_retest_refinement_result_review_accepts_refined_candidate_"
    "and_authorizes_bounded_conservation_retest_packet_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "prepare_qft_gr_minimal_working_model_conservation_retest_packet_after_"
    "post_retest_refinement_conservation_retest_refinement_refinement"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_working_model_conservation_retest_packet_after_post_"
    "retest_refinement_conservation_retest_refinement_refinement_preparation_only"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_POST_RETEST_"
        "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_20260614_v0.json"
    )
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The repeated-inconclusive refinement attempt is accepted only "
                "as a refined candidate, so the next bounded action may prepare "
                "a conservation-retest packet for that refined candidate. This "
                "does not execute the retest or admit the source."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": (
                "This repeated-inconclusive refinement-attempt result-review "
                "target is consumed here."
            ),
        },
        {
            "target": (
                "execute_qft_gr_minimal_working_model_conservation_retest_"
                "attempt_after_post_retest_refinement_conservation_retest_refinement_"
                "refinement"
            ),
            "decision": "not_authorized_before_packet_review",
            "reason": (
                "The review authorizes conservation-retest packet preparation "
                "only, not retest execution."
            ),
        },
        {
            "target": (
                "retry_qft_gr_minimal_working_model_conservation_retest_after_"
                "post_retest_refinement_conservation_retest_refinement_refinement"
            ),
            "decision": "not_authorized_by_review_execution_not_packet",
            "reason": (
                "Any retest remains downstream of a prepared and reviewed "
                "post-refinement conservation-retest packet."
            ),
        },
        {
            "target": (
                "prepare_qft_gr_minimal_working_model_countermodel_packet_after_"
                "post_retest_refinement_conservation_retest_refinement_refinement"
            ),
            "decision": "not_selected_no_failed_retest_obstruction",
            "reason": (
                "The prior retest path remains inconclusive and this result "
                "review does not convert it into failure."
            ),
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The toy source remains candidate-only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The review is not a conservation proof.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed or authorized.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": "Bianchi compatibility remains downstream and unclaimed.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "reason": "The semiclassical Einstein equation is not derived here.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR closure remains outside this result review.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def _validation_policy(attempt: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_refinement_attempt_result_review",
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
        "aggregate_lean_health_claimed": False,
        "inherited_attempt_validation_policy": attempt.get("validation_policy", {}),
        "full_suite_required_only_for_target_types": [
            "release_candidate",
            "integration_closeout",
            "aggregate_validation_diagnostic",
            "public_submission_readiness",
            "master_action_promotion_review",
            "governance_manifest_enrollment",
            "shared_test_infrastructure_change",
            "broad_dependency_or_tooling_change",
        ],
    }


def _component_scopes(components: list[dict[str, Any]]) -> set[str]:
    return {row.get("component_scope") for row in components}


def build_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_refinement_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    refined_components = attempt.get("refined_components", [])
    component_scopes = _component_scopes(refined_components)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(attempt)
    attempt_policy = attempt.get("validation_policy", {})

    acceptance_criteria = {
        "consumes_expected_refinement_attempt": attempt.get("schema_id")
        == EXPECTED_ATTEMPT_SCHEMA_ID
        and attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID,
        "attempt_outcome_expected": attempt.get("outcome_id")
        == EXPECTED_ATTEMPT_OUTCOME,
        "attempt_classification_expected": attempt.get("result_classification")
        == EXPECTED_ATTEMPT_CLASSIFICATION,
        "attempt_selected_this_result_review": attempt.get("selected_next_target")
        == CONSUMED_TARGET,
        "bounded_refinement_attempt_executed": attempt.get(
            "bounded_refinement_attempt_executed"
        )
        is True
        and attempt.get(
            "post_retest_refinement_conservation_retest_refinement_attempt_executed"
        )
        is True
        and attempt.get("refinement_attempt_executed") is True
        and attempt.get("model_refinement_executed") is True,
        "obstruction_class_confirmed": attempt.get("obstruction_class")
        == OBSTRUCTION_CLASS,
        "candidate_only_status_preserved": attempt.get("toy_source_candidate_status")
        == "candidate_only_not_source_admissibility"
        and attempt.get("toy_source_candidate_remains_candidate_only") is True,
        "selected_refinement_objective_confirmed": attempt.get(
            "refinement_objective"
        )
        == REFINEMENT_OBJECTIVE
        and attempt.get("selected_refinement_target") == REFINEMENT_OBJECTIVE,
        "refined_components_confirmed": component_scopes
        >= {
            "weak_pairing_domain",
            "regularity_assumptions",
            "test_function_class",
            "candidate_source_definition",
            "scope_restriction",
            "obstruction_accounting",
            "validation_boundary",
        },
        "component_nonclaims_preserved": all(
            row.get("source_admissibility_claimed") is False
            and row.get("conservation_claimed") is False
            for row in refined_components
        ),
        "no_conservation_rerun_or_result_claim": attempt.get(
            "conservation_retest_retried"
        )
        is False
        and attempt.get("conservation_retest_executed_by_attempt") is False
        and attempt.get("conservation_retest_result_claimed") is False
        and attempt.get("conservation_retest_pass_claimed") is False
        and attempt.get("conservation_retest_failure_claimed") is False,
        "no_countermodel_packet_prepared_or_authorized": attempt.get(
            "countermodel_packet_authorized"
        )
        is False
        and attempt.get("countermodel_packet_prepared") is False,
        "no_source_admissibility_claim": attempt.get("source_admissibility_claimed")
        is False
        and attempt.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_claim_proof_or_witness": attempt.get(
            "conservation_claimed"
        )
        is False
        and attempt.get("conservation_proved") is False
        and attempt.get("conservation_proof_object_constructed") is False
        and attempt.get("conservation_witness_constructed") is False,
        "no_bianchi_or_semiclassical_einstein": attempt.get(
            "Bianchi_compatibility_claimed"
        )
        is False
        and attempt.get("semiclassical_einstein_equation_derived") is False,
        "no_qft_gr_closure": attempt.get("qft_gr_seam_closed") is False
        and attempt.get("qft_gr_source_map_closure_claimed") is False,
        "no_empirical_validation_or_public_submission": attempt.get(
            "empirical_validation_claimed"
        )
        is False
        and attempt.get("public_submission_authorized") is False,
        "no_master_action_promotion": attempt.get("master_action_promoted") is False
        and attempt.get("master_action_promotion_authorized") is False,
        "standing_validation_caveats_preserved": attempt.get(
            "release_index_path_not_freshly_lean_validated"
        )
        is True
        and attempt.get("aggregate_lean_not_run") is True
        and attempt.get("aggregate_lean_health_claimed") is False
        and attempt_policy.get("full_pytest_required") is False
        and attempt_policy.get("full_governance_suite_required") is False
        and attempt_policy.get("full_aggregate_lean_required") is False,
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
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_"
            "POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW"
        )
    )

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accepted" if accepted else "rejected",
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_POST_RETEST_"
            "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_REQUIRES_"
            "REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_working_model_refinement_attempt_after_post_retest_"
            "refinement_conservation_retest_refinement_result_review_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_refinement": (
            EXPECTED_ATTEMPT_ID
        ),
        "consumes_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_refinement_pointer": _ptr(
            attempt_path
        ),
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_classification": attempt.get("result_classification"),
        "refinement_attempt_result_review_accepted": accepted,
        "post_retest_refinement_conservation_retest_refinement_attempt_result_review_accepted": (
            accepted
        ),
        "refinement_attempt_executed_confirmed": accepted,
        "bounded_refinement_attempt_executed": attempt.get(
            "bounded_refinement_attempt_executed"
        )
        is True,
        "post_retest_refinement_conservation_retest_refinement_attempt_executed": (
            attempt.get(
                "post_retest_refinement_conservation_retest_refinement_attempt_executed"
            )
            is True
        ),
        "model_refinement_executed_confirmed": accepted,
        "refined_candidate_accepted": accepted,
        "refined_candidate_status": attempt.get("refined_candidate_status"),
        "repeated_inconclusive_signal_preserved": attempt.get(
            "repeated_inconclusive_signal_preserved"
        )
        is True,
        "obstruction_class": OBSTRUCTION_CLASS,
        "candidate_only_status_preserved": accepted,
        "toy_source_candidate_status": attempt.get("toy_source_candidate_status"),
        "toy_source_candidate_remains_candidate_only": accepted,
        "toy_source_promoted_to_admissible_source": False,
        "refinement_objective": REFINEMENT_OBJECTIVE
        if accepted
        else "requires_remediation",
        "selected_refinement_target": REFINEMENT_OBJECTIVE
        if accepted
        else "requires_remediation",
        "selected_refinement_target_count": 1 if accepted else 0,
        "refinement_scope": attempt.get("refinement_scope"),
        "refinement_focus": attempt.get("refinement_focus"),
        "refined_components": refined_components,
        "refined_component_count": len(refined_components),
        "weak_pairing_domain_adjusted": accepted,
        "regularity_assumptions_refined": accepted,
        "regularity_context_refined": accepted,
        "test_function_class_identified": accepted,
        "candidate_source_definition_refined": accepted,
        "scope_restriction_recorded": accepted,
        "obstruction_accounting_recorded": accepted,
        "validation_boundary_preserved": accepted,
        "weak_pairing_domain_id": attempt.get("weak_pairing_domain_id"),
        "regularity_structure_id": attempt.get("regularity_structure_id"),
        "test_function_class_id": attempt.get("test_function_class_id"),
        "candidate_source_definition_id": attempt.get(
            "candidate_source_definition_id"
        ),
        "scope_restriction_id": attempt.get("scope_restriction_id"),
        "obstruction_accounting_id": attempt.get("obstruction_accounting_id"),
        "bounded_conservation_retest_packet_authorized": accepted,
        "conservation_retest_packet_preparation_authorized": accepted,
        "conservation_retest_packet_prepared_by_review": False,
        "conservation_retest_packet_prepared": False,
        "conservation_retest_attempt_authorized": False,
        "conservation_retest_retried": False,
        "conservation_retest_executed_by_review": False,
        "conservation_retest_result_claimed": False,
        "conservation_retest_pass_claimed": False,
        "conservation_retest_failure_claimed": False,
        "countermodel_packet_authorized": False,
        "countermodel_packet_prepared": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "physical_source_claimed": False,
        "conservation_claimed": False,
        "conservation_proved": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
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
        "aggregate_lean_health_claimed": False,
        "validation_policy": validation_policy,
        "validation_posture": {
            "focused_attempt_result_review_current_target_registry_gates": (
                "required_for_checkpoint"
            ),
            "adjacent_minimal_model_nonclaim_gates": "required_bounded_subset",
            "bounded_lean_substitute_result_review_frontier": (
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
            "required for this routine bounded attempt-result-review "
            "checkpoint. The release-index path remains not freshly "
            "Lean-validated, aggregate Lean is not run, and no aggregate Lean "
            "health claim is made. Timeouts remain validation caveats, not "
            "rerun instructions."
        ),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_next_target_count": 1 if accepted else 0,
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_"
            "AFTER_POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_"
            "REFINEMENT_ONLY_"
            "NO_RETEST_EXECUTION_SOURCE_ADMISSIBILITY_CONSERVATION_PROOF_"
            "WITNESS_BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_"
            "VALIDATION_PUBLIC_SUBMISSION_OR_MASTER_ACTION_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the bounded refined candidate "
            "after the repeated-inconclusive conservation-retest refinement "
            "attempt and authorizes conservation-retest packet preparation "
            "only. It does not prepare the packet, execute a retest, infer "
            "conservation success, claim source admissibility, claim "
            "conservation, construct a conservation proof object or witness, "
            "claim Bianchi compatibility, derive the semiclassical Einstein "
            "equation, close QFT-GR, validate empirically, authorize public "
            "submission, or promote the master action. Boundary shorthand: no "
            "source admissibility, no conservation proof object, no "
            "conservation witness, no Bianchi compatibility, no semiclassical "
            "Einstein equation, no QFT-GR closure, and no public submission."
        ),
        "validation_non_escalation_boundary": (
            "Routine packet/review checkpoints use bounded target-relevant "
            "validation only. Full-suite validation is not retried or escalated "
            "unless the checkpoint type requires it. A timeout is recorded as a "
            "validation caveat, not treated as an automatic rerun instruction."
        ),
    }


def write_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_refinement_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_refinement_result_review(
        attempt_path=attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model repeated-inconclusive "
            "refinement-attempt result review."
        )
    )
    parser.add_argument("--attempt", type=Path, default=DEFAULT_ATTEMPT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    attempt_path = ns.attempt if ns.attempt.is_absolute() else (REPO_ROOT / ns.attempt)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_refinement_result_review(
        attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_refinement_attempt_after_post_retest_"
        "refinement_conservation_retest_refinement_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
