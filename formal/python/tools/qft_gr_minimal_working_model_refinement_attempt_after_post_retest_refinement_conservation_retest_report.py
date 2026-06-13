from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_result_review_report import (
    DEFAULT_OUT as DEFAULT_PACKET_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OBSTRUCTION_CLASS,
    OUTCOME_ID as EXPECTED_PACKET_RESULT_REVIEW_OUTCOME,
    REFINEMENT_OBJECTIVE,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_PACKET_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_PACKET_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_PACKET_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-13T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_POST_RETEST_"
    "REFINEMENT_CONSERVATION_RETEST_20260613_v0"
)
ATTEMPT_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_POST_RETEST_"
    "REFINEMENT_CONSERVATION_RETEST_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_POST_RETEST_"
    "REFINEMENT_CONSERVATION_RETEST_EXECUTED_WITH_NO_SOURCE_ADMISSIBILITY_"
    "OR_CONSERVATION_PROOF"
)
RESULT_CLASSIFICATION = (
    "qft_gr_minimal_working_model_refinement_attempt_after_post_retest_"
    "refinement_conservation_retest_executed_with_refined_candidate_pending_"
    "result_review"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "review_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_"
    "refinement_conservation_retest_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_working_model_refinement_attempt_after_post_retest_"
    "refinement_conservation_retest_result_review"
)
REFINEMENT_SCOPE = (
    "post_retest_refinement_conservation_retest_repeated_inconclusive_weak_"
    "pairing_domain_regular_context_test_function_class_candidate_definition_"
    "scope_restriction_without_source_admissibility"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_POST_RETEST_"
        "REFINEMENT_CONSERVATION_RETEST_20260613_v0.json"
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
                "The bounded refinement attempt has been executed and must be "
                "result-reviewed before any conservation retest, countermodel "
                "packet, source-admissibility claim, proof construction, or "
                "model promotion."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": (
                "This repeated-inconclusive refinement-attempt execution target "
                "is consumed here."
            ),
        },
        {
            "target": (
                "execute_qft_gr_minimal_working_model_conservation_retest_"
                "attempt_after_post_retest_refinement"
            ),
            "decision": "not_authorized_pending_attempt_result_review",
            "reason": "This execution records refinement only, not a conservation rerun.",
        },
        {
            "target": (
                "prepare_qft_gr_minimal_working_model_countermodel_packet_after_"
                "post_retest_refinement_conservation_retest"
            ),
            "decision": "not_authorized_pending_attempt_result_review",
            "reason": (
                "The attempt does not convert repeated inconclusive retests "
                "into an explicit failed-retest countermodel obstruction."
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
            "reason": "The refinement attempt is not a conservation proof.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed by this attempt.",
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
            "reason": "QFT-GR closure remains outside this bounded attempt.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def _validation_policy(review: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_refinement_attempt_execution",
        "routine_checkpoint_uses_bounded_target_relevant_validation_only": True,
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
        "inherited_packet_result_review_validation_policy": review.get(
            "validation_policy", {}
        ),
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


def _refined_components() -> list[dict[str, Any]]:
    return [
        {
            "component_id": "toy_weak_pairing_domain_v3_candidate",
            "component_scope": "weak_pairing_domain",
            "source_dimension_id": "repeat_retest_weak_pairing_domain",
            "obstruction_class": OBSTRUCTION_CLASS,
            "refinement_action": (
                "record the narrower v3 candidate weak-pairing domain with "
                "explicit admitted and blocked toy test-vector pairings"
            ),
            "status_after_attempt": (
                "v3_candidate_pairing_domain_refined_not_source_admissibility"
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "component_id": "toy_regular_context_v3_candidate",
            "component_scope": "regularity_assumptions",
            "source_dimension_id": "repeat_retest_regular_context",
            "obstruction_class": OBSTRUCTION_CLASS,
            "refinement_action": (
                "separate derivative exchange, regularization, boundary-term, "
                "and limit/interchange assumptions into explicit v3 candidate "
                "clauses"
            ),
            "status_after_attempt": (
                "v3_regular_context_refined_as_assumption_not_theorem_discharge"
            ),
            "regularity_discharge_claimed": False,
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "component_id": "toy_conservation_test_function_class_v2_candidate",
            "component_scope": "test_function_class",
            "source_dimension_id": "repeat_retest_test_function_class",
            "obstruction_class": OBSTRUCTION_CLASS,
            "refinement_action": (
                "refine the toy compact-support or admissible test-vector class "
                "for later weak-divergence discrimination"
            ),
            "status_after_attempt": "v2_test_class_refined_not_conservation_test",
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "component_id": "toy_source_candidate_definition_v3_candidate",
            "component_scope": "candidate_source_definition",
            "source_dimension_id": "repeat_retest_candidate_source_definition",
            "obstruction_class": OBSTRUCTION_CLASS,
            "refinement_action": (
                "name the v3 candidate-source definition and separate candidate "
                "data from admissibility witnesses"
            ),
            "status_after_attempt": (
                "v3_candidate_definition_refined_not_admitted_source"
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "component_id": "bounded_toy_weak_pairing_scope_v3",
            "component_scope": "scope_restriction",
            "source_dimension_id": "repeat_retest_scope_restriction",
            "obstruction_class": OBSTRUCTION_CLASS,
            "refinement_action": (
                "restrict interpretation to the bounded toy weak-pairing scope "
                "unless a reviewed packet later authorizes broader semantics"
            ),
            "status_after_attempt": "v3_scope_restricted_no_qft_gr_closure",
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "component_id": "repeated_inconclusive_obstruction_account_v2",
            "component_scope": "obstruction_accounting",
            "source_dimension_id": "repeat_retest_obstruction_accounting",
            "obstruction_class": OBSTRUCTION_CLASS,
            "refinement_action": (
                "preserve repeated inconclusive conservation retests as an "
                "obstruction map and anti-loop signal"
            ),
            "status_after_attempt": (
                "repeated_inconclusive_result_preserved_as_obstruction_account"
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "component_id": "bounded_validation_boundary_v2",
            "component_scope": "validation_boundary",
            "source_dimension_id": "repeat_retest_validation_boundary",
            "obstruction_class": OBSTRUCTION_CLASS,
            "refinement_action": (
                "preserve bounded validation and standing Lean caveats without "
                "turning timeouts into retry loops"
            ),
            "status_after_attempt": "validation_non_escalation_boundary_preserved",
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
    ]


def _component_scopes(components: list[dict[str, Any]]) -> set[str]:
    return {row["component_scope"] for row in components}


def build_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(packet_result_review_path)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(review)
    refined_components = _refined_components()
    component_scopes = _component_scopes(refined_components)
    review_policy = review.get("validation_policy", {})

    acceptance_criteria = {
        "consumes_expected_packet_result_review": review.get("schema_id")
        == EXPECTED_PACKET_RESULT_REVIEW_SCHEMA_ID
        and review.get("review_id") == EXPECTED_PACKET_RESULT_REVIEW_ID,
        "packet_result_review_outcome_expected": review.get("outcome_id")
        == EXPECTED_PACKET_RESULT_REVIEW_OUTCOME,
        "packet_result_review_classification_expected": review.get(
            "result_review_classification"
        )
        == EXPECTED_PACKET_RESULT_REVIEW_CLASSIFICATION,
        "packet_result_review_selected_this_attempt": review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "bounded_attempt_authorized_not_executed_by_review": review.get(
            "bounded_refinement_attempt_authorized"
        )
        is True
        and review.get("refinement_attempt_authorized") is True
        and review.get("bounded_refinement_attempt_executed_by_review") is False
        and review.get("refinement_attempt_executed") is False,
        "obstruction_class_confirmed": review.get("obstruction_class")
        == OBSTRUCTION_CLASS,
        "candidate_only_status_preserved_by_review": review.get(
            "toy_source_candidate_status"
        )
        == "candidate_only_not_source_admissibility"
        and review.get("toy_source_candidate_remains_candidate_only") is True,
        "selected_refinement_objective_confirmed": review.get(
            "refinement_objective"
        )
        == REFINEMENT_OBJECTIVE
        and review.get("selected_refinement_target") == REFINEMENT_OBJECTIVE,
        "authorized_components_refined": component_scopes
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
            row["source_admissibility_claimed"] is False
            and row["conservation_claimed"] is False
            for row in refined_components
        ),
        "no_conservation_rerun_or_result_claim": review.get(
            "conservation_retest_retried"
        )
        is False
        and review.get("conservation_retest_result_claimed") is False
        and review.get("conservation_retest_pass_claimed") is False
        and review.get("conservation_retest_failure_claimed") is False,
        "no_countermodel_packet_selected": review.get(
            "countermodel_packet_authorized"
        )
        is False
        and review.get("countermodel_packet_prepared") is False,
        "no_source_admissibility_claim": review.get("source_admissibility_claimed")
        is False
        and review.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_claim_proof_or_witness": review.get(
            "conservation_claimed"
        )
        is False
        and review.get("conservation_proved") is False
        and review.get("conservation_proof_object_constructed") is False
        and review.get("conservation_witness_constructed") is False,
        "no_bianchi_or_semiclassical_einstein": review.get(
            "Bianchi_compatibility_claimed"
        )
        is False
        and review.get("semiclassical_einstein_equation_derived") is False,
        "no_qft_gr_closure": review.get("qft_gr_seam_closed") is False
        and review.get("qft_gr_source_map_closure_claimed") is False,
        "no_empirical_validation_or_public_submission": review.get(
            "empirical_validation_claimed"
        )
        is False
        and review.get("public_submission_authorized") is False,
        "no_master_action_promotion": review.get("master_action_promoted") is False
        and review.get("master_action_promotion_authorized") is False,
        "standing_validation_caveats_preserved": review.get(
            "release_index_path_not_freshly_lean_validated"
        )
        is True
        and review.get("aggregate_lean_not_run") is True
        and review.get("aggregate_lean_health_claimed") is False
        and review_policy.get("full_pytest_required") is False
        and review_policy.get("full_governance_suite_required") is False
        and review_policy.get("full_aggregate_lean_required") is False,
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
    executed = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "attempt_id": ATTEMPT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": executed,
        "executed": executed,
        "attempt_executed": executed,
        "bounded_refinement_attempt_executed": executed,
        "post_retest_refinement_conservation_retest_refinement_attempt_executed": (
            executed
        ),
        "refinement_attempt_executed": executed,
        "model_refinement_executed": executed,
        "outcome_id": OUTCOME_ID
        if executed
        else (
            "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_POST_"
            "RETEST_REFINEMENT_CONSERVATION_RETEST_REQUIRES_REMEDIATION"
        ),
        "result_classification": RESULT_CLASSIFICATION
        if executed
        else (
            "qft_gr_minimal_working_model_refinement_attempt_after_post_retest_"
            "refinement_conservation_retest_requires_remediation"
        ),
        "attempt_classification": RESULT_CLASSIFICATION
        if executed
        else (
            "qft_gr_minimal_working_model_refinement_attempt_after_post_retest_"
            "refinement_conservation_retest_requires_remediation"
        ),
        "result_classification_count": 1 if executed else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_refinement_packet_result_review": (
            EXPECTED_PACKET_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_minimal_working_model_refinement_packet_result_review_pointer": _ptr(
            packet_result_review_path
        ),
        "consumed_packet_result_review_outcome_id": review.get("outcome_id"),
        "consumed_packet_result_review_classification": review.get(
            "result_review_classification"
        ),
        "repeated_inconclusive_signal_preserved": executed,
        "obstruction_class": OBSTRUCTION_CLASS,
        "candidate_only_status_preserved": executed,
        "toy_source_candidate_status": "candidate_only_not_source_admissibility",
        "toy_source_candidate_remains_candidate_only": True,
        "toy_source_promoted_to_admissible_source": False,
        "refined_candidate_status": (
            "post_retest_refinement_conservation_retest_refined_toy_candidate_"
            "pending_result_review"
        )
        if executed
        else "requires_remediation",
        "refinement_objective": REFINEMENT_OBJECTIVE
        if executed
        else "requires_remediation",
        "selected_refinement_target": REFINEMENT_OBJECTIVE
        if executed
        else "requires_remediation",
        "selected_refinement_target_count": 1 if executed else 0,
        "refinement_scope": REFINEMENT_SCOPE,
        "refinement_focus": review.get("refinement_focus"),
        "refined_components": refined_components,
        "refined_component_count": len(refined_components),
        "weak_pairing_domain_adjusted": executed,
        "regularity_assumptions_refined": executed,
        "regularity_context_refined": executed,
        "test_function_class_identified": executed,
        "candidate_source_definition_refined": executed,
        "scope_restriction_recorded": executed,
        "obstruction_accounting_recorded": executed,
        "validation_boundary_preserved": executed,
        "weak_pairing_domain_id": "toy_weak_pairing_domain_v3_candidate",
        "regularity_structure_id": "toy_regular_context_v3_candidate",
        "test_function_class_id": "toy_conservation_test_function_class_v2_candidate",
        "candidate_source_definition_id": "toy_source_candidate_definition_v3_candidate",
        "scope_restriction_id": "bounded_toy_weak_pairing_scope_v3",
        "obstruction_accounting_id": "repeated_inconclusive_obstruction_account_v2",
        "model_refinement_packet_prepared": review.get("model_refinement_packet_prepared")
        is True,
        "bounded_refinement_attempt_result_review_pending": executed,
        "refinement_attempt_result_review_pending": executed,
        "conservation_retest_retried": False,
        "conservation_retest_executed_by_attempt": False,
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
            "focused_attempt_current_target_registry_gates": "required_for_checkpoint",
            "adjacent_minimal_model_nonclaim_gates": "required_bounded_subset",
            "bounded_lean_substitute_attempt_frontier": "required_for_checkpoint",
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
            "required for this routine bounded attempt-execution checkpoint. "
            "The release-index path remains not freshly Lean-validated, "
            "aggregate Lean is not run, and no aggregate Lean health claim is "
            "made. Timeouts remain validation caveats, not rerun instructions."
        ),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if executed
        else (
            "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_"
            "POST_RETEST_REFINEMENT_CONSERVATION_RETEST"
        ),
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_next_target_count": 1 if executed else 0,
        "selection_count": 1 if executed else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_POST_"
            "RETEST_REFINEMENT_CONSERVATION_RETEST_RESULT_ONLY_NO_CONSERVATION_"
            "RERUN_COUNTERMODEL_PACKET_SOURCE_ADMISSIBILITY_CONSERVATION_PROOF_"
            "WITNESS_BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_"
            "VALIDATION_PUBLIC_SUBMISSION_OR_MASTER_ACTION_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This bounded refinement attempt executes only the authorized "
            "repeated-inconclusive obstruction-class refinement of weak pairing "
            "domain, regularity assumptions, test-function class, candidate "
            "source definition, scope restriction, obstruction accounting, and "
            "validation boundary for the toy candidate. It does not rerun "
            "conservation, does not claim conservation, constructs no "
            "conservation proof object or conservation witness, claims no "
            "source admissibility, claims no Bianchi compatibility, derives no "
            "semiclassical Einstein equation, closes no QFT-GR seam, validates "
            "nothing empirically, authorizes no public submission, and promotes "
            "no master action. Boundary shorthand: no source admissibility, no "
            "conservation proof object, no conservation witness, no Bianchi "
            "compatibility, no semiclassical Einstein equation, no QFT-GR "
            "closure, and no public submission."
        ),
    }


def write_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest(
        packet_result_review_path=packet_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model repeated-inconclusive "
            "bounded refinement attempt report."
        )
    )
    parser.add_argument("--review", type=Path, default=DEFAULT_PACKET_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest(
        packet_result_review_path=review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_refinement_attempt_after_post_retest_"
        "refinement_conservation_retest_report: "
        f"executed={payload['executed']} "
        f"classification={payload['result_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
