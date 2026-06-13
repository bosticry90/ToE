from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OBSTRUCTION_CLASS,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    REFINEMENT_OBJECTIVE,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-13T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_AFTER_POST_"
    "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_20260613_v0"
)
PACKET_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_AFTER_POST_"
    "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_AFTER_POST_"
    "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_PREPARED_WITH_NO_"
    "CONSERVATION_PROOF_OR_SOURCE_ADMISSIBILITY"
)
PACKET_CLASSIFICATION = (
    "qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_prepared_pending_result_review"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "review_qft_gr_minimal_working_model_conservation_retest_packet_after_"
    "post_retest_refinement_conservation_retest_refinement_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_result_review"
)
RETEST_CONDITION_ID = (
    "weak_distributional_covariant_conservation_for_post_retest_refinement_"
    "conservation_retest_refined_toy_candidate"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_AFTER_POST_"
        "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_20260613_v0.json"
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


def _component_by_scope(
    components: list[dict[str, Any]], scope: str
) -> dict[str, Any]:
    for row in components:
        if row.get("component_scope") == scope:
            return row
    raise KeyError(f"Missing refined component scope: {scope}")


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The v3 post-retest-refinement conservation-retest packet must "
                "be reviewed before any retest execution or conservation "
                "result claim is authorized."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": (
                "This conservation-retest packet preparation target is "
                "consumed here."
            ),
        },
        {
            "target": (
                "execute_qft_gr_minimal_working_model_conservation_retest_"
                "attempt_after_post_retest_refinement_conservation_retest_"
                "refinement"
            ),
            "decision": "not_authorized_before_packet_result_review",
            "reason": "This packet defines the retest only; it does not execute it.",
        },
        {
            "target": (
                "retry_qft_gr_minimal_working_model_conservation_retest_after_"
                "post_retest_refinement_conservation_retest_refinement"
            ),
            "decision": "not_authorized_before_packet_result_review",
            "reason": (
                "Any retest remains downstream of a prepared packet result "
                "review."
            ),
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The v3 toy source remains candidate-only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "Packet preparation is not a conservation proof.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed by packet preparation.",
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
            "reason": "QFT-GR closure remains outside this packet.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def _validation_policy(review: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_conservation_retest_packet_preparation",
        "routine_packet_uses_bounded_target_relevant_validation_only": True,
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
        "inherited_result_review_validation_policy": review.get(
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


def _newest_refinement_delta(review: dict[str, Any]) -> dict[str, Any]:
    components = review.get("refined_components", [])
    weak_pairing = _component_by_scope(components, "weak_pairing_domain")
    regularity = _component_by_scope(components, "regularity_assumptions")
    test_class = _component_by_scope(components, "test_function_class")
    candidate_definition = _component_by_scope(
        components, "candidate_source_definition"
    )
    scope_restriction = _component_by_scope(components, "scope_restriction")
    obstruction = _component_by_scope(components, "obstruction_accounting")
    validation = _component_by_scope(components, "validation_boundary")
    return {
        "delta_id": (
            "post_retest_refinement_conservation_retest_refined_toy_candidate_"
            "delta_v3"
        ),
        "refinement_objective": review.get("refinement_objective"),
        "obstruction_class": review.get("obstruction_class"),
        "changed_after_repeated_inconclusive_retests": [
            {
                "component": "weak_pairing_domain",
                "component_id": weak_pairing.get("component_id"),
                "effect_on_retest": (
                    "Retest only weak covariant-divergence pairings admitted "
                    "by the v3 candidate weak-pairing domain."
                ),
                "source_admissibility_claimed": False,
                "conservation_claimed": False,
            },
            {
                "component": "regularity_assumptions",
                "component_id": regularity.get("component_id"),
                "effect_on_retest": (
                    "Retest derivative-exchange, regularization, boundary-term, "
                    "and limit/interchange clauses only where the v3 regularity "
                    "context admits them."
                ),
                "regularity_discharge_claimed": False,
                "source_admissibility_claimed": False,
                "conservation_claimed": False,
            },
            {
                "component": "test_function_class",
                "component_id": test_class.get("component_id"),
                "effect_on_retest": (
                    "Use the v2 toy compact-support or admissible test-vector "
                    "class for the future weak-divergence matrix."
                ),
                "source_admissibility_claimed": False,
                "conservation_claimed": False,
            },
            {
                "component": "candidate_source_definition",
                "component_id": candidate_definition.get("component_id"),
                "effect_on_retest": (
                    "Retest the v3 candidate source definition only, without "
                    "promoting it to an admissible stress-energy source."
                ),
                "source_admissibility_claimed": False,
                "conservation_claimed": False,
            },
            {
                "component": "scope_restriction",
                "component_id": scope_restriction.get("component_id"),
                "effect_on_retest": (
                    "Restrict interpretation to the bounded v3 toy "
                    "weak-pairing scope."
                ),
                "qft_gr_closure_claimed": False,
            },
            {
                "component": "obstruction_accounting",
                "component_id": obstruction.get("component_id"),
                "effect_on_retest": (
                    "Carry repeated inconclusive retests as obstruction "
                    "accounting and an anti-loop signal, not as a pass or "
                    "failure."
                ),
                "conservation_claimed": False,
            },
            {
                "component": "validation_boundary",
                "component_id": validation.get("component_id"),
                "effect_on_retest": (
                    "Preserve bounded validation and standing Lean caveats "
                    "without converting timeout caveats into retest retry "
                    "instructions."
                ),
                "conservation_retest_executed": False,
            },
        ],
        "unchanged_boundaries": [
            "toy_source_candidate_status_remains_candidate_only",
            "fixed_background_only",
            "no_backreaction_or_semiclassical_einstein_equation",
            "no_Bianchi_compatibility",
            "no_source_admissibility",
            "no_QFT_GR_closure",
            "no_conservation_claim_before_retest_execution_and_review",
        ],
    }


def _retest_condition(review: dict[str, Any]) -> dict[str, Any]:
    return {
        "condition_id": RETEST_CONDITION_ID,
        "condition_being_retested": (
            "Weak distributional covariant conservation of the v3 "
            "post-retest-refinement toy stress-energy-like candidate under "
            "the v3 weak pairing domain, v3 regularity context, and v2 "
            "test-function class."
        ),
        "statement_template": (
            "For every retest-admitted compactly supported test vector field X, "
            "with pairings admitted by toy_weak_pairing_domain_v3_candidate "
            "and derivative, regularization, boundary-term, or limit operations "
            "admitted by toy_regular_context_v3_candidate, the weak pairing "
            "<div_g(T_post_retest_refinement_conservation_retest_refined_v3), X> "
            "must vanish; otherwise record the first explicit obstruction."
        ),
        "refined_artifact_status": review.get("refined_candidate_status"),
        "weak_pairing_domain_id": "toy_weak_pairing_domain_v3_candidate",
        "regularity_structure_id": "toy_regular_context_v3_candidate",
        "test_function_class_id": "toy_conservation_test_function_class_v2_candidate",
        "candidate_source_definition_id": "toy_source_candidate_definition_v3_candidate",
        "fixed_background_only": True,
        "strong_pointwise_conservation_claimed": False,
        "global_conservation_claimed": False,
        "retest_executed": False,
    }


def _pass_fail_inconclusive_criteria() -> dict[str, list[str]]:
    return {
        "pass": [
            (
                "every retest-admitted weak pairing is defined under "
                "toy_weak_pairing_domain_v3_candidate"
            ),
            (
                "every derivative, divergence, regularization, boundary-term, "
                "and limit/interchange step used by the weak pairing is "
                "admitted by toy_regular_context_v3_candidate"
            ),
            (
                "every compact-support or admissible test-vector pairing in "
                "toy_conservation_test_function_class_v2_candidate evaluates "
                "the weak divergence to zero without adding an unrecorded "
                "assumption"
            ),
            "no v3 post-refinement retest obstruction row is triggered",
        ],
        "fail": [
            (
                "a v3 admitted weak divergence pairing is explicitly nonzero "
                "under the packet's test-function class"
            ),
            (
                "a required pairing remains undefined inside "
                "toy_weak_pairing_domain_v3_candidate"
            ),
            (
                "a required derivative, divergence, regularization, boundary, "
                "or limit/interchange step remains blocked inside "
                "toy_regular_context_v3_candidate"
            ),
        ],
        "inconclusive": [
            (
                "the retest cannot decide zero versus nonzero under only the "
                "v3 packet assumptions"
            ),
            (
                "the retest requires stronger pairing-domain, regularity, "
                "source-domain membership, or Bianchi compatibility assumptions "
                "than this packet may add"
            ),
            (
                "the weak retest remains separable from strong pointwise "
                "conservation only by preserving candidate-only status"
            ),
        ],
    }


def _pass_boundary() -> list[str]:
    return [
        (
            "A future pass would establish only that the v3 toy candidate "
            "passes this packet's weak distributional retest on the fixed "
            "background."
        ),
        (
            "A future pass would not establish full source-domain membership, "
            "stress-energy source admissibility, or physical-source status."
        ),
        (
            "A future pass would not establish Bianchi compatibility or derive "
            "a semiclassical Einstein equation."
        ),
        (
            "A future pass would not close QFT-GR, authorize empirical "
            "validation, authorize public submission, or promote the master "
            "action."
        ),
    ]


def build_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(result_review_path)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(review)
    review_policy = review.get("validation_policy", {})
    refinement_delta = _newest_refinement_delta(review)
    retest_condition = _retest_condition(review)
    pass_fail_inconclusive_criteria = _pass_fail_inconclusive_criteria()
    pass_boundary = _pass_boundary()

    acceptance_criteria = {
        "consumes_expected_result_review": review.get("schema_id")
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID
        and review.get("review_id") == EXPECTED_RESULT_REVIEW_ID,
        "result_review_outcome_expected": review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_classification_expected": review.get(
            "result_review_classification"
        )
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION,
        "result_review_selected_this_packet": review.get("selected_next_target")
        == CONSUMED_TARGET,
        "packet_preparation_authorized_only": review.get(
            "bounded_conservation_retest_packet_authorized"
        )
        is True
        and review.get("conservation_retest_packet_preparation_authorized") is True
        and review.get("conservation_retest_packet_prepared") is False
        and review.get("conservation_retest_attempt_authorized") is False,
        "candidate_only_status_preserved": review.get("toy_source_candidate_status")
        == "candidate_only_not_source_admissibility"
        and review.get("toy_source_candidate_remains_candidate_only") is True,
        "refined_candidate_components_available": {
            row.get("component_scope") for row in review.get("refined_components", [])
        }
        >= {
            "weak_pairing_domain",
            "regularity_assumptions",
            "test_function_class",
            "candidate_source_definition",
            "scope_restriction",
            "obstruction_accounting",
            "validation_boundary",
        },
        "newest_refinement_delta_defined": len(
            refinement_delta["changed_after_repeated_inconclusive_retests"]
        )
        == 7,
        "retest_condition_defined": retest_condition.get("condition_id")
        == RETEST_CONDITION_ID,
        "pass_fail_inconclusive_defined": set(pass_fail_inconclusive_criteria)
        == {"pass", "fail", "inconclusive"},
        "pass_boundary_records_no_source_or_closure": len(pass_boundary) == 4,
        "no_retest_execution": retest_condition.get("retest_executed") is False,
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
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else (
            "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_"
            "PACKET_AFTER_POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT"
        )
    )

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": prepared,
        "packet_prepared": prepared,
        "retest_packet_prepared": prepared,
        "packet_preparation_only": True,
        "post_retest_refinement_conservation_retest_refinement_retest_packet_prepared": (
            prepared
        ),
        "conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_prepared": (
            prepared
        ),
        "outcome_id": OUTCOME_ID
        if prepared
        else (
            "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_AFTER_"
            "POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REQUIRES_"
            "REMEDIATION"
        ),
        "packet_classification": PACKET_CLASSIFICATION
        if prepared
        else (
            "qft_gr_minimal_working_model_conservation_retest_packet_after_"
            "post_retest_refinement_conservation_retest_refinement_requires_"
            "remediation"
        ),
        "packet_classification_count": 1 if prepared else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_result_review": (
            EXPECTED_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_schema_id": review.get("schema_id"),
        "consumed_result_review_outcome_id": review.get("outcome_id"),
        "consumed_result_review_classification": review.get(
            "result_review_classification"
        ),
        "refinement_objective": REFINEMENT_OBJECTIVE,
        "obstruction_class": OBSTRUCTION_CLASS,
        "refined_candidate_accepted": review.get("refined_candidate_accepted")
        is True,
        "toy_source_candidate_status": review.get("toy_source_candidate_status"),
        "toy_source_candidate_remains_candidate_only": True,
        "toy_source_promoted_to_admissible_source": False,
        "newest_refinement_delta": refinement_delta,
        "retest_conservation_condition": retest_condition,
        "pass_fail_inconclusive_criteria": pass_fail_inconclusive_criteria,
        "why_even_a_future_pass_does_not_imply_source_admissibility_or_qft_gr_closure": (
            pass_boundary
        ),
        "conservation_retest_packet_result_reviewed": False,
        "conservation_retest_executed": False,
        "conservation_retest_result_claimed": False,
        "conservation_retest_pass_claimed": False,
        "conservation_retest_failure_claimed": False,
        "conservation_test_retried_as_proof": False,
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
            "focused_packet_current_target_registry_gates": "required_for_checkpoint",
            "adjacent_minimal_model_nonclaim_gates": "required_bounded_subset",
            "bounded_lean_substitute_packet_frontier": "required_for_checkpoint",
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
            "required for this routine bounded packet-preparation checkpoint. "
            "The release-index path remains not freshly Lean-validated, "
            "aggregate Lean is not run, and no aggregate Lean health claim is "
            "made. Timeouts remain validation caveats, not rerun instructions."
        ),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_next_target_count": 1 if prepared else 0,
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_"
            "AFTER_POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_"
            "RESULT_ONLY_NO_RETEST_EXECUTION_SOURCE_ADMISSIBILITY_"
            "CONSERVATION_PROOF_WITNESS_BIANCHI_SEMICLASSICAL_EINSTEIN_"
            "QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_PUBLIC_SUBMISSION_OR_"
            "MASTER_ACTION_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only a bounded conservation-retest protocol "
            "for the v3 post-retest-refinement toy source candidate. It "
            "defines the newest refinement delta, exact retest condition, "
            "pass/fail/inconclusive criteria, and why even a future pass would "
            "not imply source admissibility or QFT-GR closure. It does not "
            "execute a retest and preserves no source admissibility, no "
            "conservation claim, no conservation proof object, no conservation "
            "witness, no Bianchi compatibility, no semiclassical Einstein "
            "equation, no QFT-GR closure, no empirical validation, no public "
            "submission, and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model conservation-retest "
            "packet after post-retest-refinement conservation-retest "
            "refinement."
        )
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
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
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_conservation_retest_packet_after_"
        "post_retest_refinement_conservation_retest_refinement_report: "
        f"prepared={payload['packet_prepared']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
