from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_result_review_report import (
    DEFAULT_OUT as DEFAULT_CURRENT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_CURRENT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_CURRENT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_CURRENT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_CURRENT_REVIEW_SCHEMA_ID,
    SELECTED_REFINEMENT_TARGET,
)
from formal.python.tools.qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_report import (
    DEFAULT_OUT as DEFAULT_PRIOR_REFINEMENT_PACKET_PATH,
    OUTCOME_ID as EXPECTED_PRIOR_REFINEMENT_PACKET_OUTCOME,
    PACKET_ID as EXPECTED_PRIOR_REFINEMENT_PACKET_ID,
    SCHEMA_ID as EXPECTED_PRIOR_REFINEMENT_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-14T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_POST_RETEST_"
    "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_20260614_v0"
)
PACKET_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_POST_RETEST_"
    "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_POST_RETEST_"
    "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_PREPARED_WITH_NO_SOURCE_"
    "ADMISSIBILITY_OR_CONSERVATION_PROOF"
)
PACKET_CLASSIFICATION = (
    "qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_prepared_pending_result_review"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "review_qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_result_review"
)
REFINEMENT_OBJECTIVE = SELECTED_REFINEMENT_TARGET
OBSTRUCTION_CLASS = (
    "repeated_weak_divergence_undecided_under_candidate_pairing_domain_v3"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_POST_RETEST_"
        "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_20260614_v0.json"
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
                "The prepared refinement packet must be result-reviewed before "
                "any refinement attempt, further retest, countermodel packet, "
                "source-admissibility claim, or promotion."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": (
                "This conservation-retest-refinement packet-preparation target "
                "is consumed by the packet artifact."
            ),
        },
        {
            "target": (
                "execute_qft_gr_minimal_working_model_refinement_attempt_after_"
                "post_retest_refinement_conservation_retest_refinement"
            ),
            "decision": "not_authorized_before_packet_result_review",
            "reason": "The packet prepares a refinement plan only.",
        },
        {
            "target": (
                "execute_qft_gr_minimal_working_model_conservation_retest_"
                "attempt_after_post_retest_refinement_conservation_retest_"
                "refinement"
            ),
            "decision": "not_authorized_without_model_delta",
            "reason": (
                "A further conservation retest would repeat the undecided v3 "
                "candidate without a reviewed refinement delta."
            ),
        },
        {
            "target": (
                "prepare_qft_gr_minimal_working_model_countermodel_packet_after_"
                "post_retest_refinement_conservation_retest_refinement"
            ),
            "decision": "not_selected_no_failed_retest_obstruction",
            "reason": (
                "Countermodel preparation remains bounded downstream work, but "
                "the accepted result is inconclusive rather than failed."
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
            "reason": "No conservation proof is prepared or claimed.",
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
            "reason": "QFT-GR closure remains outside this packet.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def _repeated_inconclusive_signal() -> list[dict[str, str]]:
    return [
        {
            "signal_id": "first_conservation_retest_after_initial_refinement",
            "classification": (
                "qft_gr_minimal_working_model_conservation_retest_inconclusive_"
                "requires_model_refinement"
            ),
            "meaning": (
                "A refined toy candidate did not decide weak conservation, so "
                "candidate existence remained separate from admissibility."
            ),
        },
        {
            "signal_id": "post_retest_refinement_conservation_retest",
            "classification": (
                "qft_gr_minimal_working_model_conservation_retest_after_post_"
                "retest_refinement_inconclusive_requires_model_refinement"
            ),
            "meaning": (
                "The v2 weak-pairing domain and regularity context still did "
                "not decide zero versus nonzero weak divergence."
            ),
        },
        {
            "signal_id": (
                "post_retest_refinement_conservation_retest_refinement_v3_retest"
            ),
            "classification": (
                "qft_gr_minimal_working_model_conservation_retest_after_post_"
                "retest_refinement_conservation_retest_refinement_"
                "inconclusive_requires_model_refinement"
            ),
            "meaning": (
                "The v3 candidate weak-pairing domain and regularity clauses "
                "still leave weak divergence undecided."
            ),
        },
    ]


def _refinement_dimensions() -> list[dict[str, Any]]:
    return [
        {
            "dimension_id": "v3_retest_weak_pairing_domain",
            "scope": "weak_pairing_domain",
            "obstruction_class": OBSTRUCTION_CLASS,
            "current_status": "toy_weak_pairing_domain_v3_candidate",
            "prepared_refinement": (
                "Prepare a v4 candidate weak-pairing domain with explicit "
                "admitted and blocked test-vector pairings, without claiming "
                "source-domain membership."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "dimension_id": "v3_retest_regular_context",
            "scope": "regularity_assumptions",
            "obstruction_class": OBSTRUCTION_CLASS,
            "current_status": "toy_regular_context_v3_candidate",
            "prepared_refinement": (
                "Refine derivative-exchange, boundary-term, regularization, "
                "and limit-interchange clauses into explicit v4 candidate "
                "admission requirements, without treating them as discharged."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "dimension_id": "v3_retest_test_function_class",
            "scope": "test_function_class",
            "obstruction_class": OBSTRUCTION_CLASS,
            "current_status": "toy_conservation_test_function_class_v2_candidate",
            "prepared_refinement": (
                "Prepare a v3 admissible test-function class so the next "
                "attempt can distinguish missing tests from genuine nonzero "
                "weak divergence."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "dimension_id": "v3_retest_candidate_source_definition",
            "scope": "candidate_source_definition",
            "obstruction_class": OBSTRUCTION_CLASS,
            "current_status": "toy_source_candidate_definition_v3_candidate",
            "prepared_refinement": (
                "Name a v4 candidate-source definition and keep every "
                "source-admissibility step as unproved candidate data."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "dimension_id": "v3_retest_scope_restriction",
            "scope": "scope_restriction",
            "obstruction_class": OBSTRUCTION_CLASS,
            "current_status": "bounded_toy_candidate_weak_pairing_scope_only",
            "prepared_refinement": (
                "Keep the next refinement inside the toy weak-pairing scope "
                "unless a reviewed packet explicitly authorizes broader "
                "semantics."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "dimension_id": "v3_retest_obstruction_accounting",
            "scope": "obstruction_accounting",
            "obstruction_class": OBSTRUCTION_CLASS,
            "current_status": "three_inconclusive_conservation_retest_signals",
            "prepared_refinement": (
                "Record the repeated inconclusive retest as an anti-loop "
                "obstruction map, not as a conservation pass or failure."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "dimension_id": "v3_retest_validation_boundary",
            "scope": "validation_boundary",
            "obstruction_class": OBSTRUCTION_CLASS,
            "current_status": "bounded_routine_validation_with_standing_caveats",
            "prepared_refinement": (
                "Preserve bounded validation and standing aggregate Lean, CI, "
                "security, and release-index caveats."
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
    ]


def _why_refinement_not_immediate_retest_or_promotion() -> list[str]:
    return [
        (
            "The accepted v3 result is inconclusive, not a pass and not a "
            "failure."
        ),
        (
            "Immediate retesting would reuse the undecided v3 candidate domain "
            "and repeat the same scientific obstruction without a model delta."
        ),
        (
            "The next bounded delta is to refine the weak-pairing domain, "
            "regularity clauses, test-function class, candidate-source "
            "definition, scope restriction, and obstruction accounting."
        ),
        (
            "No explicit failed-conservation obstruction was recorded, so a "
            "countermodel packet is not selected."
        ),
        (
            "Promotion is unavailable because the source is still candidate "
            "data and no conservation proof object or witness exists."
        ),
    ]


def _review_gate_requirements() -> list[str]:
    return [
        "consume this refinement packet artifact",
        "confirm the v3 inconclusive retest remains inconclusive",
        "confirm the obstruction class exactly",
        "confirm the packet is preparation only",
        "confirm no refinement attempt is executed by the packet",
        "confirm no conservation retest is rerun by the packet",
        "confirm no countermodel packet is selected without a failed-retest obstruction",
        "confirm the weak-pairing-domain v4 candidate is identified but not discharged",
        "confirm the regularity v4 candidate is identified but not discharged",
        "confirm the test-function class v3 candidate is identified but not used as a proof",
        "confirm the candidate source definition remains candidate-only",
        "confirm no conservation proof object or witness is constructed",
        "confirm no source admissibility, Bianchi compatibility, semiclassical Einstein equation, QFT-GR closure, empirical validation, public submission, or master-action promotion is claimed",
    ]


def _validation_policy(review: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_refinement_packet_preparation_after_v3_inconclusive_retest",
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
        "inherited_review_validation_policy": review.get("validation_policy", {}),
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


def build_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement(
    *,
    current_review_path: Path = DEFAULT_CURRENT_REVIEW_PATH,
    prior_refinement_packet_path: Path = DEFAULT_PRIOR_REFINEMENT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    current_review = _read_json(current_review_path)
    prior_refinement_packet = _read_json(prior_refinement_packet_path)
    candidate_next_targets = _candidate_next_targets()
    refinement_dimensions = _refinement_dimensions()
    validation_policy = _validation_policy(current_review)
    dimension_scopes = {row["scope"] for row in refinement_dimensions}

    acceptance_criteria = {
        "consumes_expected_current_result_review": (
            current_review.get("schema_id") == EXPECTED_CURRENT_REVIEW_SCHEMA_ID
            and current_review.get("review_id") == EXPECTED_CURRENT_REVIEW_ID
        ),
        "current_result_review_outcome_expected": current_review.get("outcome_id")
        == EXPECTED_CURRENT_REVIEW_OUTCOME,
        "current_result_review_classification_expected": current_review.get(
            "result_review_classification"
        )
        == EXPECTED_CURRENT_REVIEW_CLASSIFICATION,
        "current_result_review_selected_this_packet": current_review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "prior_refinement_packet_recorded": (
            prior_refinement_packet.get("schema_id")
            == EXPECTED_PRIOR_REFINEMENT_PACKET_SCHEMA_ID
            and prior_refinement_packet.get("packet_id")
            == EXPECTED_PRIOR_REFINEMENT_PACKET_ID
            and prior_refinement_packet.get("outcome_id")
            == EXPECTED_PRIOR_REFINEMENT_PACKET_OUTCOME
            and prior_refinement_packet.get("accepted") is True
        ),
        "current_retest_inconclusive_not_converted": (
            current_review.get("accepted_inconclusive_result") is True
            and current_review.get("retest_inconclusive") is True
            and current_review.get("retest_passed") is False
            and current_review.get("retest_failed") is False
        ),
        "model_refinement_packet_authorized": (
            current_review.get("model_refinement_packet_authorized") is True
            and current_review.get("model_refinement_packet_prepared_by_review")
            is False
        ),
        "countermodel_not_selected": (
            current_review.get("countermodel_packet_authorized") is False
            and current_review.get("countermodel_packet_prepared_by_review") is False
        ),
        "selected_refinement_objective_matches_review": current_review.get(
            "selected_refinement_target"
        )
        == REFINEMENT_OBJECTIVE,
        "obstruction_class_selected": OBSTRUCTION_CLASS
        == "repeated_weak_divergence_undecided_under_candidate_pairing_domain_v3",
        "repeated_inconclusive_signal_recorded": len(_repeated_inconclusive_signal())
        == 3,
        "why_refinement_not_immediate_retest_or_promotion_recorded": len(
            _why_refinement_not_immediate_retest_or_promotion()
        )
        >= 5,
        "refinement_dimensions_recorded": dimension_scopes
        >= {
            "weak_pairing_domain",
            "regularity_assumptions",
            "test_function_class",
            "candidate_source_definition",
            "scope_restriction",
            "obstruction_accounting",
            "validation_boundary",
        },
        "review_gate_requirements_recorded": len(_review_gate_requirements()) >= 13,
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
        "standing_validation_caveats_preserved": (
            current_review.get("release_index_path_not_freshly_lean_validated")
            is True
            and current_review.get("aggregate_lean_not_run") is True
            and current_review.get("aggregate_lean_timeout_caveat_preserved") is True
            and current_review.get("aggregate_lean_health_claimed") is False
        ),
        "no_source_admissibility_claim": (
            current_review.get("source_admissibility_claimed") is False
            and current_review.get("stress_energy_source_admissibility_claimed")
            is False
        ),
        "no_conservation_claim_proof_or_witness": (
            current_review.get("conservation_claimed") is False
            and current_review.get("conservation_proved") is False
            and current_review.get("conservation_proof_object_constructed") is False
            and current_review.get("conservation_witness_constructed") is False
        ),
        "no_bianchi_or_semiclassical_einstein": (
            current_review.get("Bianchi_compatibility_claimed") is False
            and current_review.get("semiclassical_einstein_equation_derived")
            is False
        ),
        "no_qft_gr_closure": (
            current_review.get("qft_gr_seam_closed") is False
            and current_review.get("qft_gr_source_map_closure_claimed") is False
        ),
        "no_empirical_validation_or_public_submission": (
            current_review.get("empirical_validation_claimed") is False
            and current_review.get("public_submission_authorized") is False
        ),
        "no_master_action_promotion": (
            current_review.get("master_action_promoted") is False
            and current_review.get("master_action_promotion_authorized") is False
        ),
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_"
            "POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT"
        )
    )

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "packet_prepared": accepted,
        "packet_preparation_only": True,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_POST_RETEST_"
            "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REQUIRES_REMEDIATION"
        ),
        "packet_classification": PACKET_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
            "refinement_conservation_retest_refinement_requires_remediation"
        ),
        "packet_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_current_result_review": EXPECTED_CURRENT_REVIEW_ID,
        "consumes_current_result_review_pointer": _ptr(current_review_path),
        "consumed_current_result_review_outcome_id": current_review.get("outcome_id"),
        "consumed_current_result_review_classification": current_review.get(
            "result_review_classification"
        ),
        "references_prior_refinement_packet": EXPECTED_PRIOR_REFINEMENT_PACKET_ID,
        "references_prior_refinement_packet_pointer": _ptr(
            prior_refinement_packet_path
        ),
        "prior_refinement_packet_outcome_id": prior_refinement_packet.get(
            "outcome_id"
        ),
        "repeated_inconclusive_signal": _repeated_inconclusive_signal(),
        "repeated_inconclusive_signal_count": len(_repeated_inconclusive_signal()),
        "why_refinement_not_immediate_retest_or_promotion": (
            _why_refinement_not_immediate_retest_or_promotion()
        ),
        "obstruction_class": OBSTRUCTION_CLASS,
        "refinement_objective": (
            REFINEMENT_OBJECTIVE if accepted else "requires_remediation"
        ),
        "selected_refinement_target": (
            REFINEMENT_OBJECTIVE if accepted else "requires_remediation"
        ),
        "selected_refinement_target_count": 1 if accepted else 0,
        "refinement_focus": (
            "v3_inconclusive_weak_divergence_pairing_domain_regular_context_"
            "test_function_candidate_definition_scope_restriction"
        ),
        "refinement_dimensions": refinement_dimensions,
        "refinement_dimension_count": len(refinement_dimensions),
        "identified_refinement_scopes": sorted(dimension_scopes),
        "current_weak_pairing_domain_id": "toy_weak_pairing_domain_v3_candidate",
        "current_regular_context_id": "toy_regular_context_v3_candidate",
        "current_test_function_class_id": (
            "toy_conservation_test_function_class_v2_candidate"
        ),
        "current_candidate_source_definition_id": (
            "toy_source_candidate_definition_v3_candidate"
        ),
        "proposed_weak_pairing_domain_revision": (
            "toy_weak_pairing_domain_v4_candidate"
        ),
        "proposed_regular_context_revision": "toy_regular_context_v4_candidate",
        "proposed_test_function_class_revision": (
            "toy_conservation_test_function_class_v3_candidate"
        ),
        "proposed_candidate_source_definition_revision": (
            "toy_source_candidate_definition_v4_candidate"
        ),
        "scope_restriction": "bounded_toy_candidate_weak_pairing_scope_only",
        "review_gate_requirements": _review_gate_requirements(),
        "model_refinement_packet_authorized": True,
        "model_refinement_packet_prepared": accepted,
        "model_refinement_packet_preparation_only": True,
        "model_refinement_executed": False,
        "refinement_attempt_executed": False,
        "countermodel_packet_authorized": False,
        "countermodel_packet_prepared": False,
        "conservation_retest_retried": False,
        "conservation_retest_executed_by_packet": False,
        "conservation_retest_result_claimed": False,
        "conservation_retest_pass_claimed": False,
        "conservation_retest_failure_claimed": False,
        "toy_source_candidate_status": "candidate_only_not_source_admissibility",
        "toy_source_candidate_remains_candidate_only": True,
        "toy_source_promoted_to_admissible_source": False,
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
        "aggregate_lean_timeout_caveat_preserved": current_review.get(
            "aggregate_lean_timeout_caveat_preserved"
        )
        is True,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_health_claimed": False,
        "validation_policy": validation_policy,
        "validation_caveat": (
            "Bounded routine validation applies. Full pytest, full governance "
            "suite, full aggregate Lean, release-index Lean validation, CI "
            "parity, and security scans are not required or run for this "
            "routine packet checkpoint. No aggregate Lean health claim is made."
        ),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_POST_"
            "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_ONLY_NO_"
            "REFINEMENT_ATTEMPT_CONSERVATION_RETEST_COUNTERMODEL_PACKET_"
            "SOURCE_ADMISSIBILITY_CONSERVATION_PROOF_WITNESS_BIANCHI_"
            "SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_OR_"
            "PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only a bounded model-refinement plan after "
            "the v3 conservation retest remained inconclusive. It records the "
            "remaining obstruction class repeated_weak_divergence_undecided_"
            "under_candidate_pairing_domain_v3 and explains why the selected "
            "response is model refinement rather than immediate retesting, "
            "countermodel preparation, or promotion. It does not execute "
            "refinement, rerun conservation, claim conservation, construct a "
            "conservation proof object, construct a conservation witness, "
            "claim source admissibility, claim Bianchi compatibility, derive "
            "the semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, authorize public submission, or promote the master "
            "action. Boundary shorthand: no source admissibility, no "
            "conservation proof object, no conservation witness, no Bianchi "
            "compatibility, no semiclassical Einstein equation, no QFT-GR "
            "closure, and no public submission."
        ),
    }


def write_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement(
    *,
    current_review_path: Path = DEFAULT_CURRENT_REVIEW_PATH,
    prior_refinement_packet_path: Path = DEFAULT_PRIOR_REFINEMENT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement(
        current_review_path=current_review_path,
        prior_refinement_packet_path=prior_refinement_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model refinement packet after "
            "the post-retest-refinement conservation-retest refinement."
        )
    )
    parser.add_argument("--current-review", type=Path, default=DEFAULT_CURRENT_REVIEW_PATH)
    parser.add_argument(
        "--prior-refinement-packet",
        type=Path,
        default=DEFAULT_PRIOR_REFINEMENT_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    current_review_path = (
        ns.current_review
        if ns.current_review.is_absolute()
        else (REPO_ROOT / ns.current_review)
    )
    prior_refinement_packet_path = (
        ns.prior_refinement_packet
        if ns.prior_refinement_packet.is_absolute()
        else (REPO_ROOT / ns.prior_refinement_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement(
        current_review_path=current_review_path,
        prior_refinement_packet_path=prior_refinement_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
        "refinement_conservation_retest_refinement_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
