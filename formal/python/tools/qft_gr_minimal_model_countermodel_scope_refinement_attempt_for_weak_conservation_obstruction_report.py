from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_report import (
    FOUND_CLASSIFICATION,
    INCONCLUSIVE_CLASSIFICATION,
    NOT_FOUND_CLASSIFICATION,
)
from formal.python.tools.qft_gr_minimal_model_countermodel_scope_refinement_packet_for_weak_conservation_obstruction_result_review_report import (
    CANONICAL_OBSTRUCTION_ID,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OBSTRUCTION_STATUS,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    PINNED_EVALUATION_SCOPE_ID,
    PINNED_SOURCE_TEST_PAIR_ID,
    PINNED_WEAK_PAIRING_CONTRACT_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-15T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_ATTEMPT_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_20260615_v0"
)
ATTEMPT_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_ATTEMPT_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_ATTEMPT_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_EXECUTED_WITH_NO_COUNTERMODEL_RESULT_OR_QFT_GR_"
    "CLOSURE"
)
RESULT_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_scope_refinement_for_weak_"
    "conservation_obstruction_completed_pending_result_review"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "review_qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_"
    "weak_conservation_obstruction_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_"
    "conservation_obstruction_result_review"
)
COUNTERMODEL_ATTEMPT_AFTER_SCOPE_REFINEMENT_TARGET = (
    "execute_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_"
    "for_weak_conservation_obstruction"
)
LEAN_ATTEMPT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalModelCountermodelScopeRefinementAttemptForWeakConservationObstruction.lean"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_ATTEMPT_FOR_WEAK_"
        "CONSERVATION_OBSTRUCTION_20260615_v0.json"
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


def _source_test_instantiation(review: dict[str, Any]) -> dict[str, str]:
    rows = {
        row["requirement_id"]: row for row in review.get("scope_refinement_rows", [])
    }
    source_test_row = rows["concrete_broader_source_test_pair"]
    return {
        "instantiation_id": PINNED_SOURCE_TEST_PAIR_ID,
        "source_candidate_id": source_test_row["selected_source_candidate"],
        "test_object_id": source_test_row["selected_test_object"],
        "source_candidate_status": (
            "candidate_only_not_source_admissible_not_physical_source"
        ),
        "test_object_status": (
            "allowed_broader_weak_test_slot_not_bianchi_witness"
        ),
        "usage_scope": (
            "later_countermodel_or_not_found_attempt_may_evaluate_prepared_"
            "weak_conservation_obstruction_criteria_against_this_pair_after_"
            "result_review_accepts_the_scope_refinement_attempt"
        ),
        "claim_ceiling": (
            "broader_source_test_instantiation_only_no_source_admissibility_"
            "no_countermodel_result"
        ),
    }


def _weak_pairing_semantics(review: dict[str, Any]) -> dict[str, str]:
    rows = {
        row["requirement_id"]: row for row in review.get("scope_refinement_rows", [])
    }
    pairing_row = rows["weak_pairing_totality_or_partiality_contract"]
    return {
        "contract_id": PINNED_WEAK_PAIRING_CONTRACT_ID,
        "pairing_semantics": pairing_row["selected_pairing_semantics"],
        "defined_case": (
            "pairing_defined_when_source_action_test_action_and_"
            "distributional_divergence_pairing_are_all_defined"
        ),
        "undefined_case": pairing_row["undefined_pairing_status"],
        "undefined_case_claim_ceiling": (
            "countermodel_pressure_point_only_no_source_admissibility_no_no_go_"
            "result_without_result_review"
        ),
        "totality_claimed": "no",
        "partiality_pinned": "yes",
    }


def _evaluation_scope(review: dict[str, Any]) -> dict[str, Any]:
    rows = {
        row["requirement_id"]: row for row in review.get("scope_refinement_rows", [])
    }
    evaluation_row = rows["broader_divergence_or_boundary_evaluation_scope"]
    probes = [
        {
            "probe_id": "weak_divergence_pairing_definedness",
            "required_report_field": "defined_or_undefined",
            "countermodel_pressure_status": (
                "undefined_required_pairing_may_be_pressure_point_pending_review"
            ),
        },
        {
            "probe_id": "weak_divergence_pairing_value",
            "required_report_field": "zero_nonzero_or_not_evaluable",
            "countermodel_pressure_status": (
                "defined_nonzero_pairing_may_be_pressure_point_pending_review"
            ),
        },
        {
            "probe_id": "boundary_term_retention",
            "required_report_field": "vanishes_survives_or_not_evaluable",
            "countermodel_pressure_status": (
                "surviving_boundary_term_may_be_pressure_point_pending_review"
            ),
        },
        {
            "probe_id": "derivative_exchange_legitimacy",
            "required_report_field": "justified_unjustified_or_not_evaluable",
            "countermodel_pressure_status": (
                "unjustified_exchange_may_be_pressure_point_pending_review"
            ),
        },
        {
            "probe_id": "curvature_coupling_residual",
            "required_report_field": "vanishes_survives_or_not_evaluable",
            "countermodel_pressure_status": (
                "surviving_curvature_coupling_residual_may_be_pressure_point_"
                "pending_review"
            ),
        },
    ]
    return {
        "evaluation_scope_id": PINNED_EVALUATION_SCOPE_ID,
        "selected_evaluation_scope": evaluation_row["selected_evaluation_scope"],
        "boundary_semantics": evaluation_row["boundary_semantics"],
        "probe_count": len(probes),
        "probes": probes,
        "claim_ceiling": "evaluation_protocol_only_no_conservation_proof",
    }


def _decisive_classification_criteria() -> list[dict[str, str]]:
    return [
        {
            "classification": FOUND_CLASSIFICATION,
            "selected_now": "no",
            "criterion": (
                "After result review accepts this scope-refinement attempt, a "
                "later bounded countermodel attempt may select found status "
                "only if the pinned source/test pair and partial weak-pairing "
                "contract produce a concrete obstruction pressure point."
            ),
        },
        {
            "classification": NOT_FOUND_CLASSIFICATION,
            "selected_now": "no",
            "criterion": (
                "A later bounded countermodel attempt may select not-found "
                "status only if every pinned probe is evaluated under the "
                "refined semantics and no countermodel/no-go pressure point "
                "survives."
            ),
        },
        {
            "classification": INCONCLUSIVE_CLASSIFICATION,
            "selected_now": "no",
            "criterion": (
                "A later bounded countermodel attempt may remain inconclusive "
                "only if the refined scope still lacks enough semantics to "
                "decide found or not-found status."
            ),
        },
    ]


def _attempt_findings() -> list[str]:
    return [
        (
            "The attempt consumes the accepted scope-refinement packet result "
            "review and executes only the authorized bounded scope-refinement "
            "lane."
        ),
        (
            "The broader source/test instantiation is pinned as a candidate "
            "source and broader weak-test slot, with no source-admissibility "
            "claim."
        ),
        (
            "Partial weak-pairing semantics are pinned: required undefined "
            "pairings are countermodel pressure points, not no-go or source-"
            "admissibility results."
        ),
        (
            "The later attempt criteria for found, not-found, and inconclusive "
            "status are made explicit but none is selected by this scope-"
            "refinement attempt."
        ),
        (
            "The strict toy positive conservation witness remains valid only "
            "under its strict assumptions and is not refuted by this broader "
            "scope-refinement lane."
        ),
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The scope-refinement attempt executed and must be reviewed "
                "before any bounded countermodel/no-go attempt after scope "
                "refinement can be authorized."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The scope-refinement attempt execution target is consumed here.",
        },
        {
            "target": COUNTERMODEL_ATTEMPT_AFTER_SCOPE_REFINEMENT_TARGET,
            "decision": "not_authorized_until_scope_refinement_attempt_review",
            "reason": (
                "A countermodel/no-go attempt after scope refinement remains "
                "downstream of result review."
            ),
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_not_selected_by_this_attempt",
            "reason": "Source-map ladder work remains downstream of attempt results.",
        },
        {
            "target": "claim_countermodel_exists",
            "decision": "not_authorized",
            "reason": "No countermodel-found classification is selected.",
        },
        {
            "target": "claim_no_go_result",
            "decision": "not_authorized",
            "reason": "No no-go result is selected or reviewed.",
        },
        {
            "target": "claim_countermodel_not_found",
            "decision": "not_authorized",
            "reason": "No not-found classification is selected.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The pinned source remains candidate-only.",
        },
        {
            "target": "claim_broad_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The strict toy witness is not broadened by this attempt.",
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
            "reason": "The attempt does not close QFT-GR.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
        {
            "target": "promote_master_action",
            "decision": "not_authorized",
            "reason": "No master-action promotion is authorized.",
        },
    ]


def _validation_policy(result_review: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_qft_gr_minimal_model_countermodel_scope_refinement_attempt_execution",
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
        "inherited_scope_refinement_packet_result_review_validation_policy": (
            result_review.get("validation_policy", {})
        ),
    }


def build_qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    rows = result_review.get("scope_refinement_rows", [])
    row_ids = {row.get("requirement_id") for row in rows}
    source_test_instantiation = _source_test_instantiation(result_review)
    weak_pairing_semantics = _weak_pairing_semantics(result_review)
    evaluation_scope = _evaluation_scope(result_review)
    decisive_criteria = _decisive_classification_criteria()
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(result_review)

    acceptance_criteria = {
        "consumes_expected_scope_refinement_packet_result_review": (
            result_review.get("schema_id") == EXPECTED_RESULT_REVIEW_SCHEMA_ID
            and result_review.get("review_id") == EXPECTED_RESULT_REVIEW_ID
            and result_review.get("outcome_id") == EXPECTED_RESULT_REVIEW_OUTCOME
            and result_review.get("result_review_classification")
            == EXPECTED_RESULT_REVIEW_CLASSIFICATION
            and result_review.get("selected_next_target") == CONSUMED_TARGET
        ),
        "result_review_authorized_scope_refinement_attempt_only": (
            result_review.get("accepted") is True
            and result_review.get("scope_refinement_attempt_authorized") is True
            and result_review.get("bounded_scope_refinement_attempt_authorized_only")
            is True
            and result_review.get("scope_refinement_attempt_executed") is False
            and result_review.get("countermodel_attempt_authorized_by_review") is False
        ),
        "scope_requirements_loaded": (
            result_review.get("scope_refinement_row_count") == 3
            and len(rows) == 3
            and row_ids
            == {
                "concrete_broader_source_test_pair",
                "weak_pairing_totality_or_partiality_contract",
                "broader_divergence_or_boundary_evaluation_scope",
            }
        ),
        "source_test_pair_instantiated_without_source_admissibility": (
            source_test_instantiation["instantiation_id"] == PINNED_SOURCE_TEST_PAIR_ID
            and source_test_instantiation["source_candidate_status"].startswith(
                "candidate_only"
            )
            and result_review.get("source_admissibility_claimed") is False
        ),
        "partial_weak_pairing_semantics_pinned": (
            weak_pairing_semantics["contract_id"] == PINNED_WEAK_PAIRING_CONTRACT_ID
            and weak_pairing_semantics["partiality_pinned"] == "yes"
            and weak_pairing_semantics["totality_claimed"] == "no"
        ),
        "evaluation_scope_pinned_with_required_probe_outputs": (
            evaluation_scope["evaluation_scope_id"] == PINNED_EVALUATION_SCOPE_ID
            and evaluation_scope["probe_count"] == 5
            and len(evaluation_scope["probes"]) == 5
        ),
        "decisive_criteria_defined_without_selecting_countermodel_status": (
            len(decisive_criteria) == 3
            and {
                row["classification"] for row in decisive_criteria
            }
            == {
                FOUND_CLASSIFICATION,
                NOT_FOUND_CLASSIFICATION,
                INCONCLUSIVE_CLASSIFICATION,
            }
            and all(row["selected_now"] == "no" for row in decisive_criteria)
        ),
        "strict_toy_witness_preserved_not_refuted": (
            result_review.get("strict_toy_witness_preserved") is True
            and result_review.get("strict_toy_witness_accepted") is True
            and result_review.get("strict_toy_assumptions_only") is True
            and result_review.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
        ),
        "obstruction_candidate_carried_unresolved": (
            result_review.get("dominant_obstruction_candidate")
            == DOMINANT_OBSTRUCTION_CANDIDATE
            and result_review.get("canonical_obstruction_id")
            == CANONICAL_OBSTRUCTION_ID
            and result_review.get("obstruction_status") == OBSTRUCTION_STATUS
            and result_review.get("dominant_obstruction_resolved") is False
            and result_review.get("mathematical_resolution_claimed") is False
        ),
        "attempt_selects_result_review_only": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
        "no_countermodel_no_go_or_not_found_claim": (
            result_review.get("countermodel_result_claimed") is False
            and result_review.get("countermodel_exists_claimed") is False
            and result_review.get("countermodel_achieved") is False
            and result_review.get("no_go_result_claimed") is False
            and result_review.get("not_found_result_claimed") is False
            and result_review.get("inconclusive_result_claimed") is False
        ),
        "no_source_bianchi_semiclassical_closure_empirical_public_or_promotion": (
            result_review.get("source_admissibility_claimed") is False
            and result_review.get("Bianchi_compatibility_claimed") is False
            and result_review.get("semiclassical_einstein_equation_derived")
            is False
            and result_review.get("qft_gr_seam_closed") is False
            and result_review.get("qft_gr_source_map_closure_claimed") is False
            and result_review.get("empirical_validation_claimed") is False
            and result_review.get("public_submission_authorized") is False
            and result_review.get("master_action_promoted") is False
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
    executed = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if executed
        else (
            "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_"
            "ATTEMPT_FOR_WEAK_CONSERVATION_OBSTRUCTION"
        )
    )

    return {
        "schema_id": SCHEMA_ID,
        "attempt_id": ATTEMPT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "executed": executed,
        "accepted": executed,
        "attempt_decision": "executed" if executed else "requires_remediation",
        "outcome_id": OUTCOME_ID
        if executed
        else (
            "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_ATTEMPT_FOR_"
            "WEAK_CONSERVATION_OBSTRUCTION_REQUIRES_REMEDIATION"
        ),
        "result_classification": RESULT_CLASSIFICATION,
        "selected_classification": RESULT_CLASSIFICATION,
        "result_classification_count": 1 if executed else 0,
        "selected_classification_count": 1 if executed else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_scope_refinement_packet_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_scope_refinement_packet_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "scope_refinement_packet_result_review_accepted": (
            result_review.get("accepted") is True
        ),
        "bounded_scope_refinement_attempt_authorized_only": result_review.get(
            "bounded_scope_refinement_attempt_authorized_only"
        ),
        "scope_refinement_attempt_authorized": result_review.get(
            "scope_refinement_attempt_authorized"
        ),
        "scope_refinement_attempt_executed": executed,
        "scope_refinement_attempt_result_review_pending": executed,
        "scope_refinement_attempt_result_reviewed": False,
        "scope_refinement_attempt_is_not_countermodel_attempt": True,
        "countermodel_attempt_authorized": False,
        "countermodel_attempt_after_scope_refinement_authorized": False,
        "countermodel_attempt_after_scope_refinement_executed": False,
        "countermodel_attempt_reauthorized": False,
        "countermodel_attempt_reexecuted": False,
        "countermodel_search_space_refined": executed,
        "countermodel_lane_decidability_scope_pinned": executed,
        "source_test_instantiation_pinned": executed,
        "weak_pairing_semantics_pinned": executed,
        "broader_divergence_boundary_evaluation_scope_pinned": executed,
        "pinned_source_test_pair_id": PINNED_SOURCE_TEST_PAIR_ID,
        "pinned_weak_pairing_contract_id": PINNED_WEAK_PAIRING_CONTRACT_ID,
        "pinned_evaluation_scope_id": PINNED_EVALUATION_SCOPE_ID,
        "source_test_instantiation": source_test_instantiation,
        "weak_pairing_semantics": weak_pairing_semantics,
        "evaluation_scope": evaluation_scope,
        "decisive_classification_criteria": decisive_criteria,
        "decisive_classification_criteria_count": len(decisive_criteria),
        "found_classification_not_selected": True,
        "not_found_classification_not_selected": True,
        "inconclusive_classification_not_selected": True,
        "selected_countermodel_criterion_count": 0,
        "selected_no_go_criterion_count": 0,
        "countermodel_result_claimed": False,
        "countermodel_exists_claimed": False,
        "countermodel_achieved": False,
        "no_go_result_claimed": False,
        "not_found_result_claimed": False,
        "inconclusive_result_claimed": False,
        "strict_toy_witness_preserved": True,
        "strict_toy_witness_accepted": result_review.get("strict_toy_witness_accepted"),
        "strict_toy_assumptions_only": True,
        "scope_refinement_attempt_is_not_strict_toy_witness_refutation": True,
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": OBSTRUCTION_STATUS,
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "source_map_ladder_lane_retained_as_follow_on": True,
        "source_map_ladder_packet_authorized": False,
        "immediate_retest_authorized": False,
        "conservation_retest_rerun_authorized": False,
        "ordinary_model_refinement_authorized": False,
        "source_admissibility_can_be_considered": False,
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
        "attempt_findings": _attempt_findings(),
        "validation_policy": validation_policy,
        "validation_posture": {
            "focused_attempt_current_target_registry_gate": "required_for_checkpoint",
            "adjacent_qft_gr_nonclaim_gates": "required_bounded_subset",
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
            "required for this routine bounded scope-refinement-attempt "
            "checkpoint. The release-index path remains not freshly Lean-"
            "validated, aggregate Lean is not run, and no aggregate Lean health "
            "claim is made."
        ),
        "lean_attempt_file": _ptr(LEAN_ATTEMPT_PATH),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "attempt_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if executed else 0,
        "selected_next_target_count": 1 if executed else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_ATTEMPT_"
            "FOR_WEAK_CONSERVATION_OBSTRUCTION_RESULT_ONLY_NO_COUNTERMODEL_"
            "RESULT_CLAIM_NO_NO_GO_RESULT_CLAIM_NO_SOURCE_ADMISSIBILITY_NO_"
            "QFT_GR_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This bounded scope-refinement attempt pins the broader source/"
            "test instantiation, partial weak-pairing semantics, and broader "
            "divergence/boundary/curvature evaluation protocol needed to make "
            "a later countermodel lane decidable after result review. It does "
            "not execute a countermodel/no-go attempt, does not claim a "
            "countermodel result, does not claim a no-go result, does not "
            "claim a not-found result, does not refute the accepted strict toy "
            "witness, preserves no source admissibility, no Bianchi "
            "compatibility, no semiclassical Einstein equation, no broad "
            "QFT-GR conservation, no QFT-GR closure, no empirical validation, "
            "no public submission, and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the bounded QFT-GR minimal model countermodel scope-"
            "refinement attempt for the weak-conservation obstruction."
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
    payload = write_qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction(
        result_review_path=result_review_path,
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
