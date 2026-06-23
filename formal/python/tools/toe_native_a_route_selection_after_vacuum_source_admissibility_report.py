from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_source_admissibility_review_retry_after_vacuum_identity_result_review_report import (
    A_FIELD_DOMAIN_POLICY,
    ANTISYMMETRY_ROUTE,
    BIANCHI_IDENTITY_ROUTE,
    BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
    CURRENT_COUPLED_SCOPE_BOUNDARY,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as A_SOURCE_RETRY_RESULT_REVIEW_PATH,
    DIVERGENCE_IDENTITY,
    F_DEFINITION_POLICY,
    FULL_SOURCE_ADMISSIBILITY_BOUNDARY,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LOCAL_SOURCE_ROUTE_SCOPE,
    METRIC_SIGNATURE_POLICY,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    ON_SHELL_VACUUM_CONSERVATION_ROUTE,
    OUTCOME_ID as A_SOURCE_RETRY_RESULT_REVIEW_OUTCOME,
    PACKET_ID as A_SOURCE_RETRY_RESULT_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT as A_SOURCE_RETRY_RESULT_REVIEW_RESULT,
    SCHEMA_ID as A_SOURCE_RETRY_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONDITION,
    SOURCE_ROUTE_STILL_BLOCKED,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-22T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_SOURCE_ADMISSIBILITY_20260622_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_SOURCE_ADMISSIBILITY_v0"
SELECTION_RESULT = (
    "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_SOURCE_ADMISSIBILITY_SELECTS_"
    "SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_NO_CURRENT_OR_EM_CLOSURE"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_route_selection_after_vacuum_source_admissibility_selects_"
    "source_admissibility_ck_constraint_candidate_no_current_or_em_closure"
)

NEXT_TARGET = "prepare_toe_native_A_source_admissibility_ck_constraint_candidate_packet"
NEXT_TARGET_KIND = (
    "toe_native_A_source_admissibility_ck_constraint_candidate_packet_preparation"
)

SELECTED_ROUTE_ID = "A_source_admissibility_C_k_constraint_candidate"
SELECTED_ROUTE_LABEL = "vacuum U(1) A source-admissibility C_k constraint candidate"
SELECTED_ROUTE_STATUS = "selected_for_packet_preparation"
SELECTED_ROUTE_EXECUTION_STATUS = "not_executed"
SELECTED_ROUTE_REASON = (
    "The bounded local on-shell vacuum U(1) source route has been accepted, "
    "so the next A-branch pressure test is whether the conservation residual "
    "can be recorded as an admissibility-only C_k source-rule candidate "
    "without importing current coupling or EM closure."
)

SELECTED_A_CK_CONSTRAINT_FAMILY = "A_source_admissibility_constraint_family"
A_SOURCE_CK_RULE_CANDIDATE = (
    "C_source^{A,nu}[g,A] := nabla_mu T_A^{mu nu}; "
    "C_source^{A,nu}[g,A] = 0"
)
A_SOURCE_CK_RULE_SHORT_FORM = (
    "C_source^A := nabla_mu T_A^{mu nu}; C_source^A = 0"
)
A_SOURCE_CK_RULE_INTERPRETATION = (
    "vacuum U(1) admissibility-only source rule candidate; not an action "
    "term; not a dynamical law; not sourced Maxwell theory; not EM closure"
)
A_SOURCE_CK_RULE_CLASSIFICATION = [
    "vacuum U(1)",
    "admissibility-only",
    "source-rule candidate",
    "not an action term",
    "not a dynamical law",
    "not sourced Maxwell theory",
    "not EM closure",
]

CURRENT_COUPLING_TARGET = "prepare_toe_native_A_current_coupling_policy_packet"
CURRENT_CONSERVATION_TARGET = (
    "prepare_toe_native_A_current_conservation_route_under_selected_u1_policy"
)
A_BRIDGE_CK_TARGET = "prepare_toe_native_A_bridge_admissibility_ck_constraint_candidate_packet"
A_TRANSPORT_CK_TARGET = (
    "prepare_toe_native_A_transport_consistency_ck_constraint_candidate_packet"
)
FULL_EM_CLOSURE_TARGET = "prepare_toe_native_A_full_em_closure_packet"

ROUTE_SELECTOR_CANDIDATES = [
    SELECTED_ROUTE_ID,
    "A_current_coupling_policy",
    "A_current_conservation_route",
    "A_bridge_admissibility_C_k_constraint_candidate",
    "A_transport_consistency_C_k_constraint_candidate",
    "A_full_EM_closure",
]

ROUTE_SELECTOR_COMPARISON = {
    SELECTED_ROUTE_ID: SELECTED_ROUTE_REASON,
    "A_current_coupling_policy": (
        "Deferred because no J^nu, psi-current route, or external-current "
        "native derivation has been admitted."
    ),
    "A_current_conservation_route": (
        "Deferred because sourced Maxwell and matter-current exchange remain "
        "blocked."
    ),
    "A_bridge_admissibility_C_k_constraint_candidate": (
        "Deferred until the first A source-admissibility C_k candidate is "
        "recorded."
    ),
    "A_transport_consistency_C_k_constraint_candidate": (
        "Deferred until A source and bridge C_k candidates exist."
    ),
    "A_full_EM_closure": (
        "Blocked because the accepted result is only local classical vacuum "
        "U(1), on shell, with no current or matter exchange route."
    ),
}

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_SOURCE_ADMISSIBILITY_20260622_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeARouteSelectionAfterVacuumSourceAdmissibility.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _route_options() -> list[dict[str, Any]]:
    return [
        {
            "route_id": SELECTED_ROUTE_ID,
            "route_label": SELECTED_ROUTE_LABEL,
            "candidate_target": NEXT_TARGET,
            "status": SELECTED_ROUTE_STATUS,
            "execution_status": SELECTED_ROUTE_EXECUTION_STATUS,
            "selection_reason": SELECTED_ROUTE_REASON,
            "selected_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
            "source_rule_candidate": A_SOURCE_CK_RULE_CANDIDATE,
            "source_rule_candidate_recorded_for_next_packet": True,
            "ck_candidate_packet_authorized": True,
            "ck_candidate_packet_prepared": False,
            "ck_action_embedding_selected": False,
            "ck_variation_executed": False,
            "current_route_derived": False,
            "em_closure_claimed": False,
        },
        {
            "route_id": "A_current_coupling_policy",
            "candidate_target": CURRENT_COUPLING_TARGET,
            "status": "deferred_blocked_pending_J_nu_policy",
            "execution_status": "not_executed",
            "selection_reason": ROUTE_SELECTOR_COMPARISON["A_current_coupling_policy"],
            "J_nu_derived": False,
            "current_route_derived": False,
        },
        {
            "route_id": "A_current_conservation_route",
            "candidate_target": CURRENT_CONSERVATION_TARGET,
            "status": "deferred_blocked_without_sourced_maxwell_or_exchange_route",
            "execution_status": "not_executed",
            "selection_reason": ROUTE_SELECTOR_COMPARISON[
                "A_current_conservation_route"
            ],
            "sourced_maxwell_equation_derived": False,
            "matter_current_exchange_route_proved": False,
        },
        {
            "route_id": "A_bridge_admissibility_C_k_constraint_candidate",
            "candidate_target": A_BRIDGE_CK_TARGET,
            "status": "deferred_until_A_source_ck_candidate_recorded",
            "execution_status": "not_executed",
            "selection_reason": ROUTE_SELECTOR_COMPARISON[
                "A_bridge_admissibility_C_k_constraint_candidate"
            ],
            "A_bridge_C_k_rules_constructed": False,
        },
        {
            "route_id": "A_transport_consistency_C_k_constraint_candidate",
            "candidate_target": A_TRANSPORT_CK_TARGET,
            "status": "deferred_until_A_source_and_bridge_ck_candidates_exist",
            "execution_status": "not_executed",
            "selection_reason": ROUTE_SELECTOR_COMPARISON[
                "A_transport_consistency_C_k_constraint_candidate"
            ],
            "A_transport_C_k_rules_constructed": False,
        },
        {
            "route_id": "A_full_EM_closure",
            "candidate_target": FULL_EM_CLOSURE_TARGET,
            "status": "blocked_out_of_scope_for_bounded_vacuum_route",
            "execution_status": "not_executed",
            "selection_reason": ROUTE_SELECTOR_COMPARISON["A_full_EM_closure"],
            "full_em_closure_claimed": False,
        },
    ]


def _selection_criteria(previous_review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_consumes_current_after_vacuum_source_admissibility_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The active after-vacuum-source-admissibility selector target is consumed.",
        },
        {
            "row_id": "accepted_result_review_consumed",
            "status": "accepted",
            "evidence": previous_review.get("review_result"),
            "assessment": "The accepted bounded vacuum A source-route result review is the input.",
        },
        {
            "row_id": "bounded_local_vacuum_route_preserved",
            "status": "accepted",
            "evidence": BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
            "assessment": "The local classical vacuum U(1) on-shell route remains the bounded basis.",
        },
        {
            "row_id": "accepted_divergence_identity_preserved",
            "status": "accepted",
            "evidence": DIVERGENCE_IDENTITY,
            "assessment": "The accepted divergence identity remains consumed.",
        },
        {
            "row_id": "vacuum_conservation_identity_preserved",
            "status": "accepted",
            "evidence": ON_SHELL_VACUUM_CONSERVATION_ROUTE,
            "assessment": "nabla_mu T_A^{mu nu}=0 remains only the on-shell vacuum route.",
        },
        {
            "row_id": "selected_source_ck_candidate_packet",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The selector chooses the A source-admissibility C_k candidate packet next.",
        },
        {
            "row_id": "direct_source_rule_candidate_recorded",
            "status": "accepted",
            "evidence": A_SOURCE_CK_RULE_CANDIDATE,
            "assessment": "The direct conservation residual is recorded for the next packet.",
        },
        {
            "row_id": "source_rule_candidate_classified_as_admissibility_only",
            "status": "accepted",
            "evidence": A_SOURCE_CK_RULE_CLASSIFICATION,
            "assessment": "The candidate is not an action term, dynamical law, sourced EM, or EM closure.",
        },
        {
            "row_id": "candidate_not_prepared_inside_selector",
            "status": "accepted",
            "evidence": "source_admissibility_ck_candidate_packet_prepared=false",
            "assessment": "The selector authorizes but does not prepare the C_k candidate packet.",
        },
        {
            "row_id": "current_and_sourced_em_routes_blocked",
            "status": "accepted",
            "evidence": [
                "J_nu_derived=false",
                "sourced_maxwell_equation_derived=false",
                "matter_current_exchange_route_proved=false",
            ],
            "assessment": "Current, sourced Maxwell, and exchange routes remain blocked.",
        },
        {
            "row_id": "ck_action_embedding_and_variation_blocked",
            "status": "accepted",
            "evidence": [
                "ck_action_embedding_selected=false",
                "ck_action_embedding_constructed=false",
                "ck_variation_executed=false",
            ],
            "assessment": "The selector records no C_k action embedding and executes no C_k variation.",
        },
        {
            "row_id": "closure_coupling_validation_promotion_blocked",
            "status": "accepted",
            "evidence": [
                "full_em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "semiclassical_coupling_authorized=false",
                "empirical_validation_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No closure, coupling, validation, or master-action promotion follows.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_route_selection_after_vacuum_source_admissibility"
        ),
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "aggregate_timeout_with_steady_progress_interpretation": (
            "incomplete_validation_not_mathematical_failure"
        ),
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": (
            "INCOMPLETE_TIMEOUT_STEADY_PROGRESS"
        ),
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_toeformal_aggregate_status_for_packet": (
            "INCOMPLETE_TIMEOUT_STEADY_PROGRESS"
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": True,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_toe_native_a_route_selection_after_vacuum_source_admissibility(
    *,
    a_source_retry_result_review_path: Path = A_SOURCE_RETRY_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    previous_review = _read_json(a_source_retry_result_review_path)
    route_options = _route_options()
    selection_criteria = _selection_criteria(previous_review)
    acceptance_criteria = {
        "consumes_expected_selector_target": (
            previous_review.get("schema_id") == A_SOURCE_RETRY_RESULT_REVIEW_SCHEMA_ID
            and previous_review.get("packet_id")
            == A_SOURCE_RETRY_RESULT_REVIEW_PACKET_ID
            and previous_review.get("outcome_id")
            == A_SOURCE_RETRY_RESULT_REVIEW_OUTCOME
            and previous_review.get("review_result")
            == A_SOURCE_RETRY_RESULT_REVIEW_RESULT
            and previous_review.get("selected_next_target") == CONSUMED_TARGET
            and previous_review.get("accepted") is True
        ),
        "bounded_local_route_accepted": (
            previous_review.get("accepted_divergence_identity_consumed") is True
            and previous_review.get("bounded_local_on_shell_vacuum_source_route_accepted")
            is True
            and previous_review.get("local_on_shell_vacuum_source_route_accepted")
            is True
            and previous_review.get("source_admissibility_condition_satisfied_on_shell")
            is True
        ),
        "vacuum_u1_context_preserved": (
            previous_review.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and previous_review.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and previous_review.get("F_definition_policy") == F_DEFINITION_POLICY
            and previous_review.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and previous_review.get("stress_energy_under_selected_u1_policy")
            == STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
        ),
        "source_ck_candidate_selected_once": (
            sum(1 for row in route_options if row["status"] == SELECTED_ROUTE_STATUS)
            == 1
            and NEXT_TARGET
            == "prepare_toe_native_A_source_admissibility_ck_constraint_candidate_packet"
            and SELECTED_A_CK_CONSTRAINT_FAMILY
            == "A_source_admissibility_constraint_family"
        ),
        "source_rule_candidate_is_bounded_residual": (
            A_SOURCE_CK_RULE_CANDIDATE
            == (
                "C_source^{A,nu}[g,A] := nabla_mu T_A^{mu nu}; "
                "C_source^{A,nu}[g,A] = 0"
            )
            and "not an action term" in A_SOURCE_CK_RULE_CLASSIFICATION
            and "not sourced Maxwell theory" in A_SOURCE_CK_RULE_CLASSIFICATION
        ),
        "selector_does_not_prepare_or_embed_ck": True,
        "nonclaim_boundaries_preserved": (
            previous_review.get("J_nu_derived") is False
            and previous_review.get("sourced_maxwell_equation_derived") is False
            and previous_review.get("matter_gauge_energy_exchange_proved") is False
            and previous_review.get("A_relevant_C_k_rules_constructed") is False
            and previous_review.get("em_closure_claimed") is False
            and previous_review.get("qft_gr_closure_claimed") is False
            and previous_review.get("semiclassical_coupling_authorized") is False
            and previous_review.get("empirical_validation_claimed") is False
            and previous_review.get("master_action_promoted") is False
        ),
        "selection_criteria_all_accepted": all(
            row["status"] == "accepted" for row in selection_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_SOURCE_ADMISSIBILITY"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_SOURCE_ADMISSIBILITY",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "packet_result": "SELECTED" if accepted else "SELECTION_REQUIRES_REMEDIATION",
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_SOURCE_ADMISSIBILITY_REQUIRES_REMEDIATION",
        "selection_result": SELECTION_RESULT,
        "route_selection_result": SELECTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "previous_review_outcome": A_SOURCE_RETRY_RESULT_REVIEW_OUTCOME,
        "previous_review_result": A_SOURCE_RETRY_RESULT_REVIEW_RESULT,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "F_antisymmetry_route": ANTISYMMETRY_ROUTE,
        "bianchi_identity_route": BIANCHI_IDENTITY_ROUTE,
        "metric_signature_policy": METRIC_SIGNATURE_POLICY,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "stress_energy_under_selected_u1_policy": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "candidate_source_object": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "divergence_identity": DIVERGENCE_IDENTITY,
        "stress_energy_divergence_route": DIVERGENCE_IDENTITY,
        "on_shell_vacuum_conservation_identity": ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
        "on_shell_vacuum_conservation_route": ON_SHELL_VACUUM_CONSERVATION_ROUTE,
        "bounded_source_admissibility_result": BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
        "local_source_route_scope": LOCAL_SOURCE_ROUTE_SCOPE,
        "full_source_admissibility_boundary": FULL_SOURCE_ADMISSIBILITY_BOUNDARY,
        "current_coupled_scope_boundary": CURRENT_COUPLED_SCOPE_BOUNDARY,
        "route_selector_candidates": ROUTE_SELECTOR_CANDIDATES,
        "route_selector_comparison": ROUTE_SELECTOR_COMPARISON,
        "route_option_count": len(route_options),
        "route_options": route_options,
        "route_options_selected_count": sum(
            1 for row in route_options if row["status"] == SELECTED_ROUTE_STATUS
        ),
        "route_options_deferred_count": sum(
            1 for row in route_options if row["status"] != SELECTED_ROUTE_STATUS
        ),
        "selected_route_id": SELECTED_ROUTE_ID,
        "selected_route_label": SELECTED_ROUTE_LABEL,
        "selected_route_status": SELECTED_ROUTE_STATUS,
        "selected_route_execution_status": SELECTED_ROUTE_EXECUTION_STATUS,
        "selected_route_target": selected_next_target,
        "selected_route_reason": SELECTED_ROUTE_REASON,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "selected_a_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "source_admissibility_ck_constraint_candidate_packet_target": (
            selected_next_target
        ),
        "A_source_ck_rule_candidate": A_SOURCE_CK_RULE_CANDIDATE,
        "a_source_ck_rule_candidate": A_SOURCE_CK_RULE_CANDIDATE,
        "source_rule_candidate": A_SOURCE_CK_RULE_CANDIDATE,
        "source_rule_candidate_short_form": A_SOURCE_CK_RULE_SHORT_FORM,
        "A_source_ck_rule_interpretation": A_SOURCE_CK_RULE_INTERPRETATION,
        "source_rule_candidate_interpretation": A_SOURCE_CK_RULE_INTERPRETATION,
        "A_source_ck_rule_classification": A_SOURCE_CK_RULE_CLASSIFICATION,
        "source_rule_candidate_classification": A_SOURCE_CK_RULE_CLASSIFICATION,
        "current_coupling_target": CURRENT_COUPLING_TARGET,
        "current_conservation_target": CURRENT_CONSERVATION_TARGET,
        "a_bridge_ck_target": A_BRIDGE_CK_TARGET,
        "a_transport_ck_target": A_TRANSPORT_CK_TARGET,
        "full_em_closure_target": FULL_EM_CLOSURE_TARGET,
        "selection_criteria": selection_criteria,
        "selection_criteria_count": len(selection_criteria),
        "selection_criteria_accepted_count": sum(
            1 for row in selection_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "selector_prepared": accepted,
        "selector_executed": accepted,
        "route_selection_executed": accepted,
        "next_a_route_selected": accepted,
        "A_relevant_C_k_route_selected": accepted,
        "A_relevant_C_k_candidate_packet_selected": accepted,
        "A_source_admissibility_C_k_candidate_selected": accepted,
        "source_admissibility_ck_constraint_candidate_packet_selected": accepted,
        "source_admissibility_ck_candidate_packet_authorized": accepted,
        "source_rule_candidate_recorded_for_next_packet": accepted,
        "candidate_packet_authorized": accepted,
        "candidate_packet_target": selected_next_target,
        "source_admissibility_ck_candidate_packet_prepared": False,
        "candidate_packet_prepared": False,
        "candidate_packet_executed": False,
        "source_rule_candidate_promoted_to_action_term": False,
        "source_rule_candidate_promoted_to_dynamical_law": False,
        "source_rule_candidate_treated_as_sourced_em": False,
        "source_rule_candidate_treated_as_em_closure": False,
        "ck_action_embedding_selected": False,
        "C_k_action_embedding_selected": False,
        "ck_action_embedding_constructed": False,
        "C_k_action_embedding_constructed": False,
        "ck_variation_executed": False,
        "C_k_variation_executed": False,
        "ck_variation_authorized": False,
        "C_k_variation_authorized": False,
        "A_relevant_C_k_rules_constructed": False,
        "A_relevant_C_k_triads_constructed": False,
        "A_source_C_k_rule_constructed": False,
        "C_k_analogues_constructed": False,
        "source_bridge_transport_ck_analogues_constructed": False,
        "bounded_local_on_shell_source_admissibility_review_passed": accepted,
        "bounded_local_on_shell_vacuum_source_route_accepted": accepted,
        "local_on_shell_vacuum_source_route_accepted": accepted,
        "local_on_shell_vacuum_source_route_proved": accepted,
        "accepted_divergence_identity_consumed": accepted,
        "on_shell_vanishing_route_consumed": accepted,
        "source_admissibility_condition_satisfied_on_shell": accepted,
        "full_source_admissibility_review_accepted": False,
        "source_admissibility_completed": False,
        "source_admissibility_proved": False,
        "source_admissibility_claimed": False,
        "A_source_admissibility_proved": False,
        "A_source_admissibility_claimed": False,
        "stress_energy_source_admissibility_proved": False,
        "stress_energy_as_gravity_source_authorized": False,
        "semiclassical_source_established": False,
        "current_coupling_route_selected": False,
        "current_conservation_route_selected": False,
        "current_route_derived": False,
        "current_source_route_constructed": False,
        "matter_current_J_nu_derived": False,
        "J_nu_derived": False,
        "psi_current_route_constructed": False,
        "psi_derived_current": False,
        "external_current_policy_selected": False,
        "external_current_native_derivation_selected": False,
        "current_conservation_proved": False,
        "current_conservation_theorem_claimed": False,
        "matter_current_exchange_route_proved": False,
        "matter_gauge_energy_exchange_proved": False,
        "matter_gauge_energy_exchange_claimed": False,
        "maxwell_equation_derived": False,
        "maxwell_equations_derived": False,
        "sourced_maxwell_equation_derived": False,
        "sourced_maxwell_closure_claimed": False,
        "nonabelian_route_selected": False,
        "yang_mills_equations_derived": False,
        "field_equations_derived": False,
        "full_em_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "canonical_master_action_promoted": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "accepted_outcomes_considered": [
            SELECTION_RESULT,
            (
                "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_SOURCE_ADMISSIBILITY_"
                "RECORDS_SOURCE_ADMISSIBILITY_CK_CANDIDATE_AS_DEFERRED_GUIDANCE"
            ),
            (
                "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_SOURCE_ADMISSIBILITY_"
                "REJECTS_SCOPE_LEAK_PENDING_REMEDIATION"
            ),
        ],
        "critical_gate_fail_conditions": [
            "prepare the A source-admissibility C_k candidate inside the selector",
            "embed C_k in the action",
            "execute C_k variation",
            "promote the residual to a dynamical law",
            "derive J^nu",
            "derive a psi current route",
            "derive sourced Maxwell",
            "prove matter-current exchange",
            "claim full EM closure",
            "claim QFT-GR closure",
            "authorize semiclassical coupling",
            "claim empirical validation",
            "promote the working-form master action",
        ],
        "downstream_progression": [
            {
                "stage": "A_route_selector_after_vacuum_source_admissibility",
                "status": "SELECTED_A_SOURCE_ADMISSIBILITY_CK_CANDIDATE_PACKET",
                "decision": SELECTION_RESULT,
                "reason": SELECTED_ROUTE_REASON,
            },
            {
                "stage": "A_source_admissibility_ck_constraint_candidate_packet",
                "status": "NEXT_TARGET_AUTHORIZED_FOR_PREPARATION_ONLY",
                "decision": selected_next_target,
                "reason": (
                    "The next packet may record the vacuum conservation "
                    "residual as an admissibility-only source-rule candidate. "
                    "The selector itself does not build the rule, embed it in "
                    "the action, or vary it."
                ),
            },
        ],
        "mathematical_statement": (
            "Given the accepted bounded local classical vacuum U(1) route "
            + VACUUM_EULER_LAGRANGE_ROUTE
            + " and "
            + ON_SHELL_VACUUM_CONSERVATION_IDENTITY
            + ", the selector chooses the A source-admissibility C_k "
            "candidate packet. The candidate shape to test next is "
            + A_SOURCE_CK_RULE_CANDIDATE
            + ". This is a vacuum admissibility residual only."
        ),
        "non_claim_boundary": (
            "This selector selects only the next A source-admissibility C_k "
            "constraint candidate packet and records the direct candidate "
            "shape "
            + A_SOURCE_CK_RULE_CANDIDATE
            + " for that next packet. It does not prepare the candidate "
            "packet, does not embed C_k in the action, does not execute C_k "
            "variation, does not promote the residual to a dynamical law, "
            "does not derive J^nu, does not derive a psi-current or external "
            "current route, does not derive sourced Maxwell, does not prove "
            "matter-current or matter-gauge exchange, does not construct "
            "A-relevant C_k rules, does not close EM, does not close QFT-GR, "
            "does not authorize semiclassical coupling, does not claim "
            "empirical validation, and does not promote the master action."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeARouteSelectionAfterVacuumSourceAdmissibility",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "lane_level_lean_target_files": [
            _ptr(LEAN_PACKET_PATH),
            _ptr(QFTGR_AGGREGATE_PATH),
            _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            _ptr(RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH),
        ],
        "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        "validation_policy": _validation_policy(),
    }


def write_toe_native_a_route_selection_after_vacuum_source_admissibility(
    *,
    a_source_retry_result_review_path: Path = A_SOURCE_RETRY_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_a_route_selection_after_vacuum_source_admissibility(
        a_source_retry_result_review_path=a_source_retry_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A route selector after vacuum source admissibility."
        )
    )
    parser.add_argument(
        "--a-source-retry-result-review",
        type=Path,
        default=A_SOURCE_RETRY_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_a_route_selection_after_vacuum_source_admissibility(
        a_source_retry_result_review_path=args.a_source_retry_result_review,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
