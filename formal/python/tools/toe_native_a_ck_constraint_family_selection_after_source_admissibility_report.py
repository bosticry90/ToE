from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

sys.setrecursionlimit(10000)

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_source_admissibility_ck_admissibility_rule_closeout_report import (
    ADMISSIBILITY_CONSTRAINT_FORM as SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    A_FIELD_DOMAIN_POLICY,
    BIANCHI_IDENTITY_ROUTE,
    BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
    CANDIDATE_CONSTRAINT_EQUATION as SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM as SOURCE_CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID as SOURCE_CANDIDATE_CONSTRAINT_ID,
    CANDIDATE_CONSTRAINT_SHORT_FORM as SOURCE_CANDIDATE_CONSTRAINT_SHORT_FORM,
    CLOSEOUT_RESULT as SOURCE_RULE_CLOSEOUT_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as SOURCE_RULE_CLOSEOUT_PATH,
    DIVERGENCE_IDENTITY,
    F_DEFINITION_POLICY,
    FIRST_A_RULE_CLASSIFICATION,
    FULL_TOEFORMAL_STATUS,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LOCAL_SOURCE_ROUTE_SCOPE,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID as SOURCE_RULE_CLOSEOUT_OUTCOME,
    PACKET_ID as SOURCE_RULE_CLOSEOUT_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as SOURCE_RULE_CLOSEOUT_SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY as SOURCE_SELECTED_A_CK_CONSTRAINT_FAMILY,
    SOURCE_ADMISSIBILITY_CONDITION,
    SOURCE_ROUTE_STILL_BLOCKED,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
    VACUUM_ON_SHELL_IMPLICATION_FORM,
    VACUUM_SUPPORTING_IDENTITY_FORM,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-22T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY_"
    "20260622_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY_v0"
)
SELECTION_RESULT = (
    "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY_"
    "SELECTS_BRIDGE_ADMISSIBILITY_NO_CURRENT_OR_EM_CLOSURE"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_ck_constraint_family_selection_after_source_admissibility_"
    "selects_bridge_admissibility_no_current_or_em_closure"
)
NEXT_TARGET = "prepare_toe_native_A_bridge_admissibility_ck_constraint_candidate_packet"
NEXT_TARGET_KIND = (
    "toe_native_A_bridge_admissibility_ck_constraint_candidate_packet_preparation"
)

SOURCE_ADMISSIBILITY_QUESTION = (
    "Can the vacuum U(1) gauge stress-energy route act as a bounded local "
    "on-shell source route?"
)

SELECTED_A_CK_OPTION_CLASS = "bridge_admissibility_constraint"
SELECTED_A_CK_CONSTRAINT_FAMILY = "A_bridge_admissibility_constraint_family"
SELECTED_FAMILY_SELECTION_STATUS = "selected_as_next_abstract_A_relevant_family"
PREVIOUS_A_CK_OPTION_CLASS = "source_admissibility_constraint"
PREVIOUS_A_CK_CONSTRAINT_FAMILY = SOURCE_SELECTED_A_CK_CONSTRAINT_FAMILY
PREVIOUS_FAMILY_STATUS = (
    "closed_as_vacuum_gauge_source_rule_reference_not_reselected"
)

A_TRANSPORT_CONSISTENCY_CONSTRAINT_FAMILY = (
    "A_transport_consistency_constraint_family"
)
A_TRANSPORT_CONSISTENCY_FAMILY_STATUS = "deferred_until_bridge_rule_exists"
A_CURRENT_COUPLING_CONSTRAINT_FAMILY = "A_current_coupling_constraint_family"
A_CURRENT_COUPLING_FAMILY_STATUS = "blocked_pending_J_nu_policy"
A_NONABELIAN_CONSTRAINT_FAMILY = "non_Abelian_A_constraint_family"
A_NONABELIAN_CONSTRAINT_FAMILY_DISPLAY = "non-Abelian A constraint family"
A_NONABELIAN_FAMILY_STATUS = "deferred_beyond_selected_U1_policy"
A_ADDITIONAL_SOURCE_RULE_ELABORATION = "additional source-rule elaboration"
A_ADDITIONAL_SOURCE_RULE_ELABORATION_STATUS = "deferred_after_source_closeout"

A_BRIDGE_ADMISSIBILITY_QUESTION = (
    "Does the A route correctly connect the selected U(1) gauge surface, the "
    "vacuum source-admissibility rule, and the master-action C_k layer "
    "without importing current-coupled or sourced EM closure?"
)
A_BRIDGE_CANDIDATE_SHAPE_PREVIEW = "C_bridge^A = 0"
A_BRIDGE_CANDIDATE_PLAIN_MEANING = (
    "The A route is admitted only if the selected U(1) gauge surface, vacuum "
    "source-admissibility rule, and master-action C_k layer align under the "
    "bounded vacuum policy."
)
A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE = [
    "master-action A surface",
    "selected U(1) policy",
    "vacuum gauge variation",
    "gauge stress-energy",
    "vacuum source-admissibility rule",
    "C_source^{A,nu}[g,A] = 0 closeout",
    "bounded bridge-admissibility candidate route",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY_"
    "20260622_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeACKConstraintFamilySelectionAfterSourceAdmissibility.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_family_options() -> list[dict[str, Any]]:
    return [
        {
            "constraint_option_class": SELECTED_A_CK_OPTION_CLASS,
            "constraint_family_id": SELECTED_A_CK_CONSTRAINT_FAMILY,
            "selection_status": SELECTED_FAMILY_SELECTION_STATUS,
            "A_relevance": "highest_next",
            "selection_reason": (
                "After source-admissibility, the next bounded A/C_k question "
                "is whether the selected U(1) gauge surface, the vacuum "
                "source rule, and the master-action C_k layer align as a "
                "bridge route without importing current or EM closure."
            ),
            "candidate_packet_target": NEXT_TARGET,
            "recommended_candidate_shape_preview": A_BRIDGE_CANDIDATE_SHAPE_PREVIEW,
            "bridge_candidate_constructed": False,
            "ck_action_embedding_constructed": False,
            "ck_variation_executed": False,
            "current_route_constructed": False,
            "em_closure_claimed": False,
        },
        {
            "constraint_option_class": "transport_consistency_constraint",
            "constraint_family_id": A_TRANSPORT_CONSISTENCY_CONSTRAINT_FAMILY,
            "selection_status": A_TRANSPORT_CONSISTENCY_FAMILY_STATUS,
            "A_relevance": "deferred",
            "selection_reason": (
                "Transport consistency should wait until an A bridge rule "
                "candidate exists."
            ),
            "candidate_packet_target": None,
            "bridge_candidate_constructed": False,
            "ck_action_embedding_constructed": False,
            "ck_variation_executed": False,
            "current_route_constructed": False,
            "em_closure_claimed": False,
        },
        {
            "constraint_option_class": "current_coupling_constraint",
            "constraint_family_id": A_CURRENT_COUPLING_CONSTRAINT_FAMILY,
            "selection_status": A_CURRENT_COUPLING_FAMILY_STATUS,
            "A_relevance": "blocked",
            "selection_reason": (
                "Current coupling remains blocked until a J^nu policy and "
                "matter/current exchange route are selected."
            ),
            "candidate_packet_target": None,
            "bridge_candidate_constructed": False,
            "ck_action_embedding_constructed": False,
            "ck_variation_executed": False,
            "current_route_constructed": False,
            "em_closure_claimed": False,
        },
        {
            "constraint_option_class": "nonabelian_constraint_family",
            "constraint_family_id": A_NONABELIAN_CONSTRAINT_FAMILY,
            "constraint_family_display": A_NONABELIAN_CONSTRAINT_FAMILY_DISPLAY,
            "selection_status": A_NONABELIAN_FAMILY_STATUS,
            "A_relevance": "deferred",
            "selection_reason": (
                "The active A branch remains the selected U(1) route; "
                "non-Abelian structure is outside this selector."
            ),
            "candidate_packet_target": None,
            "bridge_candidate_constructed": False,
            "ck_action_embedding_constructed": False,
            "ck_variation_executed": False,
            "current_route_constructed": False,
            "em_closure_claimed": False,
        },
        {
            "constraint_option_class": "additional_source_rule_elaboration",
            "constraint_family_id": A_ADDITIONAL_SOURCE_RULE_ELABORATION,
            "selection_status": A_ADDITIONAL_SOURCE_RULE_ELABORATION_STATUS,
            "A_relevance": "deferred",
            "selection_reason": (
                "Additional source-rule elaboration is deferred because the "
                "source rule has just been closed and the next missing family "
                "is bridge admissibility."
            ),
            "candidate_packet_target": None,
            "bridge_candidate_constructed": False,
            "ck_action_embedding_constructed": False,
            "ck_variation_executed": False,
            "current_route_constructed": False,
            "em_closure_claimed": False,
        },
    ]


def _selection_criteria(source_closeout: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_consumes_authorized_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": (
                "The selector consumes the active target authorized by the A "
                "source-admissibility rule closeout."
            ),
        },
        {
            "row_id": "source_admissibility_rule_closeout_accepted",
            "status": "accepted",
            "evidence": source_closeout.get("closeout_result"),
            "assessment": (
                "The closed vacuum U(1) source-admissibility rule is preserved "
                "as accepted context."
            ),
        },
        {
            "row_id": "source_rule_context_retained_not_reselected",
            "status": "accepted",
            "evidence": PREVIOUS_A_CK_CONSTRAINT_FAMILY,
            "assessment": (
                "The source-admissibility family is retained as the closed "
                "source-rule reference, not reselected."
            ),
        },
        {
            "row_id": "bridge_family_selected_as_next_A_relevant_family",
            "status": "accepted",
            "evidence": SELECTED_A_CK_CONSTRAINT_FAMILY,
            "assessment": (
                "A bridge-admissibility is selected as the next abstract "
                "A-relevant C_k family."
            ),
        },
        {
            "row_id": "transport_family_deferred_until_bridge_exists",
            "status": "accepted",
            "evidence": A_TRANSPORT_CONSISTENCY_FAMILY_STATUS,
            "assessment": (
                "A transport consistency is deferred until a bridge rule "
                "candidate exists."
            ),
        },
        {
            "row_id": "current_coupling_family_blocked_pending_J_nu_policy",
            "status": "accepted",
            "evidence": A_CURRENT_COUPLING_FAMILY_STATUS,
            "assessment": (
                "Current coupling remains blocked pending J^nu policy and "
                "matter/current exchange route work."
            ),
        },
        {
            "row_id": "nonabelian_family_deferred_beyond_selected_U1",
            "status": "accepted",
            "evidence": A_NONABELIAN_FAMILY_STATUS,
            "assessment": (
                "The non-Abelian A family is deferred beyond the selected U(1) "
                "route."
            ),
        },
        {
            "row_id": "additional_source_rule_elaboration_deferred_after_closeout",
            "status": "accepted",
            "evidence": A_ADDITIONAL_SOURCE_RULE_ELABORATION_STATUS,
            "assessment": (
                "Additional source-rule elaboration is deferred after the "
                "source-rule closeout."
            ),
        },
        {
            "row_id": "bridge_candidate_shape_only_previewed",
            "status": "accepted",
            "evidence": A_BRIDGE_CANDIDATE_SHAPE_PREVIEW,
            "assessment": (
                "C_bridge^A = 0 is only a preview for the next candidate "
                "packet, not a constructed C_k candidate here."
            ),
        },
        {
            "row_id": "next_candidate_packet_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next live target is the A bridge-admissibility C_k "
                "constraint candidate packet."
            ),
        },
        {
            "row_id": "no_candidate_action_variation_current_or_closure",
            "status": "accepted",
            "evidence": [
                "bridge_C_k_candidate_constructed=false",
                "C_k_action_embedding_constructed=false",
                "C_k_variation_executed=false",
                "J_nu_derived=false",
                "sourced_maxwell_closure_claimed=false",
                "full_em_closure_claimed=false",
            ],
            "assessment": (
                "The selector constructs no bridge candidate, embeds no C_k "
                "action term, executes no variation, derives no current, and "
                "claims no EM or QFT-GR closure."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_ck_constraint_family_selection_after_source_admissibility"
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
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_STATUS,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_toe_native_a_ck_constraint_family_selection_after_source_admissibility(
    *,
    source_rule_closeout_path: Path = SOURCE_RULE_CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    source_closeout = _read_json(source_rule_closeout_path)
    selection_criteria = _selection_criteria(source_closeout)
    options = _candidate_family_options()
    acceptance_criteria = {
        "consumes_expected_selector_target": (
            source_closeout.get("schema_id") == SOURCE_RULE_CLOSEOUT_SCHEMA_ID
            and source_closeout.get("packet_id") == SOURCE_RULE_CLOSEOUT_PACKET_ID
            and source_closeout.get("outcome_id") == SOURCE_RULE_CLOSEOUT_OUTCOME
            and source_closeout.get("closeout_result") == SOURCE_RULE_CLOSEOUT_RESULT
            and source_closeout.get("selected_next_target") == CONSUMED_TARGET
            and source_closeout.get("accepted") is True
        ),
        "source_rule_closeout_preserved": (
            source_closeout.get("candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and source_closeout.get("candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and source_closeout.get("candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and source_closeout.get("admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and source_closeout.get("candidate_recorded_as_rule_only") is True
            and source_closeout.get("candidate_recorded_as_action_term") is False
        ),
        "vacuum_u1_context_preserved": (
            source_closeout.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and source_closeout.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and source_closeout.get("F_definition_policy") == F_DEFINITION_POLICY
            and source_closeout.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and source_closeout.get("on_shell_vacuum_conservation_identity")
            == ON_SHELL_VACUUM_CONSERVATION_IDENTITY
        ),
        "bridge_selection_is_family_only": (
            SELECTED_A_CK_OPTION_CLASS == "bridge_admissibility_constraint"
            and SELECTED_A_CK_CONSTRAINT_FAMILY
            == "A_bridge_admissibility_constraint_family"
            and NEXT_TARGET
            == "prepare_toe_native_A_bridge_admissibility_ck_constraint_candidate_packet"
        ),
        "family_comparison_recorded": (
            len(options) == 5
            and options[0]["constraint_family_id"]
            == SELECTED_A_CK_CONSTRAINT_FAMILY
            and options[1]["selection_status"]
            == A_TRANSPORT_CONSISTENCY_FAMILY_STATUS
            and options[2]["selection_status"] == A_CURRENT_COUPLING_FAMILY_STATUS
            and options[3]["selection_status"] == A_NONABELIAN_FAMILY_STATUS
            and options[4]["selection_status"]
            == A_ADDITIONAL_SOURCE_RULE_ELABORATION_STATUS
        ),
        "no_forbidden_source_or_closure_claims": all(
            source_closeout.get(key) is False
            for key in [
                "ck_action_embedding_constructed",
                "C_k_action_embedding_constructed",
                "ck_variation_executed",
                "C_k_variation_executed",
                "J_nu_derived",
                "psi_current_route_constructed",
                "external_current_native_derivation_selected",
                "sourced_maxwell_equation_derived",
                "sourced_maxwell_closure_claimed",
                "matter_current_exchange_route_proved",
                "matter_gauge_energy_exchange_proved",
                "full_em_closure_claimed",
                "qft_gr_closure_claimed",
                "semiclassical_coupling_authorized",
                "empirical_validation_claimed",
                "master_action_promoted",
            ]
        ),
        "selection_criteria_all_accepted": all(
            row["status"] == "accepted" for row in selection_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY_REQUIRES_REMEDIATION",
        "selection_result": SELECTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_rule_closeout_result": SOURCE_RULE_CLOSEOUT_RESULT,
        "source_selected_A_ck_option_class": PREVIOUS_A_CK_OPTION_CLASS,
        "source_selected_A_ck_constraint_family": PREVIOUS_A_CK_CONSTRAINT_FAMILY,
        "source_family_status": PREVIOUS_FAMILY_STATUS,
        "source_admissibility_question": SOURCE_ADMISSIBILITY_QUESTION,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_candidate_constraint_short_form": SOURCE_CANDIDATE_CONSTRAINT_SHORT_FORM,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "source_first_A_rule_classification": FIRST_A_RULE_CLASSIFICATION,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "bianchi_identity_route": BIANCHI_IDENTITY_ROUTE,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "stress_energy_under_selected_u1_policy": (
            STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
        ),
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "divergence_identity": DIVERGENCE_IDENTITY,
        "vacuum_supporting_identity_form": VACUUM_SUPPORTING_IDENTITY_FORM,
        "vacuum_on_shell_implication_form": VACUUM_ON_SHELL_IMPLICATION_FORM,
        "on_shell_vacuum_conservation_identity": (
            ON_SHELL_VACUUM_CONSERVATION_IDENTITY
        ),
        "bounded_source_admissibility_result": BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
        "local_source_route_scope": LOCAL_SOURCE_ROUTE_SCOPE,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "selected_A_ck_option_class": SELECTED_A_CK_OPTION_CLASS,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "selected_family_selection_status": SELECTED_FAMILY_SELECTION_STATUS,
        "A_bridge_admissibility_question": A_BRIDGE_ADMISSIBILITY_QUESTION,
        "A_bridge_candidate_shape_preview": A_BRIDGE_CANDIDATE_SHAPE_PREVIEW,
        "A_bridge_candidate_plain_meaning": A_BRIDGE_CANDIDATE_PLAIN_MEANING,
        "A_bridge_route_alignment_sequence": A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
        "A_bridge_route_alignment_sequence_count": len(
            A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE
        ),
        "A_transport_consistency_constraint_family": (
            A_TRANSPORT_CONSISTENCY_CONSTRAINT_FAMILY
        ),
        "A_transport_consistency_family_status": (
            A_TRANSPORT_CONSISTENCY_FAMILY_STATUS
        ),
        "A_current_coupling_constraint_family": A_CURRENT_COUPLING_CONSTRAINT_FAMILY,
        "A_current_coupling_family_status": A_CURRENT_COUPLING_FAMILY_STATUS,
        "A_nonabelian_constraint_family": A_NONABELIAN_CONSTRAINT_FAMILY,
        "A_nonabelian_constraint_family_display": (
            A_NONABELIAN_CONSTRAINT_FAMILY_DISPLAY
        ),
        "A_nonabelian_family_status": A_NONABELIAN_FAMILY_STATUS,
        "A_additional_source_rule_elaboration": A_ADDITIONAL_SOURCE_RULE_ELABORATION,
        "A_additional_source_rule_elaboration_status": (
            A_ADDITIONAL_SOURCE_RULE_ELABORATION_STATUS
        ),
        "candidate_family_options": options,
        "candidate_family_option_count": len(options),
        "selection_criteria": selection_criteria,
        "selection_criteria_count": len(selection_criteria),
        "selection_criteria_accepted_count": sum(
            1 for row in selection_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "selector_target_prepared": True,
        "selector_target_accepted": True,
        "selection_executed": True,
        "A_bridge_admissibility_family_selected": True,
        "A_bridge_admissibility_recommended_only": False,
        "A_bridge_admissibility_candidate_packet_authorized": True,
        "A_bridge_admissibility_candidate_packet_prepared": False,
        "A_bridge_candidate_shape_preview_recorded": True,
        "A_bridge_candidate_constructed": False,
        "bridge_C_k_candidate_constructed": False,
        "A_bridge_candidate_functional_defined": False,
        "A_bridge_candidate_functional_selected": False,
        "A_bridge_candidate_rule_proved": False,
        "A_bridge_route_alignment_sequence_recorded": True,
        "A_bridge_route_alignment_verified": False,
        "A_transport_consistency_family_deferred": True,
        "A_current_coupling_family_blocked_pending_J_nu_policy": True,
        "nonabelian_A_family_deferred": True,
        "additional_source_rule_elaboration_deferred": True,
        "source_admissibility_family_reselected": False,
        "source_admissibility_family_completed": False,
        "source_admissibility_family_closed_as_candidate_only": True,
        "source_rule_candidate_retained_as_context": True,
        "source_rule_candidate_reopened": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "candidate_action_insertion_executed": False,
        "ck_action_embedding_constructed": False,
        "ck_action_embedding_selected": False,
        "C_k_action_embedding_constructed": False,
        "C_k_action_embedding_selected": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "C_k_variation_executed": False,
        "C_k_variation_authorized": False,
        "lambda_variation_executed": False,
        "metric_variation_of_candidate_executed": False,
        "A_variation_of_candidate_executed": False,
        "constraint_multiplier_type_selected": False,
        "constraint_term_selected": False,
        "lambda_nu_domain_selected": False,
        "higher_derivative_scope_resolved": False,
        "boundary_terms_controlled": False,
        "new_conservation_proof_claimed": False,
        "new_source_admissibility_proof_claimed": False,
        "full_source_admissibility_review_accepted": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "source_admissibility_proved": False,
        "A_source_admissibility_claimed": False,
        "A_source_admissibility_proved": False,
        "stress_energy_as_gravity_source_authorized": False,
        "stress_energy_source_admissibility_proved": False,
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
        "em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_source_established": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "claim_level": (
            "Level 3 selector; selects the A bridge-admissibility C_k family "
            "after vacuum U(1) source-admissibility rule closeout without "
            "constructing the bridge candidate, deriving current, executing "
            "C_k variation, or promoting the master action"
        ),
        "claim_ceiling": (
            "abstract A-relevant C_k family selection only no bridge C_k "
            "candidate constructed no C_k action embedding no C_k variation no "
            "J^nu derivation no sourced Maxwell no matter-current exchange no "
            "full EM closure no QFT-GR closure no semiclassical coupling no "
            "empirical validation no master-action promotion"
        ),
        "mathematical_statement": (
            "The selector retains the closed vacuum U(1) source-admissibility "
            "rule C_source^{A,nu}[g,A] = 0 as context and selects "
            "A_bridge_admissibility_constraint_family as the next abstract "
            "A-relevant C_k family to test. The next packet may test a "
            "candidate shaped like C_bridge^A = 0 for route alignment, but no "
            "such candidate is constructed here."
        ),
        "non_claim_boundary": (
            "This selector only chooses the A bridge-admissibility C_k family "
            "as the next abstract family after the vacuum U(1) source-rule "
            "closeout. It does not construct C_bridge^A, does not prove bridge "
            "admissibility, does not verify route alignment, does not embed "
            "C_k in the action, does not execute C_k variation, does not "
            "derive J^nu, does not derive a psi-current or external-current "
            "native route, does not derive sourced Maxwell, does not prove "
            "matter-current or matter-gauge exchange, does not close EM, does "
            "not close QFT-GR, does not authorize semiclassical coupling, does "
            "not promote the master action, and does not claim empirical "
            "validation or public readiness."
        ),
        "critical_gate_fail_conditions": [
            "construct the bridge C_k candidate in this selector",
            "claim C_bridge^A is proved",
            "embed C_k into the action",
            "execute C_k variation",
            "derive J^nu",
            "derive sourced Maxwell",
            "prove matter-current exchange",
            "claim full EM closure",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_STATUS,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeACKConstraintFamilySelectionAfterSourceAdmissibility",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "source_rule_closeout_file": _ptr(source_rule_closeout_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_selection(selection: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(selection, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A C_k family selector after source-admissibility."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    selection = build_toe_native_a_ck_constraint_family_selection_after_source_admissibility(
        captured_at_utc=args.captured_at_utc
    )
    path = write_selection(selection, args.out)
    print(
        json.dumps(
            {
                "accepted": selection["accepted"],
                "out": _ptr(path),
                "selected_next_target": selection["selected_next_target"],
                "selection_result": selection["selection_result"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
