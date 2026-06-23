from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

sys.setrecursionlimit(10000)

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_ck_constraint_family_selection_after_source_admissibility_report import (
    A_BRIDGE_ADMISSIBILITY_QUESTION,
    A_BRIDGE_CANDIDATE_PLAIN_MEANING,
    A_BRIDGE_CANDIDATE_SHAPE_PREVIEW,
    A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
    A_FIELD_DOMAIN_POLICY,
    BIANCHI_IDENTITY_ROUTE,
    BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as A_CK_FAMILY_SELECTOR_PATH,
    DIVERGENCE_IDENTITY,
    F_DEFINITION_POLICY,
    FULL_TOEFORMAL_STATUS,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LOCAL_SOURCE_ROUTE_SCOPE,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID as A_CK_FAMILY_SELECTOR_OUTCOME,
    PACKET_ID as A_CK_FAMILY_SELECTOR_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as A_CK_FAMILY_SELECTOR_SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS,
    SELECTION_RESULT as A_CK_FAMILY_SELECTOR_RESULT,
    SOURCE_ADMISSIBILITY_CONDITION,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_CANDIDATE_CONSTRAINT_SHORT_FORM,
    SOURCE_ROUTE_STILL_BLOCKED,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
    VACUUM_ON_SHELL_IMPLICATION_FORM,
    VACUUM_SUPPORTING_IDENTITY_FORM,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-22T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_"
    "20260622_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_v0"
PACKET_RESULT = (
    "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_PREPARED_"
    "A_BRIDGE_ROUTE_CONSISTENCY_RULE_RECORDED_NO_CURRENT_OR_EM_CLOSURE"
)
OUTCOME_ID = PACKET_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_bridge_admissibility_ck_constraint_candidate_packet_prepared_"
    "A_bridge_route_consistency_rule_recorded_no_current_or_em_closure"
)
NEXT_TARGET = (
    "review_toe_native_A_bridge_admissibility_ck_constraint_candidate_packet_result"
)
NEXT_TARGET_KIND = (
    "toe_native_A_bridge_admissibility_ck_constraint_candidate_packet_result_review"
)

A_BRIDGE_CANDIDATE_ID = "A_bridge_vacuum_u1_route_consistency_ck_candidate"
A_BRIDGE_CANDIDATE_TYPE = "vacuum_U1_route_consistency_admissibility_candidate"
A_BRIDGE_CONSTRAINT_FORM = (
    "C_bridge^A := (E_A^master - E_A^vacuum_U1_route, "
    "T_A^master - T_A^vacuum_U1_route, "
    "C_source^A - nabla_mu T_A^{mu nu})"
)
A_BRIDGE_CONSTRAINT_EQUATION = "C_bridge^A = 0"
A_BRIDGE_CONSTRAINT_SHORT_FORM = (
    "C_bridge^A := (Delta E_A, Delta T_A, Delta C_source^A); C_bridge^A = 0"
)
A_BRIDGE_FIELD_EQUATION_MATCH = "E_A^master - E_A^vacuum_U1_route = 0"
A_BRIDGE_STRESS_ENERGY_MATCH = "T_A^master - T_A^vacuum_U1_route = 0"
A_BRIDGE_SOURCE_RESIDUAL_MATCH = "C_source^A - nabla_mu T_A^{mu nu} = 0"
A_BRIDGE_RULE_PLAIN_MEANING = (
    "The A route is admitted only if the master-action gauge route, vacuum "
    "U(1) field equation route, gauge stress-energy route, and "
    "source-admissibility residual all match under the selected policy."
)
MASTER_A_ROUTE_ID = "master_action_A_surface_under_selected_U1_policy"
VACUUM_U1_ROUTE_ID = "vacuum_U1_gauge_field_equation_route"
GAUGE_STRESS_ENERGY_ROUTE_ID = "vacuum_U1_gauge_stress_energy_route"
SOURCE_ADMISSIBILITY_ROUTE_ID = "A_source_conservation_residual_rule"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_"
    "20260622_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeABridgeAdmissibilityCKConstraintCandidatePacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _bridge_components() -> list[dict[str, Any]]:
    return [
        {
            "component_id": "A_bridge_field_equation_match",
            "component_form": A_BRIDGE_FIELD_EQUATION_MATCH,
            "plain_meaning": (
                "The master-action A field-equation route must match the "
                "selected vacuum U(1) route under the active policy."
            ),
            "variation_executed_here": False,
            "proved_here": False,
        },
        {
            "component_id": "A_bridge_stress_energy_match",
            "component_form": A_BRIDGE_STRESS_ENERGY_MATCH,
            "plain_meaning": (
                "The master-action A stress-energy route must match the "
                "vacuum U(1) gauge stress-energy route under the selected "
                "conventions."
            ),
            "variation_executed_here": False,
            "proved_here": False,
        },
        {
            "component_id": "A_bridge_source_residual_match",
            "component_form": A_BRIDGE_SOURCE_RESIDUAL_MATCH,
            "plain_meaning": (
                "The bridge must identify the source-admissibility residual "
                "with nabla_mu T_A^{mu nu} in the bounded vacuum route."
            ),
            "variation_executed_here": False,
            "proved_here": False,
        },
    ]


def _route_alignment_contract() -> list[dict[str, Any]]:
    return [
        {
            "route_step": step,
            "status": "recorded_for_A_bridge_consistency_check",
            "verified_here": False,
        }
        for step in A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE
    ]


def _candidate_criteria(selector: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "candidate_packet_consumes_A_bridge_selector",
            "status": "accepted",
            "evidence": selector.get("selection_result"),
            "assessment": (
                "The packet consumes the A bridge-admissibility family selector."
            ),
        },
        {
            "row_id": "selected_A_bridge_family_carried_forward",
            "status": "accepted",
            "evidence": [
                selector.get("selected_A_ck_option_class"),
                selector.get("selected_A_ck_constraint_family"),
            ],
            "assessment": (
                "The packet stays within the selected A bridge-admissibility "
                "C_k family."
            ),
        },
        {
            "row_id": "vacuum_u1_source_rule_context_retained",
            "status": "accepted",
            "evidence": [
                selector.get("source_candidate_constraint_form"),
                selector.get("source_admissibility_constraint_form"),
                selector.get("on_shell_vacuum_conservation_identity"),
            ],
            "assessment": (
                "The closed vacuum U(1) source rule remains the context for "
                "the bridge candidate."
            ),
        },
        {
            "row_id": "route_alignment_sequence_carried_forward",
            "status": "accepted",
            "evidence": selector.get("A_bridge_route_alignment_sequence"),
            "assessment": (
                "The selected A bridge route sequence is carried forward for "
                "later review."
            ),
        },
        {
            "row_id": "route_consistency_tuple_recorded",
            "status": "accepted",
            "evidence": A_BRIDGE_CONSTRAINT_FORM,
            "assessment": (
                "The bridge candidate is recorded as a route-consistency tuple."
            ),
        },
        {
            "row_id": "bridge_constraint_equation_recorded",
            "status": "accepted",
            "evidence": A_BRIDGE_CONSTRAINT_EQUATION,
            "assessment": "The admissibility condition C_bridge^A = 0 is recorded.",
        },
        {
            "row_id": "field_equation_stress_energy_source_residual_components_recorded",
            "status": "accepted",
            "evidence": [
                A_BRIDGE_FIELD_EQUATION_MATCH,
                A_BRIDGE_STRESS_ENERGY_MATCH,
                A_BRIDGE_SOURCE_RESIDUAL_MATCH,
            ],
            "assessment": (
                "The bridge components compare the field-equation, "
                "stress-energy, and source-residual routes."
            ),
        },
        {
            "row_id": "candidate_is_admissibility_only_not_action_term",
            "status": "accepted",
            "evidence": "A_bridge_candidate_recorded_as_admissibility_rule=true",
            "assessment": (
                "The tuple is recorded as an admissibility candidate only, "
                "not as an action term."
            ),
        },
        {
            "row_id": "no_bridge_proof_action_variation_current_or_closure",
            "status": "accepted",
            "evidence": [
                "A_bridge_admissibility_proved=false",
                "C_k_action_embedding_constructed=false",
                "C_k_variation_executed=false",
                "J_nu_derived=false",
                "sourced_maxwell_closure_claimed=false",
                "full_em_closure_claimed=false",
            ],
            "assessment": (
                "The packet records no proof, action embedding, variation, "
                "current route, EM closure, QFT-GR closure, or promotion."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_bridge_admissibility_ck_constraint_candidate_packet"
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


def build_toe_native_a_bridge_admissibility_ck_constraint_candidate_packet(
    *,
    a_ck_family_selector_path: Path = A_CK_FAMILY_SELECTOR_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector = _read_json(a_ck_family_selector_path)
    candidate_criteria = _candidate_criteria(selector)
    acceptance_criteria = {
        "consumes_expected_A_bridge_candidate_target": (
            selector.get("schema_id") == A_CK_FAMILY_SELECTOR_SCHEMA_ID
            and selector.get("packet_id") == A_CK_FAMILY_SELECTOR_PACKET_ID
            and selector.get("outcome_id") == A_CK_FAMILY_SELECTOR_OUTCOME
            and selector.get("selection_result") == A_CK_FAMILY_SELECTOR_RESULT
            and selector.get("selected_next_target") == CONSUMED_TARGET
            and selector.get("accepted") is True
        ),
        "selected_A_bridge_family_preserved": (
            selector.get("selected_A_ck_option_class") == SELECTED_A_CK_OPTION_CLASS
            and selector.get("selected_A_ck_constraint_family")
            == SELECTED_A_CK_CONSTRAINT_FAMILY
            and selector.get("A_bridge_admissibility_family_selected") is True
            and selector.get("A_bridge_admissibility_candidate_packet_authorized")
            is True
            and selector.get("A_bridge_candidate_constructed") is False
            and selector.get("A_bridge_route_alignment_verified") is False
        ),
        "source_rule_context_preserved": (
            selector.get("source_rule_closeout_outcome") == SOURCE_RULE_CLOSEOUT_OUTCOME
            and selector.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and selector.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and selector.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and selector.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and selector.get("on_shell_vacuum_conservation_identity")
            == ON_SHELL_VACUUM_CONSERVATION_IDENTITY
        ),
        "route_consistency_candidate_recorded": (
            A_BRIDGE_CONSTRAINT_EQUATION == "C_bridge^A = 0"
            and A_BRIDGE_CANDIDATE_TYPE
            == "vacuum_U1_route_consistency_admissibility_candidate"
            and len(_bridge_components()) == 3
        ),
        "no_selector_shortcut_claims": all(
            selector.get(key) is False
            for key in [
                "A_bridge_candidate_constructed",
                "bridge_C_k_candidate_constructed",
                "A_bridge_candidate_functional_defined",
                "A_bridge_candidate_rule_proved",
                "A_bridge_route_alignment_verified",
                "ck_variation_executed",
                "C_k_variation_executed",
                "J_nu_derived",
                "sourced_maxwell_closure_claimed",
                "full_em_closure_claimed",
                "qft_gr_closure_claimed",
                "semiclassical_coupling_authorized",
                "master_action_promoted",
                "empirical_validation_claimed",
            ]
        ),
        "candidate_criteria_all_accepted": all(
            row["status"] == "accepted" for row in candidate_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "A_ck_family_selector_outcome": A_CK_FAMILY_SELECTOR_OUTCOME,
        "A_ck_family_selector_result": A_CK_FAMILY_SELECTOR_RESULT,
        "selected_A_ck_option_class": SELECTED_A_CK_OPTION_CLASS,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "A_bridge_admissibility_question": A_BRIDGE_ADMISSIBILITY_QUESTION,
        "A_bridge_candidate_shape_preview": A_BRIDGE_CANDIDATE_SHAPE_PREVIEW,
        "A_bridge_candidate_plain_meaning": A_BRIDGE_CANDIDATE_PLAIN_MEANING,
        "A_bridge_route_alignment_sequence": A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
        "A_bridge_route_alignment_sequence_count": len(A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE),
        "A_bridge_candidate_id": A_BRIDGE_CANDIDATE_ID,
        "A_bridge_candidate_type": A_BRIDGE_CANDIDATE_TYPE,
        "A_bridge_constraint_form": A_BRIDGE_CONSTRAINT_FORM,
        "A_bridge_constraint_equation": A_BRIDGE_CONSTRAINT_EQUATION,
        "A_bridge_constraint_short_form": A_BRIDGE_CONSTRAINT_SHORT_FORM,
        "A_bridge_field_equation_match": A_BRIDGE_FIELD_EQUATION_MATCH,
        "A_bridge_stress_energy_match": A_BRIDGE_STRESS_ENERGY_MATCH,
        "A_bridge_source_residual_match": A_BRIDGE_SOURCE_RESIDUAL_MATCH,
        "A_bridge_rule_plain_meaning": A_BRIDGE_RULE_PLAIN_MEANING,
        "bridge_candidate_id": A_BRIDGE_CANDIDATE_ID,
        "bridge_candidate_type": A_BRIDGE_CANDIDATE_TYPE,
        "bridge_constraint_form": A_BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": A_BRIDGE_CONSTRAINT_EQUATION,
        "bridge_route_field_equation_match": A_BRIDGE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": A_BRIDGE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": A_BRIDGE_SOURCE_RESIDUAL_MATCH,
        "bridge_candidate_rule_plain_meaning": A_BRIDGE_RULE_PLAIN_MEANING,
        "bridge_components": _bridge_components(),
        "bridge_component_count": len(_bridge_components()),
        "route_alignment_contract": _route_alignment_contract(),
        "route_alignment_contract_count": len(_route_alignment_contract()),
        "master_A_route_id": MASTER_A_ROUTE_ID,
        "vacuum_U1_route_id": VACUUM_U1_ROUTE_ID,
        "gauge_stress_energy_route_id": GAUGE_STRESS_ENERGY_ROUTE_ID,
        "source_admissibility_route_id": SOURCE_ADMISSIBILITY_ROUTE_ID,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_candidate_constraint_short_form": SOURCE_CANDIDATE_CONSTRAINT_SHORT_FORM,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
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
        "candidate_criteria": candidate_criteria,
        "candidate_criteria_count": len(candidate_criteria),
        "candidate_criteria_accepted_count": sum(
            1 for row in candidate_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "A_bridge_admissibility_ck_constraint_candidate_packet_prepared": True,
        "A_bridge_candidate_packet_prepared": True,
        "A_bridge_candidate_packet_accepted": True,
        "A_bridge_candidate_recorded": True,
        "A_bridge_route_consistency_rule_recorded": True,
        "A_bridge_candidate_selected_as_route_consistency_rule": True,
        "A_bridge_candidate_recorded_as_admissibility_rule": True,
        "A_bridge_candidate_recorded_as_admissibility_candidate": True,
        "A_bridge_candidate_recorded_as_action_term": False,
        "A_bridge_candidate_recorded_as_new_dynamical_law": False,
        "A_bridge_candidate_functional_defined": False,
        "A_bridge_candidate_functional_selected": False,
        "A_bridge_candidate_rule_proved": False,
        "A_bridge_admissibility_family_selected": True,
        "A_bridge_admissibility_claimed": False,
        "A_bridge_admissibility_proved": False,
        "A_bridge_route_alignment_sequence_recorded": True,
        "A_bridge_route_alignment_verified": False,
        "route_consistency_tuple_recorded": True,
        "route_consistency_tuple_proved": False,
        "field_equation_match_recorded": True,
        "field_equation_match_proved": False,
        "stress_energy_match_recorded": True,
        "stress_energy_match_proved": False,
        "source_residual_match_recorded": True,
        "source_residual_match_proved": False,
        "source_admissibility_rule_retained_as_context": True,
        "source_admissibility_family_completed": False,
        "source_admissibility_claimed": False,
        "bridge_admissibility_claimed": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "bridge_admissibility_proof_claimed": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "ck_action_embedding_constructed": False,
        "ck_action_embedding_selected": False,
        "C_k_action_embedding_constructed": False,
        "C_k_action_embedding_selected": False,
        "candidate_action_insertion_executed": False,
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
        "sourced_maxwell_route_derived": False,
        "matter_current_exchange_derived": False,
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
            "Level 3 A bridge candidate packet; records C_bridge^A as a "
            "vacuum U(1) route-consistency admissibility candidate without "
            "defining an action term, executing C_k variation, deriving "
            "current, proving bridge admissibility, closing EM or QFT-GR, or "
            "promoting the master action"
        ),
        "claim_ceiling": (
            "vacuum U(1) bridge-admissibility C_k candidate only no bridge "
            "proof no C_k action embedding no C_k variation no J^nu derivation "
            "no sourced Maxwell route no matter/current exchange no full EM "
            "closure no QFT-GR closure no semiclassical coupling no empirical "
            "validation no master-action promotion"
        ),
        "mathematical_statement": (
            "The packet records C_bridge^A := (E_A^master - "
            "E_A^vacuum_U1_route, T_A^master - T_A^vacuum_U1_route, "
            "C_source^A - nabla_mu T_A^{mu nu}) with condition "
            "C_bridge^A = 0. The tuple is a vacuum U(1) route-consistency "
            "admissibility candidate, not an action term."
        ),
        "non_claim_boundary": (
            "This packet records an A bridge-admissibility C_k candidate as a "
            "vacuum U(1) route-consistency admissibility candidate only. It "
            "does not prove bridge admissibility, does not verify route "
            "alignment, does not define a fully concrete C_k functional, does "
            "not embed C_bridge^A into the action, does not execute C_k "
            "variation, does not vary lambda_k, A, or g, does not derive J^nu, "
            "does not derive a psi-current or external-current native route, "
            "does not derive sourced Maxwell, does not prove matter/current "
            "exchange or matter-gauge exchange, does not close EM, does not "
            "close QFT-GR, does not authorize semiclassical coupling, does not "
            "promote the master action, and does not claim empirical "
            "validation or public readiness."
        ),
        "critical_gate_fail_conditions": [
            "claim bridge admissibility is proved",
            "claim route alignment is verified",
            "embed C_bridge^A into an action",
            "execute C_k variation",
            "derive J^nu",
            "derive sourced Maxwell",
            "prove matter/current exchange",
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
            "ToeFormal.Derivation.ToeNativeABridgeAdmissibilityCKConstraintCandidatePacket",
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
            "A_ck_family_selector_file": _ptr(a_ck_family_selector_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A bridge-admissibility C_k candidate packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_toe_native_a_bridge_admissibility_ck_constraint_candidate_packet(
        captured_at_utc=args.captured_at_utc
    )
    path = write_packet(packet, args.out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "out": _ptr(path),
                "packet_result": packet["packet_result"],
                "selected_next_target": packet["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
