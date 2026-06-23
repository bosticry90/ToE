from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_bridge_admissibility_ck_constraint_candidate_packet_report import (
    A_BRIDGE_CANDIDATE_ID,
    A_BRIDGE_CANDIDATE_TYPE,
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    A_BRIDGE_CONSTRAINT_SHORT_FORM,
    A_BRIDGE_FIELD_EQUATION_MATCH,
    A_BRIDGE_RULE_PLAIN_MEANING,
    A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
    A_BRIDGE_SOURCE_RESIDUAL_MATCH,
    A_BRIDGE_STRESS_ENERGY_MATCH,
    A_FIELD_DOMAIN_POLICY,
    BIANCHI_IDENTITY_ROUTE,
    BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as CANDIDATE_PACKET_PATH,
    DIVERGENCE_IDENTITY,
    F_DEFINITION_POLICY,
    FULL_TOEFORMAL_STATUS,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LOCAL_SOURCE_ROUTE_SCOPE,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID as CANDIDATE_PACKET_OUTCOME,
    PACKET_ID as CANDIDATE_PACKET_ID,
    PACKET_RESULT as CANDIDATE_PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as CANDIDATE_PACKET_SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS,
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
    "RESULT_REVIEW_20260622_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_"
    "RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_RESULT_REVIEW_"
    "ACCEPTS_VACUUM_U1_ROUTE_CONSISTENCY_CANDIDATE_"
    "NO_FUNCTIONALIZATION_OR_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_bridge_admissibility_ck_constraint_candidate_result_review_"
    "accepts_vacuum_u1_route_consistency_candidate_no_functionalization_or_promotion"
)
NEXT_TARGET = "prepare_toe_native_A_bridge_admissibility_ck_functional_embedding_packet"
NEXT_TARGET_KIND = (
    "toe_native_A_bridge_admissibility_ck_functional_embedding_packet_preparation"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_"
    "RESULT_REVIEW_20260622_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeABridgeAdmissibilityCKConstraintCandidatePacketResultReview.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "candidate_review_target_consumed",
            "status": "accepted",
            "evidence": packet.get("selected_next_target"),
            "assessment": "The active A bridge C_k candidate result-review target is consumed.",
        },
        {
            "row_id": "C_bridge_A_tuple_preserved_exactly",
            "status": "accepted",
            "evidence": A_BRIDGE_CONSTRAINT_FORM,
            "assessment": "The A bridge route-consistency tuple is preserved exactly.",
        },
        {
            "row_id": "C_bridge_A_equation_preserved_exactly",
            "status": "accepted",
            "evidence": A_BRIDGE_CONSTRAINT_EQUATION,
            "assessment": "The bridge condition C_bridge^A = 0 is preserved.",
        },
        {
            "row_id": "E_A_route_match_component_preserved",
            "status": "accepted",
            "evidence": A_BRIDGE_FIELD_EQUATION_MATCH,
            "assessment": "The E_A route match component is preserved.",
        },
        {
            "row_id": "T_A_route_match_component_preserved",
            "status": "accepted",
            "evidence": A_BRIDGE_STRESS_ENERGY_MATCH,
            "assessment": "The T_A route match component is preserved.",
        },
        {
            "row_id": "C_source_A_residual_match_component_preserved",
            "status": "accepted",
            "evidence": A_BRIDGE_SOURCE_RESIDUAL_MATCH,
            "assessment": "The C_source^A residual match component is preserved.",
        },
        {
            "row_id": "vacuum_u1_scope_preserved",
            "status": "accepted",
            "evidence": [
                GAUGE_GROUP_POLICY,
                A_FIELD_DOMAIN_POLICY,
                F_DEFINITION_POLICY,
                LOCAL_SOURCE_ROUTE_SCOPE,
            ],
            "assessment": "The local classical vacuum U(1) scope is preserved.",
        },
        {
            "row_id": "source_rule_context_preserved",
            "status": "accepted",
            "evidence": [
                SOURCE_CANDIDATE_CONSTRAINT_FORM,
                SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            ],
            "assessment": "The closed A source-admissibility rule remains context.",
        },
        {
            "row_id": "no_bridge_proof_or_route_verification",
            "status": "accepted",
            "evidence": [
                "A_bridge_admissibility_proved=false",
                "route_consistency_tuple_proved=false",
                "A_bridge_route_alignment_verified=false",
            ],
            "assessment": "The review accepts candidate status without proving bridge admissibility.",
        },
        {
            "row_id": "no_ck_action_embedding_or_variation",
            "status": "accepted",
            "evidence": [
                "C_k_action_embedding_constructed=false",
                "candidate_action_insertion_executed=false",
                "C_k_variation_executed=false",
                "lambda_variation_executed=false",
            ],
            "assessment": "No C_k action embedding or variation is executed.",
        },
        {
            "row_id": "no_current_sourced_maxwell_or_exchange_route",
            "status": "accepted",
            "evidence": [
                "J_nu_derived=false",
                "psi_current_route_constructed=false",
                "external_current_native_derivation_selected=false",
                "sourced_maxwell_equation_derived=false",
                "matter_current_exchange_route_proved=false",
            ],
            "assessment": "No current route, sourced Maxwell route, or matter/current exchange is introduced.",
        },
        {
            "row_id": "no_closure_coupling_validation_or_promotion",
            "status": "accepted",
            "evidence": [
                "full_em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "semiclassical_coupling_authorized=false",
                "empirical_validation_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No EM closure, QFT-GR closure, coupling, validation, or promotion follows.",
        },
        {
            "row_id": "functional_embedding_next_target_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next bounded packet asks whether the bridge rule remains "
                "admissibility-only or can be embedded as an action constraint."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_bridge_admissibility_ck_constraint_candidate_packet_"
            "result_review"
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


def build_toe_native_a_bridge_admissibility_ck_constraint_candidate_packet_result_review(
    *,
    candidate_packet_path: Path = CANDIDATE_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(candidate_packet_path)
    criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_review_target": (
            packet.get("schema_id") == CANDIDATE_PACKET_SCHEMA_ID
            and packet.get("packet_id") == CANDIDATE_PACKET_ID
            and packet.get("outcome_id") == CANDIDATE_PACKET_OUTCOME
            and packet.get("packet_result") == CANDIDATE_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "candidate_tuple_exact": (
            packet.get("A_bridge_candidate_id") == A_BRIDGE_CANDIDATE_ID
            and packet.get("A_bridge_candidate_type") == A_BRIDGE_CANDIDATE_TYPE
            and packet.get("A_bridge_constraint_form") == A_BRIDGE_CONSTRAINT_FORM
            and packet.get("A_bridge_constraint_equation")
            == A_BRIDGE_CONSTRAINT_EQUATION
            and packet.get("A_bridge_constraint_short_form")
            == A_BRIDGE_CONSTRAINT_SHORT_FORM
        ),
        "route_components_exact": (
            packet.get("A_bridge_field_equation_match")
            == A_BRIDGE_FIELD_EQUATION_MATCH
            and packet.get("A_bridge_stress_energy_match")
            == A_BRIDGE_STRESS_ENERGY_MATCH
            and packet.get("A_bridge_source_residual_match")
            == A_BRIDGE_SOURCE_RESIDUAL_MATCH
        ),
        "selected_family_exact": (
            packet.get("selected_A_ck_option_class") == SELECTED_A_CK_OPTION_CLASS
            and packet.get("selected_A_ck_constraint_family")
            == SELECTED_A_CK_CONSTRAINT_FAMILY
        ),
        "vacuum_u1_scope_preserved": (
            packet.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and packet.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and packet.get("F_definition_policy") == F_DEFINITION_POLICY
            and packet.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and packet.get("on_shell_vacuum_conservation_identity")
            == ON_SHELL_VACUUM_CONSERVATION_IDENTITY
        ),
        "source_rule_context_exact": (
            packet.get("source_rule_closeout_outcome") == SOURCE_RULE_CLOSEOUT_OUTCOME
            and packet.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and packet.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and packet.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and packet.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "candidate_only_boundary_carried_forward": (
            packet.get("A_bridge_candidate_recorded") is True
            and packet.get("A_bridge_candidate_recorded_as_admissibility_rule")
            is True
            and packet.get("A_bridge_candidate_recorded_as_action_term") is False
            and packet.get("A_bridge_candidate_recorded_as_new_dynamical_law")
            is False
            and packet.get("A_bridge_candidate_rule_proved") is False
            and packet.get("A_bridge_admissibility_claimed") is False
            and packet.get("A_bridge_admissibility_proved") is False
        ),
        "no_functionalization_or_variation": all(
            packet.get(key) is False
            for key in [
                "A_bridge_candidate_functional_defined",
                "A_bridge_candidate_functional_selected",
                "concrete_ck_functional_selected",
                "concrete_ck_functional_defined",
                "fully_concrete_ck_functional_selected",
                "fully_concrete_ck_functional_defined",
                "ck_action_embedding_constructed",
                "C_k_action_embedding_constructed",
                "candidate_action_insertion_executed",
                "ck_variation_executed",
                "C_k_variation_executed",
                "lambda_variation_executed",
                "metric_variation_of_candidate_executed",
                "A_variation_of_candidate_executed",
            ]
        ),
        "no_current_sourced_em_closure_or_promotion": all(
            packet.get(key) is False
            for key in [
                "J_nu_derived",
                "psi_current_route_constructed",
                "external_current_native_derivation_selected",
                "sourced_maxwell_equation_derived",
                "sourced_maxwell_route_derived",
                "matter_current_exchange_route_proved",
                "matter_gauge_energy_exchange_proved",
                "full_em_closure_claimed",
                "qft_gr_closure_claimed",
                "semiclassical_coupling_authorized",
                "empirical_validation_claimed",
                "master_action_promoted",
                "canonical_master_action_promoted",
            ]
        ),
        "criteria_all_accepted": all(row["status"] == "accepted" for row in criteria),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CANDIDATE_REVIEW"
    )
    route_sequence = " -> ".join(A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE)
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_"
            "PACKET_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CANDIDATE_REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "candidate_packet_outcome": CANDIDATE_PACKET_OUTCOME,
        "candidate_packet_result": CANDIDATE_PACKET_RESULT,
        "selected_A_ck_option_class": SELECTED_A_CK_OPTION_CLASS,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "A_bridge_candidate_id": A_BRIDGE_CANDIDATE_ID,
        "A_bridge_candidate_type": A_BRIDGE_CANDIDATE_TYPE,
        "A_bridge_constraint_form": A_BRIDGE_CONSTRAINT_FORM,
        "A_bridge_constraint_equation": A_BRIDGE_CONSTRAINT_EQUATION,
        "A_bridge_constraint_short_form": A_BRIDGE_CONSTRAINT_SHORT_FORM,
        "A_bridge_field_equation_match": A_BRIDGE_FIELD_EQUATION_MATCH,
        "A_bridge_stress_energy_match": A_BRIDGE_STRESS_ENERGY_MATCH,
        "A_bridge_source_residual_match": A_BRIDGE_SOURCE_RESIDUAL_MATCH,
        "A_bridge_rule_plain_meaning": A_BRIDGE_RULE_PLAIN_MEANING,
        "A_bridge_route_alignment_sequence": A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
        "A_bridge_route_alignment_sequence_plain": route_sequence,
        "bridge_candidate_id": A_BRIDGE_CANDIDATE_ID,
        "bridge_candidate_type": A_BRIDGE_CANDIDATE_TYPE,
        "bridge_constraint_form": A_BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": A_BRIDGE_CONSTRAINT_EQUATION,
        "bridge_route_field_equation_match": A_BRIDGE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": A_BRIDGE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": A_BRIDGE_SOURCE_RESIDUAL_MATCH,
        "bridge_candidate_rule_plain_meaning": A_BRIDGE_RULE_PLAIN_MEANING,
        "bridge_component_count": 3,
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
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "stress_energy_under_selected_u1_policy": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "divergence_identity": DIVERGENCE_IDENTITY,
        "on_shell_vacuum_conservation_identity": ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
        "bounded_source_admissibility_result": BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
        "local_source_route_scope": LOCAL_SOURCE_ROUTE_SCOPE,
        "vacuum_supporting_identity_form": VACUUM_SUPPORTING_IDENTITY_FORM,
        "vacuum_on_shell_implication_form": VACUUM_ON_SHELL_IMPLICATION_FORM,
        "review_accepts_vacuum_u1_route_consistency_candidate": True,
        "vacuum_u1_route_consistency_candidate_accepted": True,
        "A_bridge_candidate_recorded_as_candidate_only": True,
        "A_bridge_candidate_recorded_as_admissibility_rule": True,
        "A_bridge_candidate_recorded_as_admissibility_candidate": True,
        "candidate_carried_forward_exactly": True,
        "route_consistency_tuple_carried_forward": True,
        "field_equation_match_component_preserved": True,
        "stress_energy_match_component_preserved": True,
        "source_residual_match_component_preserved": True,
        "vacuum_u1_scope_preserved": True,
        "source_admissibility_context_preserved": True,
        "A_bridge_functional_embedding_packet_authorized": True,
        "bridge_functional_embedding_packet_authorized": True,
        "functional_embedding_packet_authorized": True,
        "functional_embedding_packet_prepared": False,
        "functional_embedding_executed": False,
        "A_bridge_functional_selected": False,
        "bridge_functional_selected": False,
        "A_bridge_candidate_functional_defined": False,
        "A_bridge_candidate_functional_selected": False,
        "A_bridge_candidate_recorded_as_action_term": False,
        "A_bridge_candidate_recorded_as_new_dynamical_law": False,
        "A_bridge_candidate_rule_proved": False,
        "A_bridge_admissibility_claimed": False,
        "A_bridge_admissibility_proved": False,
        "A_bridge_route_alignment_verified": False,
        "bridge_candidate_functional_defined": False,
        "bridge_candidate_functional_selected": False,
        "bridge_candidate_recorded_as_action_term": False,
        "bridge_candidate_recorded_as_new_dynamical_law": False,
        "bridge_candidate_rule_proved": False,
        "bridge_admissibility_claimed": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "field_equation_match_proved": False,
        "stress_energy_match_proved": False,
        "source_residual_match_proved": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "ck_action_embedding_claimed": False,
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
        "review_criteria": criteria,
        "review_criteria_count": len(criteria),
        "review_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "A_BRIDGE_ADMISSIBILITY_CK_CANDIDATE_REVIEW_ACCEPTED_NO_FUNCTIONALIZATION"
        ),
        "mathematical_statement": (
            "The review accepts the ToE-native A bridge-admissibility C_k "
            "candidate packet as a vacuum U(1) route-consistency candidate "
            "only: "
            + A_BRIDGE_CONSTRAINT_FORM
            + ", with condition "
            + A_BRIDGE_CONSTRAINT_EQUATION
            + ". The E_A route match, T_A route match, and C_source^A "
            "residual match components are preserved without claiming a "
            "bridge proof, functionalization, or promotion."
        ),
        "non_claim_boundary": (
            "This review accepts the vacuum U(1) route-consistency candidate "
            "only. It does not functionalize C_bridge^A, does not embed it in "
            "S_C, does not define a C_k action term, does not select a "
            "multiplier type, does not execute C_k variation, does not vary "
            "lambda_k, A, or g, does not prove the E_A route match, does not "
            "prove the T_A route match, does not prove the C_source^A residual "
            "match, does not verify the full route alignment, does not claim "
            "full bridge admissibility, does not derive J^nu, does not derive "
            "a psi-current or external-current native route, does not derive "
            "sourced Maxwell, does not prove matter/current exchange or "
            "matter-gauge exchange, does not close EM, does not close QFT-GR, "
            "does not authorize semiclassical coupling, does not promote the "
            "master action, and does not claim empirical validation or public "
            "readiness. The bridge rule remains candidate-only until the "
            "functional-embedding packet decides or blocks action embedding."
        ),
        "critical_gate_fail_conditions": [
            "functionalize or embed C_bridge^A as an action term",
            "select a multiplier type or domain",
            "execute C_k or lambda variation",
            "execute A or metric variation of the bridge candidate",
            "claim full bridge admissibility is proved",
            "claim route alignment is verified",
            "derive J^nu",
            "derive sourced Maxwell",
            "prove matter/current exchange",
            "claim full EM closure",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation or public readiness",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_STATUS,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeABridgeAdmissibilityCKConstraintCandidatePacketResultReview",
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
            "candidate_packet_file": _ptr(candidate_packet_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_review(review: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(review, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A bridge-admissibility C_k constraint "
            "candidate packet result review."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    review = (
        build_toe_native_a_bridge_admissibility_ck_constraint_candidate_packet_result_review(
            captured_at_utc=args.captured_at_utc
        )
    )
    path = write_review(review, args.out)
    print(
        json.dumps(
            {
                "accepted": review["accepted"],
                "out": _ptr(path),
                "outcome_id": review["outcome_id"],
                "review_result": review["review_result"],
                "selected_next_target": review["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
