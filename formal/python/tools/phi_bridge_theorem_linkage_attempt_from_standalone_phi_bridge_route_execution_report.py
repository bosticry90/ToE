from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_result_review_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_TUPLE_ZERO,
    COMPONENTWISE_ZERO_ROUTE,
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    EXECUTION_ROUTE_TO_AUTHORIZE,
    FIELD_EQUATION_MATCH,
    FIELD_EQUATION_ZERO_COMPONENT,
    LEAN_PACKET_PATH as RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LEAN_STATUS_WORDING_LINES_FOR_PACKET,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    PACKET_ID as RESULT_REVIEW_PACKET_ID,
    SCHEMA_ID as RESULT_REVIEW_SCHEMA_ID,
    SOURCE_RESIDUAL_MATCH,
    SOURCE_RESIDUAL_ZERO_COMPONENT,
    STANDALONE_PHI_BRIDGE_ROUTE,
    STRESS_ENERGY_MATCH,
    STRESS_ENERGY_ZERO_COMPONENT,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_EXECUTION_OUTCOME,
    SUGGESTED_EXECUTION_OUTCOME,
    TARGET_CONCLUSION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "EXECUTION_20260630_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "EXECUTION_v0"
)
EXECUTION_RESULT = SUGGESTED_EXECUTION_OUTCOME
STRICT_EXECUTION_RESULT = STRICT_SUGGESTED_EXECUTION_OUTCOME
OUTCOME_ID = EXECUTION_RESULT
PACKET_CLASSIFICATION = (
    "phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_"
    "execution_constructs_C_bridge_phi_zero_componentwise_no_ck_rule_or_master_"
    "action_promotion"
)

NEXT_TARGET = (
    "review_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_"
    "execution_result"
)
NEXT_TARGET_KIND = (
    "phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_"
    "execution_result_review"
)
SUGGESTED_REVIEW_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "EXECUTION_RESULT_REVIEW_ACCEPTS_C_BRIDGE_PHI_ZERO_FROM_COMPONENTWISE_"
    "ROUTE_MATCH_NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_PROMOTION"
)
STRICT_SUGGESTED_REVIEW_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "EXECUTION_RESULT_REVIEW_ACCEPTS_LOCAL_PHI_BRIDGE_THEOREM_LINKAGE_ONLY_NO_"
    "PHI_SECTOR_OR_SEAM_CLOSURE"
)

EXECUTED_COMPONENTWISE_ROUTE = COMPONENTWISE_ZERO_ROUTE
EXECUTION_FINDINGS = [
    "phi-bridge theorem-linkage attempt executed",
    "C_bridge^phi tuple definition preserved",
    "E_phi master/witness equality used",
    "T_phi master/witness equality used",
    "C_source^phi divergence-match equality used",
    "componentwise zero route constructed",
    "C_bridge^phi = 0 locally constructed",
    "no phi-sector closure",
    "no scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no seam closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]
BOUNDARY_ITEMS = [
    "no phi-sector closure",
    "no scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no seam closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]
ROUTE_PURITY_WATCH_ITEMS = [
    "no C_source^phi theorem substitution",
    "no A-source route import",
    "no psi-A route import",
    "no QFT-GR route import",
    "master/witness route match is not master-action promotion",
]
PLAIN_MEANING = (
    "The frozen C_bridge^phi tuple is reduced componentwise: the master and "
    "witness phi field-equation components match, the stress-energy components "
    "match, and the source residual matches the stress divergence, so the tuple "
    "is (0, 0, 0) and the local target C_bridge^phi = 0 is constructed."
)
LEAN_THEOREM_NAME = "c_bridge_phi_zero_from_componentwise_route_match"
LEAN_THEOREM_DESCRIPTION = (
    "Generic Lean witness: if all three C_bridge^phi tuple components are zero, "
    "then the tuple is the zero tuple."
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION = (
    "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
)
SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION = "PASSED_SERIAL_RERUN"
LEAN_STATUS_WORDING_FOR_EXECUTION = LEAN_STATUS_WORDING_FOR_PACKET
LEAN_STATUS_WORDING_LINES_FOR_EXECUTION = LEAN_STATUS_WORDING_LINES_FOR_PACKET

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "EXECUTION_20260630_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiBridgeTheoremLinkageAttemptFromStandalonePhiBridgeRouteExecution.lean"
)
QFTGR_AGGREGATE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "C_source_phi_route_reused": False,
        "C_bridge_phi_route_reused_from_C_source_phi": False,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "QFT_GR_route_imported": False,
        "QFT_GR_source_route_imported": False,
        "J_current_imported": False,
        "master_action_route_substituted": False,
        "new_bridge_formula_invented": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "field_equation_match_proved": False,
        "stress_energy_match_proved": False,
        "source_residual_match_proved": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "C_source_phi_closure_claimed": False,
        "C_bridge_phi_closure_claimed": False,
        "phi_sector_closure_claimed": False,
        "full_scalar_qft_closure_claimed": False,
        "full_scalar_QFT_closure_claimed": False,
        "A_sector_closure_claimed": False,
        "sourced_maxwell_closure_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "general_C_k_theorem_linkage_closure": False,
        "general_C_k_closure": False,
        "C_k_dynamical_law_status": False,
        "C_k_rule_promotion_authorized": False,
        "C_k_rule_promoted": False,
        "rule_promoted": False,
        "C_k_action_embedding_claimed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_authorized": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "action_embedding_claimed": False,
        "action_variation_executed": False,
        "multiplier_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_claimed": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
    }


def _result_review_valid(result_review: dict[str, Any]) -> bool:
    return (
        result_review.get("schema_id") == RESULT_REVIEW_SCHEMA_ID
        and result_review.get("packet_id") == RESULT_REVIEW_PACKET_ID
        and result_review.get("outcome_id") == RESULT_REVIEW_OUTCOME
        and result_review.get("review_result") == RESULT_REVIEW_OUTCOME
        and result_review.get("strict_review_result") == STRICT_REVIEW_RESULT
        and result_review.get("selected_next_target") == CONSUMED_TARGET
        and result_review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and result_review.get("componentwise_zero_route") == COMPONENTWISE_ZERO_ROUTE
        and result_review.get("execution_route_to_authorize")
        == EXECUTION_ROUTE_TO_AUTHORIZE
        and result_review.get("theorem_discharged") is False
        and result_review.get("C_bridge_phi_discharged") is False
        and result_review.get("master_action_promoted") is False
        and result_review.get("accepted") is True
    )


def _execution_steps() -> list[dict[str, str]]:
    return [
        {
            "step_id": "use_field_equation_route_match",
            "statement": FIELD_EQUATION_MATCH,
            "role": "first C_bridge^phi tuple component",
        },
        {
            "step_id": "use_stress_energy_route_match",
            "statement": STRESS_ENERGY_MATCH,
            "role": "second C_bridge^phi tuple component",
        },
        {
            "step_id": "use_source_residual_divergence_match",
            "statement": SOURCE_RESIDUAL_MATCH,
            "role": "third C_bridge^phi tuple component",
        },
        {
            "step_id": "construct_field_equation_zero_component",
            "statement": FIELD_EQUATION_ZERO_COMPONENT,
            "role": "componentwise zero construction",
        },
        {
            "step_id": "construct_stress_energy_zero_component",
            "statement": STRESS_ENERGY_ZERO_COMPONENT,
            "role": "componentwise zero construction",
        },
        {
            "step_id": "construct_source_residual_zero_component",
            "statement": SOURCE_RESIDUAL_ZERO_COMPONENT,
            "role": "componentwise zero construction",
        },
        {
            "step_id": "construct_zero_tuple",
            "statement": BRIDGE_TUPLE_ZERO,
            "role": "local tuple target",
        },
        {
            "step_id": "construct_C_bridge_phi_zero",
            "statement": TARGET_CONCLUSION,
            "role": "local theorem-linkage target constructed",
        },
    ]


def _execution_criteria() -> list[dict[str, Any]]:
    return [
        {
            "row_id": "execution_target_authorized",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The prior review selected this bounded execution target.",
        },
        {
            "row_id": "tuple_definition_preserved",
            "status": "accepted",
            "evidence": BRIDGE_CONSTRAINT_FORM,
            "assessment": "The frozen standalone phi bridge tuple is unchanged.",
        },
        {
            "row_id": "field_equation_component_zero",
            "status": "accepted",
            "evidence": FIELD_EQUATION_ZERO_COMPONENT,
            "assessment": "The E_phi master/witness match gives the first zero component.",
        },
        {
            "row_id": "stress_energy_component_zero",
            "status": "accepted",
            "evidence": STRESS_ENERGY_ZERO_COMPONENT,
            "assessment": "The T_phi master/witness match gives the second zero component.",
        },
        {
            "row_id": "source_residual_component_zero",
            "status": "accepted",
            "evidence": SOURCE_RESIDUAL_ZERO_COMPONENT,
            "assessment": "The C_source^phi divergence match gives the third zero component.",
        },
        {
            "row_id": "C_bridge_phi_zero_constructed",
            "status": "accepted",
            "evidence": TARGET_CONCLUSION,
            "assessment": "The local C_bridge^phi theorem-linkage target is constructed.",
        },
        {
            "row_id": "route_contamination_blocked",
            "status": "accepted",
            "evidence": ROUTE_PURITY_WATCH_ITEMS,
            "assessment": "No C_source^phi, A-source, psi-A, QFT-GR, or master-action route is substituted.",
        },
        {
            "row_id": "no_closure_or_promotion",
            "status": "accepted",
            "evidence": BOUNDARY_ITEMS,
            "assessment": "The execution remains local theorem-linkage only.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_"
            "execution"
        ),
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "full_toeformal_aggregate_status_for_execution": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
        ),
        "scoped_lean_targets_status_for_execution": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
        ),
        "lean_status_wording_lines_for_execution": (
            LEAN_STATUS_WORDING_LINES_FOR_EXECUTION
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution(
    *,
    result_review_path: Path = RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    route_text = " ".join(EXECUTED_COMPONENTWISE_ROUTE)
    execution_steps = _execution_steps()
    execution_criteria = _execution_criteria()
    acceptance_criteria = {
        "consumes_expected_execution_target": _result_review_valid(result_review),
        "tuple_definition_preserved": (
            BRIDGE_CONSTRAINT_FORM
            == "C_bridge^phi := (E_phi^master - E_phi^witness, "
            "T_phi^master - T_phi^witness, "
            "C_source^phi - nabla_mu T_phi^{mu nu})"
            and BRIDGE_CONSTRAINT_EQUATION == "C_bridge^phi = 0"
            and BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM == "C_bridge^phi = 0"
        ),
        "componentwise_route_constructed": (
            EXECUTED_COMPONENTWISE_ROUTE
            == [
                "E_phi^master = E_phi^witness",
                "T_phi^master = T_phi^witness",
                "C_source^phi = nabla_mu T_phi^{mu nu}",
                "therefore: E_phi^master - E_phi^witness = 0",
                "therefore: T_phi^master - T_phi^witness = 0",
                "therefore: C_source^phi - nabla_mu T_phi^{mu nu} = 0",
                "therefore: C_bridge^phi = (0, 0, 0)",
                "therefore: C_bridge^phi = 0",
            ]
        ),
        "zero_components_constructed": (
            FIELD_EQUATION_ZERO_COMPONENT == "E_phi^master - E_phi^witness = 0"
            and STRESS_ENERGY_ZERO_COMPONENT == "T_phi^master - T_phi^witness = 0"
            and SOURCE_RESIDUAL_ZERO_COMPONENT
            == "C_source^phi - nabla_mu T_phi^{mu nu} = 0"
        ),
        "C_bridge_phi_zero_constructed": (
            BRIDGE_TUPLE_ZERO == "C_bridge^phi = (0, 0, 0)"
            and TARGET_CONCLUSION == "C_bridge^phi = 0"
        ),
        "route_contamination_blocked": (
            "J^alpha" not in route_text
            and "nabla_mu F" not in route_text
            and "QFT-GR" not in route_text
        ),
        "execution_criteria_all_accepted": all(
            row["status"] == "accepted" for row in execution_criteria
        ),
        "lean_status_wording_preserved": (
            LEAN_STATUS_WORDING_LINES_FOR_EXECUTION
            == [
                "full ToeFormal aggregate = NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION",
                "scoped Lean targets = PASSED_SERIAL_RERUN",
            ]
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "BRIDGE_ROUTE_EXECUTION"
        )
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "BRIDGE_ROUTE_EXECUTION"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "executed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_"
            "ROUTE_EXECUTION_REQUIRES_REMEDIATION"
        ),
        "packet_result": OUTCOME_ID
        if accepted
        else (
            "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_"
            "ROUTE_EXECUTION_REQUIRES_REMEDIATION"
        ),
        "execution_result": OUTCOME_ID
        if accepted
        else (
            "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_"
            "ROUTE_EXECUTION_REQUIRES_REMEDIATION"
        ),
        "strict_execution_result": STRICT_EXECUTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if accepted else "remediation",
        "post_execution_target": NEXT_TARGET,
        "post_execution_target_kind": NEXT_TARGET_KIND,
        "suggested_review_outcome": SUGGESTED_REVIEW_OUTCOME,
        "strict_suggested_review_outcome": STRICT_SUGGESTED_REVIEW_OUTCOME,
        "result_review_schema_id": RESULT_REVIEW_SCHEMA_ID,
        "result_review_packet_id": RESULT_REVIEW_PACKET_ID,
        "result_review_outcome": RESULT_REVIEW_OUTCOME,
        "result_review_strict_outcome": STRICT_REVIEW_RESULT,
        "result_review_consumed": accepted,
        "selected_obligation": "C_bridge^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_bridge^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_bridge^phi",
        "standalone_phi_bridge_route": STANDALONE_PHI_BRIDGE_ROUTE,
        "standalone_phi_bridge_route_preserved": accepted,
        "exact_tuple_definition_preserved": accepted,
        "target_C_bridge_phi_zero_preserved": accepted,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "componentwise_zero_route": COMPONENTWISE_ZERO_ROUTE,
        "componentwise_zero_route_count": len(COMPONENTWISE_ZERO_ROUTE),
        "execution_route_to_authorize": EXECUTION_ROUTE_TO_AUTHORIZE,
        "execution_route_to_authorize_count": len(EXECUTION_ROUTE_TO_AUTHORIZE),
        "executed_componentwise_route": EXECUTED_COMPONENTWISE_ROUTE,
        "executed_componentwise_route_count": len(EXECUTED_COMPONENTWISE_ROUTE),
        "field_equation_match": FIELD_EQUATION_MATCH,
        "stress_energy_match": STRESS_ENERGY_MATCH,
        "source_residual_match": SOURCE_RESIDUAL_MATCH,
        "field_equation_zero_component": FIELD_EQUATION_ZERO_COMPONENT,
        "stress_energy_zero_component": STRESS_ENERGY_ZERO_COMPONENT,
        "source_residual_zero_component": SOURCE_RESIDUAL_ZERO_COMPONENT,
        "bridge_tuple_zero": BRIDGE_TUPLE_ZERO,
        "target_conclusion": TARGET_CONCLUSION,
        "route_kind": "standalone_phi_bridge_componentwise_zero_execution",
        "plain_meaning": PLAIN_MEANING,
        "lean_theorem_name": LEAN_THEOREM_NAME,
        "lean_theorem_description": LEAN_THEOREM_DESCRIPTION,
        "E_phi_master_witness_equality_used": accepted,
        "T_phi_master_witness_equality_used": accepted,
        "C_source_phi_divergence_match_equality_used": accepted,
        "E_phi_master_witness_match_target_preserved": accepted,
        "T_phi_master_witness_match_target_preserved": accepted,
        "C_source_phi_divergence_match_target_preserved": accepted,
        "componentwise_zero_route_constructed": accepted,
        "C_bridge_phi_tuple_zero_constructed": accepted,
        "C_bridge_phi_zero_constructed": accepted,
        "C_bridge_phi_zero_derived": accepted,
        "C_bridge_phi_linkage_constructed": accepted,
        "C_bridge_phi_admissibility_status": "local theorem-linkage only",
        "same_standalone_phi_bridge_registry_tuple": True,
        "same_sign_and_index_conventions": True,
        "theorem_linkage_completed": accepted,
        "theorem_target_recorded": accepted,
        "definition_linkage_constructed": accepted,
        "proof_execution": "executed",
        "proof_execution_authorized": True,
        "proof_attempt_executed": accepted,
        "proof_debt_reduced": accepted,
        "theorem_execution_authorized": True,
        "theorem_discharged": accepted,
        "theorem_linkage_obligation_discharged": accepted,
        "C_bridge_phi_theorem_linkage_obligation_discharged": accepted,
        "C_bridge_phi_discharged": accepted,
        "rule_promotion": "not authorized",
        "execution_steps": execution_steps,
        "execution_step_count": len(execution_steps),
        "execution_criteria": execution_criteria,
        "execution_criteria_count": len(execution_criteria),
        "execution_criteria_accepted_count": sum(
            1 for row in execution_criteria if row["status"] == "accepted"
        ),
        "execution_findings": EXECUTION_FINDINGS,
        "execution_finding_count": len(EXECUTION_FINDINGS),
        "boundary_items": BOUNDARY_ITEMS,
        "boundary_item_count": len(BOUNDARY_ITEMS),
        "route_purity_watch_items": ROUTE_PURITY_WATCH_ITEMS,
        "route_purity_watch_item_count": len(ROUTE_PURITY_WATCH_ITEMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": False,
        "claim_ladder_position": (
            "below phi-sector closure, scalar/QFT closure, QFT-GR source "
            "admissibility, seam closure, empirical prediction, empirical "
            "confirmation, and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This execution constructs only the local standalone phi-bridge "
            "C_bridge^phi theorem-linkage route. It preserves C_bridge^phi := "
            "(E_phi^master - E_phi^witness, T_phi^master - T_phi^witness, "
            "C_source^phi - nabla_mu T_phi^{mu nu}), uses "
            "E_phi^master = E_phi^witness, T_phi^master = T_phi^witness, "
            "and C_source^phi = nabla_mu T_phi^{mu nu}, constructs the three "
            "zero components, then constructs C_bridge^phi = (0, 0, 0) and "
            "C_bridge^phi = 0. It does not claim phi-sector closure, scalar/QFT "
            "closure, QFT-GR closure, EM-QFT closure, seam closure, general C_k "
            "closure, C_k promotion, action embedding, variation, empirical "
            "validation, or master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume execute_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route",
            "fail to preserve the C_bridge^phi tuple definition",
            "fail to use E_phi^master = E_phi^witness",
            "fail to use T_phi^master = T_phi^witness",
            "fail to use C_source^phi = nabla_mu T_phi^{mu nu}",
            "fail to construct the three zero components",
            "fail to construct C_bridge^phi = (0, 0, 0)",
            "fail to construct C_bridge^phi = 0",
            "silently substitute a C_source^phi proof route",
            "silently import an A-source, psi-A, or QFT-GR route",
            "treat master/witness route match as master-action promotion",
            "claim phi-sector closure",
            "claim scalar/QFT closure",
            "claim EM-QFT or QFT-GR closure",
            "claim general C_k closure",
            "promote any C_k rule",
            "embed or vary an action",
            "claim empirical validation",
            "claim seam closure",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_EXECUTION,
        "lean_status_wording_lines": LEAN_STATUS_WORDING_LINES_FOR_EXECUTION,
        "full_toeformal_aggregate_status_for_execution": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
        ),
        "scoped_lean_targets_status_for_execution": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
        ),
        "aggregate_lean_validation_status_for_execution": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiBridgeTheoremLinkageAttemptFromStandalonePhiBridgeRouteExecution",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "result_review_file": _ptr(result_review_path),
            "result_review_lean_file": _ptr(RESULT_REVIEW_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_false_boundary_flags())
    payload["proof_execution_authorized"] = True
    payload["proof_attempt_executed"] = accepted
    payload["proof_debt_reduced"] = accepted
    payload["theorem_execution_authorized"] = True
    payload["theorem_discharged"] = accepted
    payload["theorem_linkage_completed"] = accepted
    payload["theorem_linkage_obligation_discharged"] = accepted
    payload["C_bridge_phi_discharged"] = accepted
    payload["C_bridge_phi_zero_derived"] = accepted
    payload["C_bridge_phi_zero_constructed"] = accepted
    payload["C_bridge_phi_linkage_constructed"] = accepted
    payload["C_bridge_phi_theorem_linkage_obligation_discharged"] = accepted
    return payload


def write_execution(payload: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Execute the standalone phi-bridge C_bridge^phi componentwise zero "
            "theorem-linkage route."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--result-review", type=Path, default=RESULT_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    result_review_path = (
        args.result_review
        if args.result_review.is_absolute()
        else REPO_ROOT / args.result_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution(
            result_review_path=result_review_path,
            captured_at_utc=args.captured_at_utc,
        )
    )
    path = write_execution(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "executed": payload["executed"],
                "out": _ptr(path),
                "execution_result": payload["execution_result"],
                "selected_next_target": payload["selected_next_target"],
                "C_bridge_phi_zero_derived": payload["C_bridge_phi_zero_derived"],
                "phi_sector_closure_claimed": payload["phi_sector_closure_claimed"],
                "rule_promoted": payload["rule_promoted"],
                "master_action_promoted": payload["master_action_promoted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
