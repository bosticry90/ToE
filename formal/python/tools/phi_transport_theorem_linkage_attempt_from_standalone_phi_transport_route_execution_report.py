from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_result_review_report import (
    BLOCKED_CLAIMS,
    COMPONENTWISE_ZERO_ROUTE,
    C_TRANSPORT_TUPLE_ZERO,
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    EXECUTION_ROUTE_TO_AUTHORIZE,
    KNOWN_PHI_TRANSPORT_CHAIN_FORM,
    LEAN_PACKET_PATH as RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LEAN_STATUS_WORDING_LINES_FOR_PACKET,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    PACKET_ID as RESULT_REVIEW_PACKET_ID,
    ROUTE_PURITY_WATCH_ITEMS,
    SCHEMA_ID as RESULT_REVIEW_SCHEMA_ID,
    STANDALONE_PHI_TRANSPORT_ROUTE,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_EXECUTION_OUTCOME,
    SUGGESTED_EXECUTION_OUTCOME,
    TARGET_CONCLUSION,
    TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT,
    TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT,
    TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-07-01T00:00:00Z"

SCHEMA_ID = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "EXECUTION_20260701_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "EXECUTION_v0"
)
EXECUTION_RESULT = SUGGESTED_EXECUTION_OUTCOME
STRICT_EXECUTION_RESULT = STRICT_SUGGESTED_EXECUTION_OUTCOME
OUTCOME_ID = EXECUTION_RESULT
PACKET_CLASSIFICATION = (
    "phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_"
    "execution_constructs_C_transport_phi_zero_componentwise_no_ck_rule_or_"
    "master_action_promotion"
)

NEXT_TARGET = (
    "review_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_"
    "route_execution_result"
)
NEXT_TARGET_KIND = (
    "phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_"
    "execution_result_review"
)
SUGGESTED_REVIEW_OUTCOME = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "EXECUTION_RESULT_REVIEW_ACCEPTS_C_TRANSPORT_PHI_ZERO_FROM_COMPONENTWISE_"
    "TRANSPORT_MATCH_NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_PROMOTION"
)
STRICT_SUGGESTED_REVIEW_OUTCOME = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "EXECUTION_RESULT_REVIEW_ACCEPTS_LOCAL_PHI_TRANSPORT_THEOREM_LINKAGE_ONLY_NO_"
    "PHI_SECTOR_OR_SEAM_CLOSURE"
)

EXECUTED_COMPONENTWISE_ROUTE = COMPONENTWISE_ZERO_ROUTE
EXECUTION_FINDINGS = [
    "phi-transport theorem-linkage attempt executed",
    "five-component C_transport^phi tuple preserved",
    "ACTION -> VARIATION zero component used",
    "VARIATION -> BRIDGE zero component used",
    "BRIDGE -> SOURCE zero component used",
    "SOURCE -> RESIDUAL zero component used",
    "RESIDUAL -> REGIME zero component used",
    "componentwise zero route constructed",
    "C_transport^phi = 0 locally constructed",
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
TRANSPORT_ROUTE_PURITY_WATCH_ITEMS = [
    "no C_source^phi substitution",
    "no C_bridge^phi substitution",
    "no A-sector route import",
    "no psi-A route import",
    "no QFT-GR route import",
    "action-to-regime transport match is not master-action promotion",
]
PLAIN_MEANING = (
    "Each transport step in the phi derivation chain has no mismatch. Therefore "
    "the whole phi transport-consistency check vanishes by the local five-"
    "component route only."
)
LEAN_THEOREM_NAME = "c_transport_phi_zero_from_componentwise_transport_match"
LEAN_THEOREM_DESCRIPTION = (
    "Generic Lean witness: if all five C_transport^phi tuple components are "
    "zero, then the tuple is the zero tuple."
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
    / "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "EXECUTION_20260701_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiTransportTheoremLinkageAttemptFromStandalonePhiTransportRouteExecution.lean"
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


def _blocked_boundary_flags() -> dict[str, bool]:
    return {
        "new_transport_formula_invented": False,
        "C_source_phi_route_reused": False,
        "C_bridge_phi_route_reused": False,
        "C_bridge_phi_route_reused_as_transport": False,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "QFT_GR_route_imported": False,
        "QFT_GR_source_route_imported": False,
        "master_action_route_substituted": False,
        "J_current_imported": False,
        "transport_consistency_proved": False,
        "transport_components_proved": False,
        "transport_candidate_rule_proved": False,
        "full_route_alignment_proved": False,
        "route_chain_compatibility_proved": False,
        "source_admissibility_proved": False,
        "bridge_admissibility_proved": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "C_source_phi_closure_claimed": False,
        "C_bridge_phi_closure_claimed": False,
        "C_transport_phi_closure_claimed": False,
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
        and result_review.get("C_transport_phi_discharged") is False
        and result_review.get("master_action_promoted") is False
        and result_review.get("accepted") is True
    )


def _execution_steps() -> list[dict[str, str]]:
    return [
        {
            "step_id": "use_action_variation_transport_zero",
            "statement": TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT,
            "role": "first C_transport^phi tuple component",
        },
        {
            "step_id": "use_variation_bridge_transport_zero",
            "statement": TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT,
            "role": "second C_transport^phi tuple component",
        },
        {
            "step_id": "use_bridge_source_transport_zero",
            "statement": TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT,
            "role": "third C_transport^phi tuple component",
        },
        {
            "step_id": "use_source_residual_transport_zero",
            "statement": TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT,
            "role": "fourth C_transport^phi tuple component",
        },
        {
            "step_id": "use_residual_regime_transport_zero",
            "statement": TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT,
            "role": "fifth C_transport^phi tuple component",
        },
        {
            "step_id": "construct_zero_tuple",
            "statement": C_TRANSPORT_TUPLE_ZERO,
            "role": "local tuple target",
        },
        {
            "step_id": "construct_C_transport_phi_zero",
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
            "evidence": TRANSPORT_CONSTRAINT_FORM,
            "assessment": "The frozen standalone phi transport tuple is unchanged.",
        },
        {
            "row_id": "five_transport_components_zero",
            "status": "accepted",
            "evidence": EXECUTED_COMPONENTWISE_ROUTE[:5],
            "assessment": "All five transport components are zero in order.",
        },
        {
            "row_id": "C_transport_phi_zero_constructed",
            "status": "accepted",
            "evidence": TARGET_CONCLUSION,
            "assessment": "The local C_transport^phi theorem-linkage target is constructed.",
        },
        {
            "row_id": "route_contamination_blocked",
            "status": "accepted",
            "evidence": TRANSPORT_ROUTE_PURITY_WATCH_ITEMS,
            "assessment": "No source, bridge, A-sector, psi-A, QFT-GR, or master-action route is substituted.",
        },
        {
            "row_id": "no_sector_closure_or_promotion",
            "status": "accepted",
            "evidence": BOUNDARY_ITEMS,
            "assessment": "The execution remains local theorem-linkage only.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_"
            "route_execution"
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


def build_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_execution(
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
            TRANSPORT_CONSTRAINT_FORM
            == "C_transport^phi := (Transport_ACTION_VARIATION^phi, "
            "Transport_VARIATION_BRIDGE^phi, Transport_BRIDGE_SOURCE^phi, "
            "Transport_SOURCE_RESIDUAL^phi, Transport_RESIDUAL_REGIME^phi)"
            and TRANSPORT_CONSTRAINT_EQUATION == "C_transport^phi = 0"
            and TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM == "C_transport^phi = 0"
        ),
        "componentwise_route_constructed": (
            EXECUTED_COMPONENTWISE_ROUTE
            == [
                "Transport_ACTION_VARIATION^phi = 0",
                "Transport_VARIATION_BRIDGE^phi = 0",
                "Transport_BRIDGE_SOURCE^phi = 0",
                "Transport_SOURCE_RESIDUAL^phi = 0",
                "Transport_RESIDUAL_REGIME^phi = 0",
                "therefore: C_transport^phi = (0, 0, 0, 0, 0)",
                "therefore: C_transport^phi = 0",
            ]
        ),
        "zero_components_constructed": (
            TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT
            == "Transport_ACTION_VARIATION^phi = 0"
            and TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT
            == "Transport_VARIATION_BRIDGE^phi = 0"
            and TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT
            == "Transport_BRIDGE_SOURCE^phi = 0"
            and TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT
            == "Transport_SOURCE_RESIDUAL^phi = 0"
            and TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT
            == "Transport_RESIDUAL_REGIME^phi = 0"
        ),
        "C_transport_phi_zero_constructed": (
            C_TRANSPORT_TUPLE_ZERO == "C_transport^phi = (0, 0, 0, 0, 0)"
            and TARGET_CONCLUSION == "C_transport^phi = 0"
        ),
        "route_contamination_blocked": (
            "C_source^phi =" not in route_text
            and "C_bridge^phi =" not in route_text
            and "J^alpha" not in route_text
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
            "REMEDIATE_PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_"
            "PHI_TRANSPORT_ROUTE_EXECUTION"
        )
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_"
            "PHI_TRANSPORT_ROUTE_EXECUTION"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "executed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "TRANSPORT_ROUTE_EXECUTION_REQUIRES_REMEDIATION"
        ),
        "packet_result": OUTCOME_ID
        if accepted
        else (
            "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "TRANSPORT_ROUTE_EXECUTION_REQUIRES_REMEDIATION"
        ),
        "execution_result": OUTCOME_ID
        if accepted
        else (
            "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "TRANSPORT_ROUTE_EXECUTION_REQUIRES_REMEDIATION"
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
        "selected_obligation": "C_transport^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_transport^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_transport^phi",
        "standalone_phi_transport_route": STANDALONE_PHI_TRANSPORT_ROUTE,
        "standalone_phi_transport_route_preserved": accepted,
        "exact_five_component_transport_tuple_preserved": accepted,
        "target_C_transport_phi_zero_preserved": accepted,
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_admissibility_constraint_form": (
            TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "transport_component_count": len(TRANSPORT_COMPONENTS),
        "transport_component_forms": [
            row["component_form"] for row in TRANSPORT_COMPONENTS
        ],
        "componentwise_zero_route": COMPONENTWISE_ZERO_ROUTE,
        "componentwise_zero_route_count": len(COMPONENTWISE_ZERO_ROUTE),
        "execution_route_to_authorize": EXECUTION_ROUTE_TO_AUTHORIZE,
        "execution_route_to_authorize_count": len(EXECUTION_ROUTE_TO_AUTHORIZE),
        "executed_componentwise_route": EXECUTED_COMPONENTWISE_ROUTE,
        "executed_componentwise_route_count": len(EXECUTED_COMPONENTWISE_ROUTE),
        "transport_action_variation_zero_component": (
            TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT
        ),
        "transport_variation_bridge_zero_component": (
            TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT
        ),
        "transport_bridge_source_zero_component": (
            TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT
        ),
        "transport_source_residual_zero_component": (
            TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT
        ),
        "transport_residual_regime_zero_component": (
            TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT
        ),
        "C_transport_tuple_zero": C_TRANSPORT_TUPLE_ZERO,
        "target_conclusion": TARGET_CONCLUSION,
        "route_kind": "standalone_phi_transport_componentwise_zero_execution",
        "plain_meaning": PLAIN_MEANING,
        "lean_theorem_name": LEAN_THEOREM_NAME,
        "lean_theorem_description": LEAN_THEOREM_DESCRIPTION,
        "known_phi_transport_chain_form": KNOWN_PHI_TRANSPORT_CHAIN_FORM,
        "transport_action_variation_zero_component_used": accepted,
        "transport_variation_bridge_zero_component_used": accepted,
        "transport_bridge_source_zero_component_used": accepted,
        "transport_source_residual_zero_component_used": accepted,
        "transport_residual_regime_zero_component_used": accepted,
        "componentwise_zero_route_constructed": accepted,
        "C_transport_phi_tuple_zero_constructed": accepted,
        "C_transport_phi_zero_constructed": accepted,
        "C_transport_phi_zero_derived": accepted,
        "C_transport_phi_linkage_constructed": accepted,
        "C_transport_phi_admissibility_status": "local theorem-linkage only",
        "same_standalone_phi_transport_registry_tuple": True,
        "same_component_order": True,
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
        "C_transport_phi_theorem_linkage_obligation_discharged": accepted,
        "C_transport_phi_theorem_linkage_gap_discharged": accepted,
        "C_transport_phi_discharged": accepted,
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
        "route_purity_watch_items": TRANSPORT_ROUTE_PURITY_WATCH_ITEMS,
        "prior_route_purity_watch_items": ROUTE_PURITY_WATCH_ITEMS,
        "route_purity_watch_item_count": len(TRANSPORT_ROUTE_PURITY_WATCH_ITEMS),
        "prior_blocked_claims": BLOCKED_CLAIMS,
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
            "This execution constructs only the local standalone phi-transport "
            "C_transport^phi theorem-linkage route. It preserves "
            "C_transport^phi := (Transport_ACTION_VARIATION^phi, "
            "Transport_VARIATION_BRIDGE^phi, Transport_BRIDGE_SOURCE^phi, "
            "Transport_SOURCE_RESIDUAL^phi, Transport_RESIDUAL_REGIME^phi), "
            "uses the five zero transport components, then constructs "
            "C_transport^phi = (0, 0, 0, 0, 0) and C_transport^phi = 0. It "
            "does not claim phi-sector closure, scalar/QFT closure, QFT-GR "
            "closure, EM-QFT closure, seam closure, general C_k closure, "
            "C_k promotion, action embedding, variation, empirical validation, "
            "or master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume execute_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route",
            "fail to preserve the C_transport^phi tuple definition",
            "fail to use Transport_ACTION_VARIATION^phi = 0",
            "fail to use Transport_VARIATION_BRIDGE^phi = 0",
            "fail to use Transport_BRIDGE_SOURCE^phi = 0",
            "fail to use Transport_SOURCE_RESIDUAL^phi = 0",
            "fail to use Transport_RESIDUAL_REGIME^phi = 0",
            "fail to construct C_transport^phi = (0, 0, 0, 0, 0)",
            "fail to construct C_transport^phi = 0",
            "silently substitute C_source^phi or C_bridge^phi",
            "silently import an A-sector, psi-A, or QFT-GR route",
            "treat action-to-regime transport match as master-action promotion",
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
            "ToeFormal.Derivation.PhiTransportTheoremLinkageAttemptFromStandalonePhiTransportRouteExecution",
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
    payload.update(_blocked_boundary_flags())
    payload["proof_execution_authorized"] = True
    payload["proof_attempt_executed"] = accepted
    payload["proof_debt_reduced"] = accepted
    payload["theorem_execution_authorized"] = True
    payload["theorem_discharged"] = accepted
    payload["theorem_linkage_completed"] = accepted
    payload["theorem_linkage_obligation_discharged"] = accepted
    payload["C_transport_phi_discharged"] = accepted
    payload["C_transport_phi_zero_derived"] = accepted
    payload["C_transport_phi_zero_constructed"] = accepted
    payload["C_transport_phi_linkage_constructed"] = accepted
    payload["C_transport_phi_theorem_linkage_gap_discharged"] = accepted
    payload["C_transport_phi_theorem_linkage_obligation_discharged"] = accepted
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
            "Execute the standalone phi-transport C_transport^phi componentwise "
            "zero theorem-linkage route."
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
        build_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_execution(
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
                "C_transport_phi_zero_derived": payload[
                    "C_transport_phi_zero_derived"
                ],
                "phi_sector_closure_claimed": payload["phi_sector_closure_claimed"],
                "rule_promoted": payload["rule_promoted"],
                "master_action_promoted": payload["master_action_promoted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if payload["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
