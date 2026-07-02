from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_transport_theorem_linkage_obligation_packet_result_review_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_RULE_CLOSEOUT_OUTCOME,
    COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN,
    DEFAULT_OUT as REVIEW_PATH,
    EXACT_PRIOR_TRANSPORT_ADMISSIBILITY_TARGET,
    EXACT_PRIOR_TRANSPORT_STATEMENT,
    EXACT_PRIOR_TRANSPORT_TARGET,
    KNOWN_PHI_TRANSPORT_CHAIN_FORM,
    LEAN_PACKET_PATH as REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LEAN_STATUS_WORDING_LINES_FOR_PACKET,
    LIKELY_COMPONENTWISE_ATTEMPT_ROUTE,
    LIKELY_PLAIN_MEANING,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as REVIEW_OUTCOME,
    PACKET_ID as REVIEW_PACKET_ID,
    SCHEMA_ID as REVIEW_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    STANDALONE_PHI_TRANSPORT_ROUTE,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_ATTEMPT_PREPARATION_OUTCOME,
    SUGGESTED_ATTEMPT_PREPARATION_OUTCOME,
    TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
    TRANSPORT_CLOSEOUT_RULE_ROLE,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_CLASSIFICATION,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-07-01T00:00:00Z"

SCHEMA_ID = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "20260701_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_v0"
OUTCOME_ID = SUGGESTED_ATTEMPT_PREPARATION_OUTCOME
STRICT_ATTEMPT_PREPARATION_RESULT = STRICT_SUGGESTED_ATTEMPT_PREPARATION_OUTCOME
PACKET_CLASSIFICATION = (
    "phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_"
    "prepares_componentwise_transport_zero_route_no_theorem_discharge"
)

NEXT_TARGET = (
    "review_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_"
    "route_result"
)
NEXT_TARGET_KIND = (
    "phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_"
    "result_review"
)
SUGGESTED_REVIEW_OUTCOME = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "RESULT_REVIEW_ACCEPTS_COMPONENTWISE_TRANSPORT_ZERO_ROUTE_PREPARATION_NO_"
    "THEOREM_DISCHARGE_OR_CK_RULE_PROMOTION"
)
STRICT_SUGGESTED_REVIEW_OUTCOME = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "RESULT_REVIEW_ACCEPTS_ACTION_TO_REGIME_TRANSPORT_MATCH_TARGET_PREPARED_NO_"
    "ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)

TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT = "Transport_ACTION_VARIATION^phi = 0"
TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT = "Transport_VARIATION_BRIDGE^phi = 0"
TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT = "Transport_BRIDGE_SOURCE^phi = 0"
TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT = "Transport_SOURCE_RESIDUAL^phi = 0"
TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT = "Transport_RESIDUAL_REGIME^phi = 0"
C_TRANSPORT_TUPLE_ZERO = "C_transport^phi = (0, 0, 0, 0, 0)"
TARGET_CONCLUSION = "C_transport^phi = 0"

COMPONENTWISE_ZERO_ROUTE = [
    TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT,
    TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT,
    TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT,
    TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT,
    TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT,
    "therefore: C_transport^phi = (0, 0, 0, 0, 0)",
    "therefore: C_transport^phi = 0",
]
PREPARED_LINKAGE_TARGET = (
    "C_transport^phi = 0 from the frozen standalone phi transport tuple by "
    "preparing the five zero transport components from ACTION to REGIME."
)
PLAIN_MEANING = (
    "Each transport step in the phi derivation chain has no mismatch. "
    "Therefore the whole phi transport-consistency check vanishes."
)

PREPARATION_CLAIMS = [
    "phi-transport theorem-linkage attempt prepared",
    "five-component transport route preserved",
    "ACTION -> VARIATION component indexed",
    "VARIATION -> BRIDGE component indexed",
    "BRIDGE -> SOURCE component indexed",
    "SOURCE -> RESIDUAL component indexed",
    "RESIDUAL -> REGIME component indexed",
    "componentwise zero target prepared",
    "no proof execution",
    "no theorem discharge",
]

WATCH_ITEMS = [
    "same standalone phi transport registry tuple",
    "same ACTION -> VARIATION component",
    "same VARIATION -> BRIDGE component",
    "same BRIDGE -> SOURCE component",
    "same SOURCE -> RESIDUAL component",
    "same RESIDUAL -> REGIME component",
    "same component order",
    "same C_transport^phi = 0 target",
    "no C_source^phi substitution",
    "no C_bridge^phi substitution",
    "no A-sector route import",
    "no psi-A route import",
    "no QFT-GR route import",
    "no master-action promotion from transport match",
]

BOUNDARY_ITEMS = [
    "no proof execution during preparation",
    "no theorem discharge",
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

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "20260701_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiTransportTheoremLinkageAttemptFromStandalonePhiTransportRoute.lean"
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
        "preparation_executes_proof": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_execution_authorized": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "C_transport_phi_discharged": False,
        "C_transport_phi_zero_derived": False,
        "C_transport_phi_theorem_linkage_gap_discharged": False,
        "C_transport_phi_theorem_linkage_obligation_discharged": False,
        "C_transport_phi_proof_executed": False,
        "C_transport_phi_closure_claimed": False,
        "transport_consistency_proved": False,
        "transport_components_proved": False,
        "transport_candidate_rule_proved": False,
        "full_route_alignment_proved": False,
        "route_chain_compatibility_proved": False,
        "source_admissibility_proved": False,
        "bridge_admissibility_proved": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
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


def _review_valid(review: dict[str, Any]) -> bool:
    component_forms = [row["component_form"] for row in TRANSPORT_COMPONENTS]
    return (
        review.get("schema_id") == REVIEW_SCHEMA_ID
        and review.get("packet_id") == REVIEW_PACKET_ID
        and review.get("outcome_id") == REVIEW_OUTCOME
        and review.get("review_result") == REVIEW_OUTCOME
        and review.get("strict_review_result") == STRICT_REVIEW_RESULT
        and review.get("selected_next_target") == CONSUMED_TARGET
        and review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and review.get("suggested_attempt_preparation_outcome")
        == SUGGESTED_ATTEMPT_PREPARATION_OUTCOME
        and review.get("strict_suggested_attempt_preparation_outcome")
        == STRICT_SUGGESTED_ATTEMPT_PREPARATION_OUTCOME
        and review.get("standalone_phi_transport_route")
        == STANDALONE_PHI_TRANSPORT_ROUTE
        and review.get("transport_constraint_form") == TRANSPORT_CONSTRAINT_FORM
        and review.get("transport_constraint_equation") == TRANSPORT_CONSTRAINT_EQUATION
        and review.get("transport_admissibility_constraint_form")
        == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        and review.get("transport_component_count") == len(TRANSPORT_COMPONENTS)
        and review.get("transport_component_forms") == component_forms
        and review.get("likely_componentwise_attempt_route")
        == LIKELY_COMPONENTWISE_ATTEMPT_ROUTE
        and review.get("proof_attempt_executed") is False
        and review.get("theorem_discharged") is False
        and review.get("C_transport_phi_discharged") is False
        and review.get("master_action_promoted") is False
        and review.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_"
            "route"
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
        "full_toeformal_aggregate_status_for_packet": (
            "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
        ),
        "scoped_lean_targets_status_for_packet": "PASSED_SERIAL_RERUN",
        "lean_status_wording_lines_for_packet": LEAN_STATUS_WORDING_LINES_FOR_PACKET,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route(
    *,
    review_path: Path = REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    component_forms = [row["component_form"] for row in TRANSPORT_COMPONENTS]
    acceptance_criteria = {
        "consumes_expected_packet_result_review": _review_valid(review),
        "standalone_phi_transport_registry_tuple_preserved": (
            STANDALONE_PHI_TRANSPORT_ROUTE
            == "prior standalone phi transport-consistency registry"
            and TRANSPORT_CONSTRAINT_FORM
            == "C_transport^phi := (Transport_ACTION_VARIATION^phi, "
            "Transport_VARIATION_BRIDGE^phi, Transport_BRIDGE_SOURCE^phi, "
            "Transport_SOURCE_RESIDUAL^phi, Transport_RESIDUAL_REGIME^phi)"
            and TRANSPORT_CONSTRAINT_EQUATION == "C_transport^phi = 0"
        ),
        "five_component_transport_route_prepared": (
            component_forms
            == [
                TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT,
                TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT,
                TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT,
                TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT,
                TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT,
            ]
        ),
        "componentwise_zero_route_prepared": (
            COMPONENTWISE_ZERO_ROUTE
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
        "route_contamination_blocked": (
            "C_source^phi =" not in " ".join(COMPONENTWISE_ZERO_ROUTE)
            and "C_bridge^phi =" not in " ".join(COMPONENTWISE_ZERO_ROUTE)
            and "J^alpha" not in " ".join(COMPONENTWISE_ZERO_ROUTE)
            and "F^{mu" not in " ".join(COMPONENTWISE_ZERO_ROUTE)
            and "QFT-GR" not in " ".join(COMPONENTWISE_ZERO_ROUTE)
        ),
        "preparation_only_no_theorem_discharge": True,
        "lean_status_wording_preserved": (
            LEAN_STATUS_WORDING_LINES_FOR_PACKET
            == [
                "full ToeFormal aggregate = NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION",
                "scoped Lean targets = PASSED_SERIAL_RERUN",
            ]
        ),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_"
            "PHI_TRANSPORT_ROUTE_PREPARATION"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "attempt_prepared": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_REQUIRES_REMEDIATION",
        "attempt_preparation_result": OUTCOME_ID
        if prepared
        else "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if prepared
        else "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_REQUIRES_REMEDIATION",
        "strict_attempt_preparation_result": STRICT_ATTEMPT_PREPARATION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if prepared else "remediation",
        "suggested_review_outcome": SUGGESTED_REVIEW_OUTCOME,
        "strict_suggested_review_outcome": STRICT_SUGGESTED_REVIEW_OUTCOME,
        "review_schema_id": REVIEW_SCHEMA_ID,
        "review_packet_id": REVIEW_PACKET_ID,
        "review_outcome": REVIEW_OUTCOME,
        "review_result": REVIEW_OUTCOME,
        "review_strict_result": STRICT_REVIEW_RESULT,
        "review_consumed": prepared,
        "prior_review_accepted": prepared,
        "selected_obligation": "C_transport^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_transport^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_transport^phi",
        "standalone_phi_transport_route": STANDALONE_PHI_TRANSPORT_ROUTE,
        "standalone_phi_transport_route_preserved": prepared,
        "exact_five_component_transport_tuple_preserved": prepared,
        "target_C_transport_phi_zero_preserved": prepared,
        "componentwise_zero_target_prepared": prepared,
        "exact_prior_transport_statement": EXACT_PRIOR_TRANSPORT_STATEMENT,
        "exact_prior_transport_target": EXACT_PRIOR_TRANSPORT_TARGET,
        "exact_prior_transport_admissibility_target": (
            EXACT_PRIOR_TRANSPORT_ADMISSIBILITY_TARGET
        ),
        "transport_candidate_id": TRANSPORT_CANDIDATE_ID,
        "transport_candidate_type": TRANSPORT_CANDIDATE_TYPE,
        "transport_rule_classification": TRANSPORT_RULE_CLASSIFICATION,
        "transport_closeout_rule_classification": (
            TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION
        ),
        "transport_rule_role": TRANSPORT_CLOSEOUT_RULE_ROLE,
        "transport_rule_epistemic_status": TRANSPORT_RULE_EPISTEMIC_STATUS,
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_admissibility_constraint_form": (
            TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "transport_component_count": len(TRANSPORT_COMPONENTS),
        "transport_component_forms": component_forms,
        "transport_components_preserved_unproved": True,
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
        "transport_action_variation_component_indexed": prepared,
        "transport_variation_bridge_component_indexed": prepared,
        "transport_bridge_source_component_indexed": prepared,
        "transport_source_residual_component_indexed": prepared,
        "transport_residual_regime_component_indexed": prepared,
        "transport_action_variation_component_preserved": prepared,
        "transport_variation_bridge_component_preserved": prepared,
        "transport_bridge_source_component_preserved": prepared,
        "transport_source_residual_component_preserved": prepared,
        "transport_residual_regime_component_preserved": prepared,
        "transport_action_embedding_chain_form": TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM,
        "known_phi_transport_chain_form": KNOWN_PHI_TRANSPORT_CHAIN_FORM,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_rule_closeout_outcome": BRIDGE_RULE_CLOSEOUT_OUTCOME,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "completed_local_theorem_linkage_chain": COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN,
        "likely_componentwise_attempt_route": LIKELY_COMPONENTWISE_ATTEMPT_ROUTE,
        "componentwise_zero_route": COMPONENTWISE_ZERO_ROUTE,
        "componentwise_zero_route_count": len(COMPONENTWISE_ZERO_ROUTE),
        "C_transport_tuple_zero": C_TRANSPORT_TUPLE_ZERO,
        "target_conclusion": TARGET_CONCLUSION,
        "prepared_linkage_target": PREPARED_LINKAGE_TARGET,
        "plain_meaning": PLAIN_MEANING,
        "prior_plain_meaning": LIKELY_PLAIN_MEANING,
        "route_kind": "standalone_phi_transport_componentwise_zero_preparation",
        "preparation_claims": PREPARATION_CLAIMS,
        "preparation_claim_count": len(PREPARATION_CLAIMS),
        "componentwise_transport_zero_route_indexed": prepared,
        "action_to_regime_transport_match_target_prepared": prepared,
        "action_to_regime_transport_match_promoted_to_master_action": False,
        "same_standalone_phi_transport_registry_tuple": True,
        "same_action_variation_component": True,
        "same_variation_bridge_component": True,
        "same_bridge_source_component": True,
        "same_source_residual_component": True,
        "same_residual_regime_component": True,
        "same_component_order": True,
        "same_target_C_transport_phi_zero": True,
        "route_contamination_guard": (
            "prepare only the componentwise standalone phi transport route; do "
            "not substitute C_source^phi, C_bridge^phi, A-sector, psi-A, QFT-GR, "
            "or master-action routes and do not treat action-to-regime transport "
            "match as action variation or master-action promotion"
        ),
        "watch_items": WATCH_ITEMS,
        "watch_item_count": len(WATCH_ITEMS),
        "boundary_items": BOUNDARY_ITEMS,
        "boundary_item_count": len(BOUNDARY_ITEMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": prepared,
        "claim_ladder_position": (
            "below theorem discharge, phi-sector closure, scalar/QFT closure, "
            "seam closure, empirical prediction, empirical confirmation, and "
            "mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This packet prepares only the standalone phi-transport "
            "C_transport^phi theorem-linkage attempt from the frozen tuple "
            "C_transport^phi := (Transport_ACTION_VARIATION^phi, "
            "Transport_VARIATION_BRIDGE^phi, Transport_BRIDGE_SOURCE^phi, "
            "Transport_SOURCE_RESIDUAL^phi, Transport_RESIDUAL_REGIME^phi). "
            "It indexes the component targets Transport_ACTION_VARIATION^phi = 0, "
            "Transport_VARIATION_BRIDGE^phi = 0, Transport_BRIDGE_SOURCE^phi = 0, "
            "Transport_SOURCE_RESIDUAL^phi = 0, and "
            "Transport_RESIDUAL_REGIME^phi = 0, then targets "
            "C_transport^phi = (0, 0, 0, 0, 0) and C_transport^phi = 0. It "
            "does not execute a proof, discharge C_transport^phi, claim "
            "phi-sector closure, claim scalar/QFT closure, close EM-QFT or "
            "QFT-GR, claim general C_k closure, embed or vary an action, claim "
            "empirical validation, or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route",
            "fail to preserve the frozen C_transport^phi tuple",
            "fail to prepare Transport_ACTION_VARIATION^phi = 0",
            "fail to prepare Transport_VARIATION_BRIDGE^phi = 0",
            "fail to prepare Transport_BRIDGE_SOURCE^phi = 0",
            "fail to prepare Transport_SOURCE_RESIDUAL^phi = 0",
            "fail to prepare Transport_RESIDUAL_REGIME^phi = 0",
            "silently substitute C_source^phi, C_bridge^phi, A-sector, psi-A, QFT-GR, or master-action routes",
            "execute the theorem attempt during preparation",
            "discharge C_transport^phi during preparation",
            "claim phi-sector closure",
            "claim full scalar/QFT closure",
            "claim EM-QFT or QFT-GR closure",
            "claim general C_k closure",
            "embed or vary an action",
            "treat action-to-regime transport match as master-action promotion",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_PACKET,
        "lean_status_wording_lines": LEAN_STATUS_WORDING_LINES_FOR_PACKET,
        "full_toeformal_aggregate_status_for_packet": (
            "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
        ),
        "scoped_lean_targets_status_for_packet": "PASSED_SERIAL_RERUN",
        "aggregate_lean_validation_status_for_packet": "PASSED_SERIAL_RERUN",
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiTransportTheoremLinkageAttemptFromStandalonePhiTransportRoute",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "review_file": _ptr(review_path),
            "review_lean_file": _ptr(REVIEW_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_false_boundary_flags())
    return payload


def write_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Prepare the standalone phi-transport C_transport^phi componentwise "
            "zero theorem-linkage attempt without executing or discharging it."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--review", type=Path, default=REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = args.review if args.review.is_absolute() else REPO_ROOT / args.review
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    packet = (
        build_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route(
            review_path=review_path,
            captured_at_utc=args.captured_at_utc,
        )
    )
    path = write_packet(packet, out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "out": _ptr(path),
                "attempt_preparation_result": packet["attempt_preparation_result"],
                "selected_next_target": packet["selected_next_target"],
                "transport_constraint_form": packet["transport_constraint_form"],
                "target_conclusion": packet["target_conclusion"],
                "proof_attempt_executed": packet["proof_attempt_executed"],
                "theorem_discharged": packet["theorem_discharged"],
                "master_action_promoted": packet["master_action_promoted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if packet["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
