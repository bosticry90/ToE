from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_report import (
    COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN,
    DEFAULT_OUT as SELECTION_PATH,
    FOLLOW_ON_TARGET_AFTER_REVIEW as SELECTOR_FOLLOW_ON_TARGET_AFTER_REVIEW,
    FOLLOW_ON_TARGET_KIND as SELECTOR_FOLLOW_ON_TARGET_KIND,
    FORBIDDEN_REUSED_ROUTES,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION,
    LEAN_PACKET_PATH as SELECTION_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_SELECTION,
    LEAN_STATUS_WORDING_LINES_FOR_SELECTION,
    MAIN_WATCH_ITEM as SELECTOR_MAIN_WATCH_ITEM,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as SELECTION_OUTCOME,
    PACKET_ID as SELECTION_PACKET_ID,
    PHI_TRANSPORT_REGISTRY_BOUNDARY,
    PLAIN_MEANING,
    ROUTE_BOUNDARY,
    SCHEMA_ID as SELECTION_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION,
    SELECTED_OBLIGATION,
    SELECTED_OBLIGATION_ROW_ID,
    SELECTED_THEOREM_LINKAGE_GAP,
    SELECTION_REASON,
    SELECTION_RESULT,
    STRICT_SELECTION_RESULT,
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
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_BRIDGE_"
    "CLOSEOUT_RESULT_REVIEW_20260630_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_BRIDGE_"
    "CLOSEOUT_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_BRIDGE_CLOSEOUT_"
    "RESULT_REVIEW_ACCEPTS_C_TRANSPORT_PHI_THEOREM_LINKAGE_GAP_SELECTION_NO_"
    "PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_BRIDGE_CLOSEOUT_"
    "RESULT_REVIEW_ACCEPTS_PHI_TRANSPORT_LINKAGE_SELECTION_ONLY_NO_GAP_DISCHARGE_"
    "OR_CK_RULE_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_"
    "result_review_accepts_phi_transport_selection_only"
)

NEXT_TARGET = "prepare_phi_transport_theorem_linkage_obligation_packet"
NEXT_TARGET_KIND = "phi_transport_theorem_linkage_obligation_packet"
LIKELY_POST_PACKET_REVIEW_TARGET = (
    "review_phi_transport_theorem_linkage_obligation_packet_result"
)
LIKELY_POST_PACKET_REVIEW_KIND = (
    "phi_transport_theorem_linkage_obligation_packet_result_review"
)
LIKELY_PACKET_OUTCOME = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_C_TRANSPORT_PHI_"
    "ROUTE_SCOPED_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
STRICT_LIKELY_PACKET_OUTCOME = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_STANDALONE_PHI_"
    "TRANSPORT_CONSISTENCY_TARGET_NO_THEOREM_DISCHARGE_OR_MASTER_ACTION_PROMOTION"
)

NEXT_PACKET_SCOPE_INSTRUCTION = (
    "Scope the C_transport^phi theorem-linkage obligation only, recovering the "
    "exact C_transport^phi statement, transport-chain stability components, "
    "component order, sign convention, covariant derivative convention, and "
    "boundary/domain assumptions from the prior standalone phi "
    "transport-consistency registry."
)
LIKELY_SCHEMATIC_TARGET = (
    f"{TRANSPORT_CONSTRAINT_FORM}; {TRANSPORT_CONSTRAINT_EQUATION}"
)
NEXT_PACKET_RECOVERY_ITEMS = [
    "exact C_transport^phi statement from the prior standalone phi transport-consistency registry",
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    "transport-chain stability components",
    "component order",
    "sign convention",
    "covariant derivative convention",
    "boundary and domain assumptions",
    "no C_source^phi, C_bridge^phi, A-sector, psi-A, QFT-GR, or master-action route substitution",
]
MAIN_WATCH_ITEM = (
    "Recover the exact C_transport^phi statement from the prior standalone phi "
    "transport-consistency registry. Do not silently substitute C_source^phi, "
    "C_bridge^phi, A-sector, psi-A, QFT-GR, or master-action routes."
)

REVIEW_ACCEPTANCE_SUMMARY = [
    "selector result accepted",
    "C_transport^phi theorem-linkage obligation selected",
    "selection follows completed C_source^phi and C_bridge^phi local linkages",
    "prior phi-source and phi-bridge closeouts remain bounded",
    "no phi transport proof execution",
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

BLOCKED_CLAIMS = [
    "no proof execution during review",
    "no C_transport^phi discharge during review",
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

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION
LEAN_STATUS_WORDING_LINES_FOR_REVIEW = LEAN_STATUS_WORDING_LINES_FOR_SELECTION
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_SELECTION

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_BRIDGE_"
        "CLOSEOUT_RESULT_REVIEW_20260630_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / (
        "CKFamilyTheoremLinkageObligationSelectionAfterPhiBridgeCloseoutResultReview.lean"
    )
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
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "C_transport_phi_discharged": False,
        "C_transport_phi_theorem_linkage_gap_discharged": False,
        "C_transport_phi_theorem_linkage_obligation_discharged": False,
        "C_transport_phi_proof_executed": False,
        "C_transport_phi_closure_claimed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
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
        "obligation_row_discharged": False,
        "obligation_rows_discharged": False,
        "new_physics_created": False,
    }


def _selector_valid(selector: dict[str, Any]) -> bool:
    return (
        selector.get("schema_id") == SELECTION_SCHEMA_ID
        and selector.get("packet_id") == SELECTION_PACKET_ID
        and selector.get("outcome_id") == SELECTION_OUTCOME
        and selector.get("selection_result") == SELECTION_RESULT
        and selector.get("strict_selection_result") == STRICT_SELECTION_RESULT
        and selector.get("selected_next_target") == CONSUMED_TARGET
        and selector.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and selector.get("follow_on_target_after_review")
        == SELECTOR_FOLLOW_ON_TARGET_AFTER_REVIEW
        and selector.get("follow_on_target_kind") == SELECTOR_FOLLOW_ON_TARGET_KIND
        and selector.get("selected_obligation") == SELECTED_OBLIGATION
        and selector.get("selected_theorem_linkage_gap") == SELECTED_THEOREM_LINKAGE_GAP
        and selector.get("selected_obligation_row_id") == SELECTED_OBLIGATION_ROW_ID
        and selector.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "ck_family_theorem_linkage_obligation_selection_after_phi_bridge_"
            "closeout_result_review"
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
        "full_toeformal_aggregate_status_for_review": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "lean_status_wording_lines_for_review": LEAN_STATUS_WORDING_LINES_FOR_REVIEW,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_result_review(
    *,
    selection_path: Path = SELECTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector = _read_json(selection_path)
    acceptance_criteria = {
        "consumes_expected_selector_result": _selector_valid(selector),
        "selector_result_accepted": selector.get("accepted") is True,
        "C_transport_phi_theorem_linkage_obligation_selected": (
            selector.get("selected_obligation") == SELECTED_OBLIGATION
            and selector.get("selected_theorem_linkage_gap")
            == SELECTED_THEOREM_LINKAGE_GAP
            and selector.get("selected_obligation_row_id")
            == SELECTED_OBLIGATION_ROW_ID
        ),
        "selection_follows_completed_C_source_phi_and_C_bridge_phi_linkages": (
            selector.get("C_source_phi_locally_linked") is True
            and selector.get("C_bridge_phi_locally_linked") is True
            and selector.get("completed_local_theorem_linkage_chain")
            == COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN
        ),
        "prior_phi_source_and_phi_bridge_closeouts_remain_bounded": (
            selector.get("C_source_phi_locally_linked") is True
            and selector.get("C_bridge_phi_locally_linked") is True
            and selector.get("phi_sector_closure_claimed") is False
            and selector.get("full_scalar_qft_closure_claimed") is False
        ),
        "prior_standalone_phi_transport_registry_preserved": (
            selector.get("phi_transport_registry_boundary")
            == PHI_TRANSPORT_REGISTRY_BOUNDARY
            and selector.get("prior_phi_transport_constraint_form")
            == TRANSPORT_CONSTRAINT_FORM
            and selector.get("prior_phi_transport_constraint_equation")
            == TRANSPORT_CONSTRAINT_EQUATION
            and selector.get("prior_phi_transport_admissibility_constraint_form")
            == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "no_forbidden_review_claims": (
            selector.get("proof_attempt_executed") is False
            and selector.get("theorem_discharged") is False
            and selector.get("gap_discharged") is False
            and selector.get("phi_sector_closure_claimed") is False
            and selector.get("full_scalar_qft_closure_claimed") is False
            and selector.get("qft_gr_closure_claimed") is False
            and selector.get("em_qft_closure_claimed") is False
            and selector.get("seam_closure_claim") is False
            and selector.get("general_C_k_closure") is False
            and selector.get("rule_promoted") is False
            and selector.get("action_embedding_claimed") is False
            and selector.get("action_variation_executed") is False
            and selector.get("empirical_validation_claimed") is False
            and selector.get("master_action_promoted") is False
        ),
        "packet_preparation_target_preserved_without_discharge": (
            SELECTOR_FOLLOW_ON_TARGET_AFTER_REVIEW == NEXT_TARGET
            and ROUTE_BOUNDARY.startswith("selector only")
        ),
        "lean_status_wording_careful": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_BRIDGE_CLOSEOUT_RESULT_REVIEW"
    )
    transport_component_forms = [row["component_form"] for row in TRANSPORT_COMPONENTS]
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_"
            "PHI_BRIDGE_CLOSEOUT_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_BRIDGE_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_BRIDGE_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_BRIDGE_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if accepted else "remediation",
        "likely_post_packet_review_target": LIKELY_POST_PACKET_REVIEW_TARGET,
        "likely_post_packet_review_kind": LIKELY_POST_PACKET_REVIEW_KIND,
        "likely_packet_outcome": LIKELY_PACKET_OUTCOME,
        "strict_likely_packet_outcome": STRICT_LIKELY_PACKET_OUTCOME,
        "selection_schema_id": SELECTION_SCHEMA_ID,
        "selection_packet_id": SELECTION_PACKET_ID,
        "selection_outcome": SELECTION_OUTCOME,
        "selection_result": SELECTION_RESULT,
        "selection_strict_outcome": STRICT_SELECTION_RESULT,
        "selector_result_consumed": accepted,
        "selector_result_accepted": accepted,
        "completed_local_theorem_linkage_chain": COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN,
        "completed_local_theorem_linkage_chain_count": len(
            COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN
        ),
        "prior_phi_source_and_phi_bridge_closeouts_remain_bounded": accepted,
        "C_exchange_Apsi_locally_linked": accepted,
        "C_source_A_locally_linked": accepted,
        "C_source_phi_locally_linked": accepted,
        "C_bridge_phi_locally_linked": accepted,
        "selected_obligation": SELECTED_OBLIGATION,
        "selected_theorem_linkage_gap": SELECTED_THEOREM_LINKAGE_GAP,
        "selected_obligation_row_id": SELECTED_OBLIGATION_ROW_ID,
        "C_transport_phi_selected_as_next_unresolved_obligation": accepted,
        "selection_follows_completed_C_source_phi_and_C_bridge_phi_linkages": accepted,
        "next_theorem_linkage_obligation_selected": accepted,
        "follow_on_target_preserved": accepted,
        "follow_on_target_after_review": NEXT_TARGET,
        "follow_on_target_kind": NEXT_TARGET_KIND,
        "review_acceptance_summary": REVIEW_ACCEPTANCE_SUMMARY,
        "selection_reason": SELECTION_REASON,
        "plain_meaning": PLAIN_MEANING,
        "route_boundary": ROUTE_BOUNDARY,
        "phi_transport_registry_boundary": PHI_TRANSPORT_REGISTRY_BOUNDARY,
        "prior_phi_transport_candidate_id": TRANSPORT_CANDIDATE_ID,
        "prior_phi_transport_candidate_type": TRANSPORT_CANDIDATE_TYPE,
        "prior_phi_transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "prior_phi_transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "prior_phi_transport_admissibility_constraint_form": (
            TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "prior_phi_transport_rule_classification": TRANSPORT_RULE_CLASSIFICATION,
        "prior_phi_transport_closeout_rule_classification": (
            TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION
        ),
        "prior_phi_transport_rule_role": TRANSPORT_CLOSEOUT_RULE_ROLE,
        "prior_phi_transport_rule_epistemic_status": (
            TRANSPORT_RULE_EPISTEMIC_STATUS
        ),
        "prior_phi_transport_component_count": len(TRANSPORT_COMPONENTS),
        "prior_phi_transport_component_forms": transport_component_forms,
        "forbidden_reused_routes": FORBIDDEN_REUSED_ROUTES,
        "selector_main_watch_item": SELECTOR_MAIN_WATCH_ITEM,
        "main_watch_item": MAIN_WATCH_ITEM,
        "next_packet_scope": NEXT_PACKET_SCOPE_INSTRUCTION,
        "next_packet_scope_instruction": NEXT_PACKET_SCOPE_INSTRUCTION,
        "likely_schematic_target_subject_to_registry_wording": (
            LIKELY_SCHEMATIC_TARGET
        ),
        "next_packet_recovery_items": NEXT_PACKET_RECOVERY_ITEMS,
        "next_packet_recovery_item_count": len(NEXT_PACKET_RECOVERY_ITEMS),
        "review_only": accepted,
        "review_executes_proof": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "C_transport_phi_discharged": False,
        "C_transport_phi_theorem_linkage_gap_discharged": False,
        "C_transport_phi_theorem_linkage_obligation_discharged": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "claim_ladder_position": (
            "below phi-sector closure, scalar/QFT closure, QFT-GR closure, "
            "EM-QFT closure, seam closure, empirical prediction, empirical "
            "confirmation, and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only the post-phi-bridge-closeout C_k "
            "theorem-linkage obligation selector result. It accepts that "
            "C_transport^phi was selected as the next theorem-linkage "
            "obligation and preserves phi transport obligation-packet "
            "preparation as the next target. It keeps that future packet tied "
            "to the prior standalone phi transport-consistency registry. It "
            "does not execute any proof, discharge C_transport^phi, claim "
            "phi-sector closure, claim scalar/QFT closure, claim QFT-GR or "
            "EM-QFT closure, close a seam, claim general C_k closure, promote "
            "any C_k rule, embed or vary an action, claim empirical "
            "validation, import or substitute C_source^phi, C_bridge^phi, "
            "A-sector, psi-A, QFT-GR, or master-action routes as the transport "
            "route, or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_result",
            "fail to accept the C_transport^phi theorem-linkage obligation selection",
            "fail to select prepare_phi_transport_theorem_linkage_obligation_packet",
            "fail to recover the prior standalone phi transport-consistency registry",
            "execute proof during review",
            "discharge C_transport^phi during review",
            "claim phi-sector closure",
            "claim scalar/QFT closure",
            "claim QFT-GR closure",
            "claim EM-QFT closure",
            "close a seam",
            "claim general C_k closure",
            "promote a C_k rule",
            "embed or vary an action",
            "substitute C_source^phi or C_bridge^phi as the transport route",
            "import A-sector, psi-A, QFT-GR, or master-action routes as the transport route",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_REVIEW,
        "lean_status_wording_lines": LEAN_STATUS_WORDING_LINES_FOR_REVIEW,
        "full_toeformal_aggregate_status_for_review": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "aggregate_lean_validation_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterPhiBridgeCloseoutResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "selection_file": _ptr(selection_path),
            "selection_lean_file": _ptr(SELECTION_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
    return payload


def write_review(review: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(review, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Review the post-phi-bridge-closeout C_k theorem-linkage obligation "
            "selector result."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--selection", type=Path, default=SELECTION_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    selection_path = (
        args.selection if args.selection.is_absolute() else REPO_ROOT / args.selection
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_result_review(
            selection_path=selection_path,
            captured_at_utc=args.captured_at_utc,
        )
    )
    path = write_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
                "selected_obligation": payload["selected_obligation"],
                "selected_next_target": payload["selected_next_target"],
                "likely_packet_outcome": payload["likely_packet_outcome"],
                "proof_attempt_executed": payload["proof_attempt_executed"],
                "C_transport_phi_discharged": payload["C_transport_phi_discharged"],
                "phi_sector_closure_claimed": payload[
                    "phi_sector_closure_claimed"
                ],
                "qft_gr_closure_claimed": payload["qft_gr_closure_claimed"],
                "em_qft_closure_claimed": payload["em_qft_closure_claimed"],
                "rule_promoted": payload["rule_promoted"],
                "lean_status_wording_lines": payload["lean_status_wording_lines"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if payload["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
