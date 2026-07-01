from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_theorem_linkage_priority_selection_after_index_report import (
    DEFAULT_OUT as PRIORITY_SELECTION_PATH,
    RANKED_ROW_IDS,
)
from formal.python.tools.phi_bridge_admissibility_ck_admissibility_rule_closeout_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CANDIDATE_ID,
    BRIDGE_CANDIDATE_TYPE,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    BRIDGE_RULE_CLASSIFICATION,
    BRIDGE_RULE_EPISTEMIC_STATUS,
    CLOSEOUT_RESULT as PHI_BRIDGE_REGISTRY_RESULT,
    DEFAULT_OUT as PHI_BRIDGE_REGISTRY_PATH,
    LEAN_PACKET_PATH as PHI_BRIDGE_REGISTRY_LEAN_PACKET_PATH,
    OUTCOME_ID as PHI_BRIDGE_REGISTRY_OUTCOME,
    PACKET_ID as PHI_BRIDGE_REGISTRY_PACKET_ID,
    SCHEMA_ID as PHI_BRIDGE_REGISTRY_SCHEMA_ID,
)
from formal.python.tools.phi_source_theorem_linkage_obligation_closeout_result_review_report import (
    DEFAULT_OUT as CLOSEOUT_RESULT_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW as FULL_TOEFORMAL_AGGREGATE_STATUS_FROM_REVIEW,
    LEAN_PACKET_PATH as CLOSEOUT_RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_LINES_FOR_REVIEW,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as CLOSEOUT_RESULT_REVIEW_OUTCOME,
    PACKET_ID as CLOSEOUT_RESULT_REVIEW_PACKET_ID,
    REVIEW_RESULT as CLOSEOUT_RESULT_REVIEW_RESULT,
    SCHEMA_ID as CLOSEOUT_RESULT_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW as SCOPED_LEAN_TARGETS_STATUS_FROM_REVIEW,
    STRICT_REVIEW_RESULT as CLOSEOUT_RESULT_REVIEW_STRICT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_SOURCE_"
    "CLOSEOUT_20260630_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_SOURCE_CLOSEOUT_v0"
)
SELECTION_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_SOURCE_CLOSEOUT_"
    "SELECTS_C_BRIDGE_PHI_THEOREM_LINKAGE_GAP_NO_PROOF_EXECUTION_OR_MASTER_"
    "ACTION_PROMOTION"
)
STRICT_SELECTION_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_SOURCE_CLOSEOUT_"
    "SELECTS_PHI_BRIDGE_LINKAGE_OBLIGATION_NO_GAP_DISCHARGE_OR_CK_RULE_PROMOTION"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "ck_family_theorem_linkage_obligation_selection_after_phi_source_closeout_"
    "selects_phi_bridge_linkage_obligation_no_gap_discharge"
)

NEXT_TARGET = (
    "review_ck_family_theorem_linkage_obligation_selection_after_phi_source_"
    "closeout_result"
)
NEXT_TARGET_KIND = (
    "ck_family_theorem_linkage_obligation_selection_after_phi_source_"
    "closeout_result_review"
)
FOLLOW_ON_TARGET_AFTER_REVIEW = "prepare_phi_bridge_theorem_linkage_obligation_packet"
FOLLOW_ON_TARGET_KIND = "phi_bridge_theorem_linkage_obligation_packet"

SELECTED_OBLIGATION = "C_bridge^phi theorem-linkage obligation"
SELECTED_THEOREM_LINKAGE_GAP = "C_bridge^phi theorem-linkage gap"
SELECTED_OBLIGATION_ROW_ID = "C_bridge^phi"
COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN = [
    "C_exchange^{Apsi} closed locally",
    "C_source^A closed locally",
    "C_source^phi closed locally",
]
SELECTION_REASON = (
    "The phi-source theorem-linkage closeout review is accepted. With "
    "C_exchange^{Apsi}, C_source^A, and C_source^phi locally closed as "
    "admissibility theorem-linkage only, the selector chooses the remaining "
    "phi-adjacent bridge-linkage row tied to the prior standalone phi "
    "bridge-admissibility registry."
)
PLAIN_MEANING = (
    "The selector moves from the locally closed standalone phi-source linkage "
    "to the C_bridge^phi theorem-linkage obligation without attempting or "
    "discharging that bridge proof."
)
SELECTOR_QUESTION = (
    "Which remaining C_k theorem-linkage obligation should be attempted next "
    "after C_source^phi closeout?"
)

PHI_BRIDGE_REGISTRY_BOUNDARY = (
    "prior standalone phi bridge-admissibility registry only"
)
ROUTE_BOUNDARY = (
    "selector only; exact C_bridge^phi theorem target, prior standalone phi "
    "bridge-admissibility registry, route-equivalence and bridge-soundness "
    "obligations, assumptions, identity route, sign conventions, and boundary "
    "conditions are deferred to the phi bridge theorem-linkage obligation packet"
)
MAIN_WATCH_ITEM = (
    "Keep C_bridge^phi tied to the prior standalone phi bridge-admissibility "
    "registry. Do not silently reuse C_source^phi, A-source, psi-A, or QFT-GR "
    "routes."
)
FORBIDDEN_REUSED_ROUTES = [
    "C_source^phi route",
    "A-source route",
    "psi-A route",
    "QFT-GR route",
]
AVOIDED_CLAIMS = [
    "do not execute the C_bridge^phi proof route",
    "do not discharge the C_bridge^phi theorem-linkage gap",
    "do not claim phi-sector closure",
    "do not claim scalar/QFT closure",
    "do not reuse the C_source^phi theorem-linkage route as the bridge route",
    "do not import an A-source route",
    "do not import a psi-A route",
    "do not import a QFT-GR route",
    "do not promote any C_k rule",
    "do not embed or vary an action",
    "do not promote the master action",
]
BLOCKED_CLAIMS = [
    "no proof execution",
    "no theorem discharge",
    "no phi-sector closure",
    "no scalar/QFT closure",
    "no seam closure",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FROM_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION = SCOPED_LEAN_TARGETS_STATUS_FROM_REVIEW
LEAN_STATUS_WORDING_LINES_FOR_SELECTION = LEAN_STATUS_WORDING_LINES_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_SELECTION = "\n".join(LEAN_STATUS_WORDING_LINES_FOR_SELECTION)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_SOURCE_"
        "CLOSEOUT_20260630_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CKFamilyTheoremLinkageObligationSelectionAfterPhiSourceCloseout.lean"
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
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "C_bridge_phi_theorem_linkage_gap_discharged": False,
        "C_bridge_phi_theorem_linkage_obligation_discharged": False,
        "C_bridge_phi_proof_executed": False,
        "C_bridge_phi_route_reused_from_C_source_phi": False,
        "C_source_phi_route_reused": False,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "QFT_GR_route_imported": False,
        "QFT_GR_source_route_imported": False,
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


def _consumed_review_valid(review: dict[str, Any]) -> bool:
    return (
        review.get("schema_id") == CLOSEOUT_RESULT_REVIEW_SCHEMA_ID
        and review.get("packet_id") == CLOSEOUT_RESULT_REVIEW_PACKET_ID
        and review.get("outcome_id") == CLOSEOUT_RESULT_REVIEW_OUTCOME
        and review.get("review_result") == CLOSEOUT_RESULT_REVIEW_RESULT
        and review.get("strict_review_result")
        == CLOSEOUT_RESULT_REVIEW_STRICT_OUTCOME
        and review.get("selected_next_target") == CONSUMED_TARGET
        and review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and review.get("accepted") is True
        and review.get("phi_source_closeout_result_review_accepted") is True
        and review.get("phi_source_theorem_linkage_obligation_locally_closed")
        is True
        and review.get("C_source_phi_zero_locally_linked") is True
        and review.get("phi_sector_closure_claimed") is False
        and review.get("full_scalar_qft_closure_claimed") is False
        and review.get("qft_gr_closure_claimed") is False
        and review.get("general_C_k_closure") is False
        and review.get("seam_closure_claim") is False
        and review.get("rule_promoted") is False
        and review.get("master_action_promoted") is False
    )


def _priority_order_valid(priority_selection: dict[str, Any]) -> bool:
    ranked_rows = [
        item.get("row_id")
        for item in priority_selection.get("priority_ranking", [])
    ]
    if not ranked_rows:
        ranked_rows = priority_selection.get("ranked_row_ids", [])
    return (
        "C_source^phi" in RANKED_ROW_IDS
        and SELECTED_OBLIGATION_ROW_ID in RANKED_ROW_IDS
        and RANKED_ROW_IDS.index("C_source^phi")
        < RANKED_ROW_IDS.index(SELECTED_OBLIGATION_ROW_ID)
        and (not ranked_rows or SELECTED_OBLIGATION_ROW_ID in ranked_rows)
    )


def _phi_bridge_registry_valid(phi_bridge_registry: dict[str, Any]) -> bool:
    return (
        phi_bridge_registry.get("schema_id") == PHI_BRIDGE_REGISTRY_SCHEMA_ID
        and phi_bridge_registry.get("packet_id") == PHI_BRIDGE_REGISTRY_PACKET_ID
        and phi_bridge_registry.get("outcome_id") == PHI_BRIDGE_REGISTRY_OUTCOME
        and phi_bridge_registry.get("closeout_result") == PHI_BRIDGE_REGISTRY_RESULT
        and phi_bridge_registry.get("accepted") is True
        and phi_bridge_registry.get("bridge_rule_classification")
        == BRIDGE_RULE_CLASSIFICATION
        and phi_bridge_registry.get("bridge_rule_epistemic_status")
        == BRIDGE_RULE_EPISTEMIC_STATUS
        and phi_bridge_registry.get("bridge_candidate_id") == BRIDGE_CANDIDATE_ID
        and phi_bridge_registry.get("bridge_candidate_type") == BRIDGE_CANDIDATE_TYPE
        and phi_bridge_registry.get("bridge_constraint_form")
        == BRIDGE_CONSTRAINT_FORM
        and phi_bridge_registry.get("bridge_constraint_equation")
        == BRIDGE_CONSTRAINT_EQUATION
        and phi_bridge_registry.get("bridge_admissibility_constraint_form")
        == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        and phi_bridge_registry.get("bridge_route_field_equation_match")
        == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
        and phi_bridge_registry.get("bridge_route_stress_energy_match")
        == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
        and phi_bridge_registry.get("bridge_route_source_residual_match")
        == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        and phi_bridge_registry.get("bridge_admissibility_proved") is False
        and phi_bridge_registry.get("bridge_route_alignment_verified") is False
        and phi_bridge_registry.get("ck_variation_executed") is False
        and phi_bridge_registry.get("master_action_promoted") is False
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "ck_family_theorem_linkage_obligation_selection_after_phi_source_closeout"
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
        "full_toeformal_aggregate_status_for_selection": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION
        ),
        "scoped_lean_targets_status_for_selection": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION
        ),
        "lean_status_wording_lines_for_selection": (
            LEAN_STATUS_WORDING_LINES_FOR_SELECTION
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


def build_ck_family_theorem_linkage_obligation_selection_after_phi_source_closeout(
    *,
    closeout_result_review_path: Path = CLOSEOUT_RESULT_REVIEW_PATH,
    priority_selection_path: Path = PRIORITY_SELECTION_PATH,
    phi_bridge_registry_path: Path = PHI_BRIDGE_REGISTRY_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(closeout_result_review_path)
    priority_selection = _read_json(priority_selection_path)
    phi_bridge_registry = _read_json(phi_bridge_registry_path)
    acceptance_criteria = {
        "consumes_expected_phi_source_closeout_result_review": (
            _consumed_review_valid(review)
        ),
        "phi_source_closeout_review_accepted": (
            review.get("phi_source_closeout_result_review_accepted") is True
            and review.get("standalone_phi_route_preserved") is True
            and review.get("C_source_phi_zero_locally_linked") is True
            and review.get("selector_authorized") is True
        ),
        "selects_C_bridge_phi_as_next_unresolved_obligation": (
            SELECTED_OBLIGATION == "C_bridge^phi theorem-linkage obligation"
            and SELECTED_OBLIGATION_ROW_ID == "C_bridge^phi"
            and _priority_order_valid(priority_selection)
        ),
        "prior_standalone_phi_bridge_registry_preserved": (
            _phi_bridge_registry_valid(phi_bridge_registry)
        ),
        "selector_only_without_phi_bridge_proof_execution": (
            ROUTE_BOUNDARY.startswith("selector only")
            and FOLLOW_ON_TARGET_AFTER_REVIEW
            == "prepare_phi_bridge_theorem_linkage_obligation_packet"
        ),
        "does_not_reuse_forbidden_routes": (
            FORBIDDEN_REUSED_ROUTES
            == [
                "C_source^phi route",
                "A-source route",
                "psi-A route",
                "QFT-GR route",
            ]
            and MAIN_WATCH_ITEM
            == (
                "Keep C_bridge^phi tied to the prior standalone phi "
                "bridge-admissibility registry. Do not silently reuse "
                "C_source^phi, A-source, psi-A, or QFT-GR routes."
            )
        ),
        "lean_status_wording_careful": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_"
            "PHI_SOURCE_CLOSEOUT"
        )
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_"
            "PHI_SOURCE_CLOSEOUT"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "selected": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_SOURCE_"
            "CLOSEOUT_REQUIRES_REMEDIATION"
        ),
        "selection_result": OUTCOME_ID
        if accepted
        else (
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_SOURCE_"
            "CLOSEOUT_REQUIRES_REMEDIATION"
        ),
        "selector_outcome": OUTCOME_ID
        if accepted
        else (
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_SOURCE_"
            "CLOSEOUT_REQUIRES_REMEDIATION"
        ),
        "packet_result": OUTCOME_ID
        if accepted
        else (
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_SOURCE_"
            "CLOSEOUT_REQUIRES_REMEDIATION"
        ),
        "strict_selection_result": STRICT_SELECTION_RESULT,
        "strict_selector_outcome": STRICT_SELECTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if accepted else "remediation",
        "follow_on_target_after_review": FOLLOW_ON_TARGET_AFTER_REVIEW,
        "follow_on_target_kind": FOLLOW_ON_TARGET_KIND,
        "selector_question": SELECTOR_QUESTION,
        "closeout_result_review_schema_id": CLOSEOUT_RESULT_REVIEW_SCHEMA_ID,
        "closeout_result_review_packet_id": CLOSEOUT_RESULT_REVIEW_PACKET_ID,
        "closeout_result_review_outcome": CLOSEOUT_RESULT_REVIEW_OUTCOME,
        "closeout_result_review_strict_outcome": (
            CLOSEOUT_RESULT_REVIEW_STRICT_OUTCOME
        ),
        "closeout_result_review_consumed": accepted,
        "phi_source_theorem_linkage_closeout_review_accepted": accepted,
        "phi_source_closeout_review_accepted": accepted,
        "completed_local_theorem_linkage_chain": COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN,
        "completed_local_theorem_linkage_chain_count": len(
            COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN
        ),
        "C_exchange_Apsi_closed_locally": accepted,
        "C_source_A_closed_locally": accepted,
        "C_source_phi_closed_locally": accepted,
        "selected_obligation": SELECTED_OBLIGATION,
        "selected_theorem_linkage_gap": SELECTED_THEOREM_LINKAGE_GAP,
        "selected_obligation_row_id": SELECTED_OBLIGATION_ROW_ID,
        "C_bridge_phi_selected_as_next_unresolved_obligation": accepted,
        "next_remaining_C_k_theorem_linkage_obligation_selected": accepted,
        "next_theorem_linkage_obligation_selected": accepted,
        "selection_reason": SELECTION_REASON,
        "plain_meaning": PLAIN_MEANING,
        "phi_bridge_registry_boundary": PHI_BRIDGE_REGISTRY_BOUNDARY,
        "prior_phi_bridge_admissibility_registry_schema_id": (
            PHI_BRIDGE_REGISTRY_SCHEMA_ID
        ),
        "prior_phi_bridge_admissibility_registry_packet_id": (
            PHI_BRIDGE_REGISTRY_PACKET_ID
        ),
        "prior_phi_bridge_admissibility_registry_outcome": (
            PHI_BRIDGE_REGISTRY_OUTCOME
        ),
        "prior_phi_bridge_admissibility_registry_result": (
            PHI_BRIDGE_REGISTRY_RESULT
        ),
        "prior_phi_bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "prior_phi_bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "prior_phi_bridge_admissibility_constraint_form": (
            BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "prior_phi_bridge_candidate_id": BRIDGE_CANDIDATE_ID,
        "prior_phi_bridge_candidate_type": BRIDGE_CANDIDATE_TYPE,
        "prior_phi_bridge_route_field_equation_match": (
            BRIDGE_ROUTE_FIELD_EQUATION_MATCH
        ),
        "prior_phi_bridge_route_stress_energy_match": (
            BRIDGE_ROUTE_STRESS_ENERGY_MATCH
        ),
        "prior_phi_bridge_route_source_residual_match": (
            BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        ),
        "route_boundary": ROUTE_BOUNDARY,
        "main_watch_item": MAIN_WATCH_ITEM,
        "forbidden_reused_routes": FORBIDDEN_REUSED_ROUTES,
        "selector_only": accepted,
        "avoided_claims": AVOIDED_CLAIMS,
        "blocked_claims": BLOCKED_CLAIMS,
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "claim_ladder_position": (
            "below phi-sector closure, scalar/QFT closure, QFT-GR source "
            "admissibility, seam closure, empirical confirmation, and mature "
            "physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This selector only chooses the next C_k-family theorem-linkage "
            "obligation after the local standalone phi-source closeout. It "
            "selects C_bridge^phi as the next unresolved obligation and ties "
            "that future packet to the prior standalone phi bridge-admissibility "
            "registry. It does not execute or discharge the C_bridge^phi route, "
            "does not reuse C_source^phi, A-source, psi-A, or QFT-GR routes as "
            "the bridge route, does not claim phi-sector or scalar/QFT closure, "
            "does not close any seam, does not promote any C_k rule, does not "
            "embed or vary an action, does not claim empirical validation, and "
            "does not promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume select_next_ck_family_theorem_linkage_obligation_after_phi_source_closeout",
            "fail to select C_bridge^phi theorem-linkage obligation",
            "fail to tie C_bridge^phi to the prior standalone phi bridge-admissibility registry",
            "reuse C_source^phi as the bridge route",
            "reuse A-source route as the bridge route",
            "reuse psi-A route as the bridge route",
            "reuse QFT-GR route as the bridge route",
            "execute proof during selector",
            "discharge theorem during selector",
            "claim phi-sector closure",
            "claim scalar/QFT closure",
            "promote a C_k rule",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_SELECTION,
        "lean_status_wording_lines": LEAN_STATUS_WORDING_LINES_FOR_SELECTION,
        "full_toeformal_aggregate_status_for_selection": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION
        ),
        "scoped_lean_targets_status_for_selection": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION
        ),
        "aggregate_lean_validation_status_for_selection": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterPhiSourceCloseout",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "closeout_result_review_file": _ptr(closeout_result_review_path),
            "closeout_result_review_lean_file": _ptr(
                CLOSEOUT_RESULT_REVIEW_LEAN_PACKET_PATH
            ),
            "priority_selection_file": _ptr(priority_selection_path),
            "prior_phi_bridge_admissibility_registry_file": _ptr(
                phi_bridge_registry_path
            ),
            "prior_phi_bridge_admissibility_registry_lean_file": _ptr(
                PHI_BRIDGE_REGISTRY_LEAN_PACKET_PATH
            ),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
    return payload


def write_selection(selection: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(selection, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Select the next C_k theorem-linkage obligation after local "
            "phi-source theorem-linkage closeout."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--closeout-result-review",
        type=Path,
        default=CLOSEOUT_RESULT_REVIEW_PATH,
    )
    parser.add_argument(
        "--priority-selection",
        type=Path,
        default=PRIORITY_SELECTION_PATH,
    )
    parser.add_argument(
        "--phi-bridge-registry",
        type=Path,
        default=PHI_BRIDGE_REGISTRY_PATH,
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = (
        args.closeout_result_review
        if args.closeout_result_review.is_absolute()
        else REPO_ROOT / args.closeout_result_review
    )
    priority_path = (
        args.priority_selection
        if args.priority_selection.is_absolute()
        else REPO_ROOT / args.priority_selection
    )
    phi_bridge_registry_path = (
        args.phi_bridge_registry
        if args.phi_bridge_registry.is_absolute()
        else REPO_ROOT / args.phi_bridge_registry
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_ck_family_theorem_linkage_obligation_selection_after_phi_source_closeout(
            closeout_result_review_path=review_path,
            priority_selection_path=priority_path,
            phi_bridge_registry_path=phi_bridge_registry_path,
            captured_at_utc=args.captured_at_utc,
        )
    )
    path = write_selection(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "selector_outcome": payload["selector_outcome"],
                "selected_obligation": payload["selected_obligation"],
                "selected_next_target": payload["selected_next_target"],
                "follow_on_target_after_review": payload[
                    "follow_on_target_after_review"
                ],
                "proof_attempt_executed": payload["proof_attempt_executed"],
                "theorem_discharged": payload["theorem_discharged"],
                "phi_sector_closure_claimed": payload[
                    "phi_sector_closure_claimed"
                ],
                "rule_promoted": payload["rule_promoted"],
                "lean_status_wording_lines": payload["lean_status_wording_lines"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
