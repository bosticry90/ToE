from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_theorem_linkage_obligation_index_result_review_report import (
    BLOCKED_CLAIMS,
    C_BRIDGE_CLASSIFICATION,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CLASSIFICATION,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_SOURCE_CLASSIFICATION,
    C_TRANSPORT_CLASSIFICATION,
    CONTROLLED_STATUS_LABELS,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as INDEX_RESULT_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as INDEX_RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OBLIGATION_ROW_FIELDS,
    OBLIGATION_ROW_IDS,
    OUTCOME_ID as INDEX_RESULT_REVIEW_OUTCOME,
    PACKET_ID as INDEX_RESULT_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RECOMMENDED_PRIORITY_ROW,
    RECOMMENDED_SELECTOR_CHOICE,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as INDEX_RESULT_REVIEW_SCHEMA_ID,
    SELECTOR_CANDIDATES,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_20260626_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_v0"
SELECTION_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_SELECTS_"
    "PRIORITY_SELECTION_PACKET_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "ck_family_theorem_linkage_obligation_selection_after_index_selects_"
    "priority_selection_packet_no_proof_execution_or_master_action_promotion"
)

NEXT_TARGET = "review_ck_family_theorem_linkage_obligation_selection_after_index_result"
NEXT_TARGET_KIND = "ck_family_theorem_linkage_obligation_selection_after_index_result_review"
SELECTED_FOLLOW_ON_TARGET = "prepare_ck_family_theorem_linkage_priority_selection_after_index"
SELECTED_FOLLOW_ON_TARGET_KIND = (
    "ck_family_theorem_linkage_priority_selection_after_index_preparation"
)

SELECTED_PACKET_LABEL = "C_k family theorem-linkage priority-selection packet"
SELECTED_PACKET_STATUS = "selected_pending_result_review"
SELECTED_PACKET_EXECUTION_STATUS = "not_prepared"
SELECTED_PACKET_REASON = (
    "The obligation index names proof debts, but the project must rank those "
    "obligations before authorizing a bounded theorem-linkage proof attempt."
)

LIKELY_PRIORITY_CANDIDATES = [
    "C_exchange theorem-linkage gap",
    "psi-A total-conservation theorem-linkage gap",
    "C_source^A theorem-linkage gap",
    "C_source^phi theorem-linkage gap",
]
LIKELY_FIRST_PRIORITY_CANDIDATE = "C_exchange theorem-linkage gap"
RECOMMENDED_FIRST_PRIORITY_ROW = RECOMMENDED_PRIORITY_ROW
SELECTED_PROOF_TARGET = "NONE_SELECTED"
SELECTED_THEOREM_ROW = "NONE_SELECTED"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_20260626_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CKFamilyTheoremLinkageObligationSelectionAfterIndex.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "C_k_action_embedding_claimed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_authorized": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "ck_action_embedding_claimed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "multiplier_route_selected": False,
        "multiplier_action_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_claimed": False,
        "direct_dynamical_law_interpretation_selected": False,
        "dynamical_law_claimed": False,
        "functional_action_embedding_claimed": False,
        "functionalization_authorized": False,
        "C_exchange_functional_embedding_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "full_em_closure_claimed": False,
        "em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "standard_model_derivation_claimed": False,
        "phase2_authorized": False,
        "phase2_readiness_claim": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "pillar_completion_inferred": False,
        "theorem_linkage_completed": False,
        "assumption_discharge_completed": False,
        "gap_review_closes_any_gap": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "rule_promoted": False,
        "obligation_row_discharged": False,
        "obligation_rows_discharged": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "proof_debt_target_selected": False,
        "proof_target_selected": False,
        "proof_target_execution_authorized": False,
        "proof_execution_authorized": False,
        "priority_selection_prepared": False,
        "priority_selection_executed": False,
        "priority_selection_packet_prepared": False,
        "priority_selection_packet_executed": False,
        "priority_row_selected": False,
        "theorem_row_selected": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "new_physics_created": False,
        "new_field_or_interaction_expansion_selected": False,
        "immediate_new_field_or_interaction_expansion_selected": False,
    }


def _input_boundary_clear(review: dict[str, Any]) -> bool:
    return all(
        review.get(key) is False
        for key in _false_boundary_flags()
        if key in review
    )


def _selection_options() -> list[dict[str, Any]]:
    return [
        {
            "option_id": SELECTED_FOLLOW_ON_TARGET,
            "option_label": SELECTED_PACKET_LABEL,
            "status": SELECTED_PACKET_STATUS,
            "execution_status": SELECTED_PACKET_EXECUTION_STATUS,
            "selection_reason": SELECTED_PACKET_REASON,
            "priority_selection_packet_selected": True,
            "priority_selection_packet_prepared": False,
            "proof_target_selected": False,
            "proof_execution_authorized": False,
            "master_action_promotion_selected": False,
        },
        {
            "option_id": "select_C_exchange_theorem_linkage_gap_for_proof",
            "status": "deferred_until_priority_selection_packet",
            "execution_status": "not_selected",
            "selection_reason": (
                "C_exchange is the likely first candidate, but proof-row "
                "selection is intentionally deferred to the priority-selection "
                "packet."
            ),
        },
        {
            "option_id": "select_psi_A_total_conservation_theorem_linkage_gap_for_proof",
            "status": "deferred_until_priority_selection_packet",
            "execution_status": "not_selected",
            "selection_reason": (
                "This row remains a plausible candidate, not a selected proof "
                "target in this selector."
            ),
        },
        {
            "option_id": "return_directly_to_QFT_GR_source_admissibility_lane",
            "status": "deferred_not_rejected",
            "execution_status": "not_selected",
            "selection_reason": (
                "Deferred until the priority-selection packet ranks the C_k "
                "theorem-linkage proof debts."
            ),
        },
    ]


def _selection_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_consumes_current_obligation_after_index_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The selector consumes the active post-index target.",
        },
        {
            "row_id": "index_result_review_accepted",
            "status": "accepted",
            "evidence": review.get("review_result"),
            "assessment": "The theorem-linkage obligation index result review is accepted.",
        },
        {
            "row_id": "priority_selection_packet_selected_only",
            "status": "accepted",
            "evidence": SELECTED_FOLLOW_ON_TARGET,
            "assessment": "Only the priority-selection packet is selected.",
        },
        {
            "row_id": "no_theorem_row_selected",
            "status": "accepted",
            "evidence": {
                "selected_proof_target": SELECTED_PROOF_TARGET,
                "selected_theorem_row": SELECTED_THEOREM_ROW,
            },
            "assessment": "No theorem row is selected for proof execution.",
        },
        {
            "row_id": "likely_candidates_recorded",
            "status": "accepted",
            "evidence": LIKELY_PRIORITY_CANDIDATES,
            "assessment": "Likely candidates are recorded for the next packet to rank.",
        },
        {
            "row_id": "obligation_rows_remain_indexed_only",
            "status": "accepted",
            "evidence": OBLIGATION_ROW_IDS,
            "assessment": "The 13 obligation rows remain indexed only.",
        },
        {
            "row_id": "no_gap_discharge",
            "status": "accepted",
            "evidence": {
                "gap_count": review.get("gap_count"),
                "open_gap_count": review.get("open_gap_count"),
                "closed_gap_count": review.get("closed_gap_count"),
            },
            "assessment": "GAP-1 through GAP-8 remain open.",
        },
        {
            "row_id": "no_proof_execution_or_rule_promotion",
            "status": "accepted",
            "evidence": [
                "proof_execution_authorized=false",
                "proof_attempt_executed=false",
                "rule_promoted=false",
            ],
            "assessment": "No proof execution or C_k rule promotion is selected.",
        },
        {
            "row_id": "no_action_seam_empirical_or_master_action_promotion",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "The selector preserves the bounded nonclaim boundary.",
        },
        {
            "row_id": "selector_result_review_first",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The immediate target is the selector-result review.",
        },
        {
            "row_id": "full_toeformal_aggregate_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full ToeFormal aggregate is preserved as NOT_RUN.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "ck_family_theorem_linkage_obligation_selection_after_index",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "aggregate_lean_validation_status_allowed_values": ["NOT_RUN"],
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_ck_family_theorem_linkage_obligation_selection_after_index(
    *,
    review_path: Path = INDEX_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    selection_options = _selection_options()
    selection_criteria = _selection_criteria(review)
    acceptance_criteria = {
        "consumes_expected_current_selector_target": (
            review.get("schema_id") == INDEX_RESULT_REVIEW_SCHEMA_ID
            and review.get("packet_id") == INDEX_RESULT_REVIEW_PACKET_ID
            and review.get("outcome_id") == INDEX_RESULT_REVIEW_OUTCOME
            and review.get("review_result") == INDEX_RESULT_REVIEW_OUTCOME
            and review.get("packet_result") == INDEX_RESULT_REVIEW_OUTCOME
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and review.get("accepted") is True
        ),
        "priority_selection_packet_recommendation_preserved": (
            review.get("recommended_selector_choice") == SELECTED_FOLLOW_ON_TARGET
            and RECOMMENDED_SELECTOR_CHOICE == SELECTED_FOLLOW_ON_TARGET
        ),
        "obligation_rows_remain_indexed": (
            review.get("proof_obligation_row_ids") == OBLIGATION_ROW_IDS
            and review.get("proof_obligation_row_count") == 13
            and review.get("obligation_row_fields") == OBLIGATION_ROW_FIELDS
            and review.get("obligation_row_field_count") == 10
        ),
        "controlled_statuses_preserved": (
            review.get("controlled_status_labels") == CONTROLLED_STATUS_LABELS
            and review.get("controlled_status_label_count") == 7
        ),
        "priority_candidates_preserved": (
            review.get("selector_candidates") == SELECTOR_CANDIDATES
            and LIKELY_PRIORITY_CANDIDATES == SELECTOR_CANDIDATES
            and review.get("recommended_priority_row") == RECOMMENDED_PRIORITY_ROW
        ),
        "all_gaps_remain_open": (
            review.get("gap_count") == 8
            and review.get("open_gap_count") == 8
            and review.get("closed_gap_count") == 0
            and review.get("no_gap_discharged") is True
            and review.get("no_gap_closed") is True
        ),
        "no_proof_target_selected": (
            SELECTED_PROOF_TARGET == "NONE_SELECTED"
            and SELECTED_THEOREM_ROW == "NONE_SELECTED"
            and review.get("proof_debt_target_selected") is False
            and review.get("proof_execution_authorized") is False
        ),
        "exactly_one_packet_selected": (
            sum(1 for row in selection_options if row["status"] == SELECTED_PACKET_STATUS)
            == 1
        ),
        "rule_architecture_context_preserved": (
            review.get("C_source_classification") == C_SOURCE_CLASSIFICATION
            and review.get("C_bridge_classification") == C_BRIDGE_CLASSIFICATION
            and review.get("C_transport_classification") == C_TRANSPORT_CLASSIFICATION
            and review.get("C_exchange_classification") == C_EXCHANGE_CLASSIFICATION
            and review.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "no_input_forbidden_claims": _input_boundary_clear(review),
        "selection_criteria_all_accepted": all(
            row["status"] == "accepted" for row in selection_criteria
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            review.get("aggregate_lean_validation_status_for_review")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and review.get("full_toeformal_aggregate_status_for_review")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and review.get("full_toeformal_aggregate_passed") is False
            and review.get("full_toeformal_aggregate_failed") is False
            and review.get("full_toeformal_aggregate_timed_out") is False
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_REQUIRES_REMEDIATION",
        "selection_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_follow_on_target_after_review": SELECTED_FOLLOW_ON_TARGET,
        "selected_follow_on_target_kind": SELECTED_FOLLOW_ON_TARGET_KIND,
        "selected_post_review_target": SELECTED_FOLLOW_ON_TARGET,
        "selected_post_review_target_kind": SELECTED_FOLLOW_ON_TARGET_KIND,
        "selected_packet_label": SELECTED_PACKET_LABEL,
        "selected_packet_status": SELECTED_PACKET_STATUS,
        "selected_packet_execution_status": SELECTED_PACKET_EXECUTION_STATUS,
        "selected_packet_reason": SELECTED_PACKET_REASON,
        "index_result_review_schema_id": INDEX_RESULT_REVIEW_SCHEMA_ID,
        "index_result_review_packet_id": INDEX_RESULT_REVIEW_PACKET_ID,
        "index_result_review_outcome": INDEX_RESULT_REVIEW_OUTCOME,
        "index_result_review_consumed": accepted,
        "selection_options": selection_options,
        "selection_option_count": len(selection_options),
        "selection_options_selected_count": sum(
            1 for row in selection_options if row["status"] == SELECTED_PACKET_STATUS
        ),
        "selection_options_deferred_count": sum(
            1 for row in selection_options if row["status"].startswith("deferred")
        ),
        "likely_priority_candidates": LIKELY_PRIORITY_CANDIDATES,
        "likely_priority_candidate_count": len(LIKELY_PRIORITY_CANDIDATES),
        "likely_first_priority_candidate": LIKELY_FIRST_PRIORITY_CANDIDATE,
        "recommended_first_priority_row": RECOMMENDED_FIRST_PRIORITY_ROW,
        "recommended_selector_choice": RECOMMENDED_SELECTOR_CHOICE,
        "selected_proof_target": SELECTED_PROOF_TARGET,
        "selected_theorem_row": SELECTED_THEOREM_ROW,
        "proof_obligation_row_ids": OBLIGATION_ROW_IDS,
        "proof_obligation_row_count": len(OBLIGATION_ROW_IDS),
        "obligation_row_fields": OBLIGATION_ROW_FIELDS,
        "obligation_row_field_count": len(OBLIGATION_ROW_FIELDS),
        "controlled_status_labels": CONTROLLED_STATUS_LABELS,
        "controlled_status_label_count": len(CONTROLLED_STATUS_LABELS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "selection_criteria": selection_criteria,
        "selection_criteria_count": len(selection_criteria),
        "selection_criteria_accepted_count": sum(
            1 for row in selection_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "selector_target_prepared": accepted,
        "selector_target_accepted": accepted,
        "selection_executed": accepted,
        "obligation_after_index_selector_executed": accepted,
        "priority_selection_packet_selected": accepted,
        "priority_selection_packet_authorized_after_review": accepted,
        "priority_selection_packet_prepared": False,
        "priority_selection_packet_executed": False,
        "priority_selection_prepared": False,
        "priority_selection_executed": False,
        "selector_result_review_authorized": accepted,
        "selector_result_review_prepared": False,
        "selector_result_review_accepted": False,
        "theorem_linkage_obligation_index_reviewed": accepted,
        "obligation_index_reviewed": accepted,
        "proof_obligation_rows_indexed": accepted,
        "row_index_only": accepted,
        "proof_debt_target_selected": False,
        "proof_target_selected": False,
        "priority_row_selected": False,
        "theorem_row_selected": False,
        "proof_execution_authorized": False,
        "proof_target_execution_authorized": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "obligation_rows_discharged": False,
        "obligation_row_discharged": False,
        "gap_1_through_gap_8_indexed": accepted,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "no_rule_promoted": accepted,
        "no_C_k_functionalization_occurs": accepted,
        "no_C_k_variation_occurs": accepted,
        "no_seam_closure_occurs": accepted,
        "no_master_action_promotion_occurs": accepted,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "new_physics_created": False,
        "new_field_or_interaction_expansion_selected": False,
        "immediate_new_field_or_interaction_expansion_selected": False,
        "all_C_k_families_admissibility_only": accepted,
        "all_summarized_rules_admissibility_only": accepted,
        "all_summarized_rules_not_action_embedded": accepted,
        "all_summarized_rules_not_varied": accepted,
        "all_summarized_rules_not_direct_dynamical_laws": accepted,
        "all_summarized_rules_not_empirical_claims": accepted,
        "C_source_classification": C_SOURCE_CLASSIFICATION,
        "C_bridge_classification": C_BRIDGE_CLASSIFICATION,
        "C_transport_classification": C_TRANSPORT_CLASSIFICATION,
        "C_exchange_classification": C_EXCHANGE_CLASSIFICATION,
        "current_candidate": CURRENT_CANDIDATE,
        "current_conservation_result": CURRENT_CONSERVATION_RESULT,
        "sourced_gauge_route": SOURCED_GAUGE_ROUTE,
        "gauge_sector_exchange_identity": GAUGE_SECTOR_EXCHANGE_IDENTITY,
        "matter_sector_exchange_identity": MATTER_SECTOR_EXCHANGE_IDENTITY,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_constraint_form": C_EXCHANGE_CONSTRAINT_FORM,
        "C_exchange_admissibility_condition": C_EXCHANGE_ADMISSIBILITY_CONDITION,
        "plain_meaning": (
            "The selector chooses a priority-selection packet as the next "
            "follow-on step. It does not choose or execute a theorem proof."
        ),
        "mathematical_statement": (
            "The selector preserves the 13 indexed C_k proof obligations and "
            "authorizes only a ranking packet after result review. No theorem "
            "row is selected, no proof execution is authorized, and no C_k rule "
            "is promoted."
        ),
        "non_claim_boundary": (
            "This selector selects only the C_k family theorem-linkage "
            "priority-selection packet as the follow-on target. It does not "
            "prepare that packet, select a theorem row for proof execution, "
            "execute any proof target, discharge GAP-1 through GAP-8, promote "
            "any C_k rule, embed C_k in an action, vary C_k, select a multiplier "
            "route, select a penalty route, make a direct dynamical-law claim, "
            "close EM-QFT, close QFT-GR, close GR-QM, claim empirical validation, "
            "or promote the master action. The master action remains a "
            "working-form, noncanonical, non-promoted organizing surface. The "
            "full ToeFormal aggregate is kept as NOT_RUN."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume select_next_ck_family_theorem_linkage_obligation_after_index",
            "fail to select prepare_ck_family_theorem_linkage_priority_selection_after_index",
            "select a theorem row for proof execution",
            "authorize proof target execution",
            "prepare the priority-selection packet inside this selector",
            "discharge any GAP-1 through GAP-8 item",
            "promote any C_k rule",
            "claim any C_k family is action embedded",
            "authorize or execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "claim a direct dynamical-law interpretation",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "claim GR-QM closure",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterIndex",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "index_result_review_file": _ptr(review_path),
            "index_result_review_lean_file": _ptr(INDEX_RESULT_REVIEW_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }
    payload.update(_false_boundary_flags())
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
            "Select the priority-selection packet after the C_k theorem-linkage "
            "obligation index."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--review", type=Path, default=INDEX_RESULT_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = args.review if args.review.is_absolute() else REPO_ROOT / args.review
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_ck_family_theorem_linkage_obligation_selection_after_index(
        review_path=review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_selection(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "selection_result": payload["selection_result"],
                "selected_follow_on_target_after_review": payload[
                    "selected_follow_on_target_after_review"
                ],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
