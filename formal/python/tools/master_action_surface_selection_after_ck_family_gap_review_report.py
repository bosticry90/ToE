from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.master_action_ck_family_gap_review_after_phi_a_and_psi_a_result_review_report import (
    BLOCKED_CLAIMS,
    C_BRIDGE_CLASSIFICATION,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CLASSIFICATION,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_SOURCE_CLASSIFICATION,
    C_TRANSPORT_CLASSIFICATION,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as GAP_REVIEW_RESULT_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAP_REVIEW_INSPECTION_QUESTIONS,
    LEAN_PACKET_PATH as GAP_REVIEW_RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as GAP_REVIEW_RESULT_REVIEW_OUTCOME,
    PACKET_ID as GAP_REVIEW_RESULT_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RECOMMENDED_SELECTOR_CHOICE,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as GAP_REVIEW_RESULT_REVIEW_SCHEMA_ID,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_GAP_REVIEW_20260626_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_GAP_REVIEW_v0"
SELECTION_RESULT = (
    "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_GAP_REVIEW_SELECTS_"
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "master_action_surface_selection_after_ck_family_gap_review_selects_"
    "ck_family_theorem_linkage_obligation_index_no_action_variation_or_"
    "master_action_promotion"
)

NEXT_TARGET = "review_master_action_surface_selection_after_ck_family_gap_review_result"
NEXT_TARGET_KIND = "master_action_surface_selection_after_ck_family_gap_review_result_review"

SELECTED_FOLLOW_ON_TARGET = "prepare_ck_family_theorem_linkage_obligation_index"
SELECTED_FOLLOW_ON_TARGET_KIND = "ck_family_theorem_linkage_obligation_index_preparation"
SELECTED_MASTER_ACTION_SURFACE = "ck_family_theorem_linkage_obligation_index"
SELECTED_SURFACE_LABEL = "C_k family theorem-linkage obligation index"
SELECTED_SURFACE_STATUS = "selected_pending_result_review"
SELECTED_SURFACE_EXECUTION_STATUS = "not_prepared"
SELECTED_SURFACE_REASON = (
    "The gap review left all C_k gaps open, so the next disciplined surface is "
    "an obligation index that separates theorem-linked rows from policy-linked "
    "or assumption-supplied rows before any stronger physics claim is allowed."
)

ALTERNATE_SELECTOR_CHOICES = [
    "return_to_QFT_GR_source_admissibility_lane",
    "prepare_ck_family_public_plain_language_status_packet",
    "select_next_interaction_surface_after_psi_A_u1",
]
SELECTOR_CHOICES = [SELECTED_FOLLOW_ON_TARGET, *ALTERNATE_SELECTOR_CHOICES]

PLANNED_OBLIGATION_ROW_IDS = [
    "C_source^phi",
    "C_bridge^phi",
    "C_transport^phi",
    "C_source^A",
    "C_bridge^A",
    "C_transport^A",
    "psi-A current route",
    "psi-A sourced gauge route",
    "psi-A gauge exchange",
    "psi-A matter exchange",
    "psi-A total conservation",
    "C_exchange^{Apsi}",
]

PLANNED_OBLIGATION_ROW_FIELDS = [
    "rule family",
    "field or interaction scope",
    "current evidence pointer",
    "theorem-linkage status",
    "supplied assumptions",
    "open proof debt",
    "functionalization blocker",
    "variation blocker",
    "seam-closure blocker",
    "next possible theorem slice",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_GAP_REVIEW_20260626_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionSurfaceSelectionAfterCKFamilyGapReview.lean"
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
        "rule_promoted": False,
        "obligation_index_prepared": False,
        "obligation_index_executed": False,
        "obligation_row_discharged": False,
        "theorem_linkage_obligation_index_prepared": False,
        "theorem_linkage_obligation_index_executed": False,
        "theorem_linkage_obligation_index_reviewed": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "return_to_qft_gr_source_admissibility_lane_selected": False,
        "public_plain_language_status_packet_prepared": False,
        "next_interaction_surface_selected": False,
        "immediate_new_field_or_interaction_expansion_selected": False,
    }


def _input_boundary_clear(review: dict[str, Any]) -> bool:
    return all(
        review.get(key) is False
        for key in _false_boundary_flags()
        if key in review
    )


def _planned_obligation_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for row_id in PLANNED_OBLIGATION_ROW_IDS:
        if row_id.endswith("^phi"):
            scope = "phi isolated-field C_k family"
        elif row_id.endswith("^A"):
            scope = "A isolated-field C_k family"
        else:
            scope = "psi-A interaction C_k family"
        rows.append(
            {
                "planned_row_id": row_id,
                "field_or_interaction_scope": scope,
                "planned_row_status": "planned_not_prepared",
                "theorem_linkage_status": "to_be_indexed",
                "supplied_assumptions": "to_be_indexed",
                "open_proof_debt": "to_be_indexed",
                "functionalization_blocker": "to_be_indexed",
                "variation_blocker": "to_be_indexed",
                "seam_closure_blocker": "to_be_indexed",
                "next_possible_theorem_slice": "to_be_indexed",
                "obligation_discharged": False,
            }
        )
    return rows


def _surface_options() -> list[dict[str, Any]]:
    return [
        {
            "surface_option_id": SELECTED_MASTER_ACTION_SURFACE,
            "surface_label": SELECTED_SURFACE_LABEL,
            "candidate_target_after_review": SELECTED_FOLLOW_ON_TARGET,
            "status": SELECTED_SURFACE_STATUS,
            "execution_status": SELECTED_SURFACE_EXECUTION_STATUS,
            "selection_reason": SELECTED_SURFACE_REASON,
            "theorem_linkage_obligation_index_selected": True,
            "theorem_linkage_obligation_index_prepared": False,
            "theorem_linkage_obligation_index_executed": False,
            "new_field_or_interaction_expansion_selected": False,
            "C_k_action_embedding_selected": False,
            "C_k_variation_selected": False,
            "master_action_promotion_selected": False,
        },
        {
            "surface_option_id": "return_to_QFT_GR_source_admissibility_lane",
            "status": "deferred_not_rejected",
            "execution_status": "not_executed",
            "selection_reason": (
                "Deferred until theorem-linkage obligations clarify which "
                "C_k rows can support harder seam work."
            ),
        },
        {
            "surface_option_id": "prepare_ck_family_public_plain_language_status_packet",
            "status": "deferred_not_rejected",
            "execution_status": "not_executed",
            "selection_reason": (
                "Deferred because the immediate scientific need is an obligation "
                "map rather than public compression."
            ),
        },
        {
            "surface_option_id": "select_next_interaction_surface_after_psi_A_u1",
            "status": "deferred_not_rejected",
            "execution_status": "not_executed",
            "selection_reason": (
                "Deferred to avoid expanding the interaction catalog before "
                "the existing interaction-family proof obligations are indexed."
            ),
        },
    ]


def _selection_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_consumes_gap_review_result_review_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The selector consumes the active post-gap-review target.",
        },
        {
            "row_id": "gap_review_result_review_accepted",
            "status": "accepted",
            "evidence": review.get("review_result"),
            "assessment": "The prior gap-review result review is accepted.",
        },
        {
            "row_id": "all_gaps_remain_open",
            "status": "accepted",
            "evidence": {
                "gap_count": review.get("gap_count"),
                "open_gap_count": review.get("open_gap_count"),
                "closed_gap_count": review.get("closed_gap_count"),
            },
            "assessment": "The selector follows an open-gap review; no gap is discharged.",
        },
        {
            "row_id": "recommendation_preserved",
            "status": "accepted",
            "evidence": review.get("recommended_selector_choice"),
            "assessment": "The theorem-linkage obligation index recommendation is preserved.",
        },
        {
            "row_id": "obligation_index_selected_not_prepared",
            "status": "accepted",
            "evidence": SELECTED_FOLLOW_ON_TARGET,
            "assessment": (
                "The theorem-linkage obligation index is selected as the follow-on "
                "surface, but it is not prepared in this selector."
            ),
        },
        {
            "row_id": "planned_obligation_rows_enumerated",
            "status": "accepted",
            "evidence": PLANNED_OBLIGATION_ROW_IDS,
            "assessment": "The expected obligation-index row set is recorded for the next packet.",
        },
        {
            "row_id": "planned_obligation_fields_enumerated",
            "status": "accepted",
            "evidence": PLANNED_OBLIGATION_ROW_FIELDS,
            "assessment": "The expected obligation-index fields are recorded for the next packet.",
        },
        {
            "row_id": "selector_result_review_first",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The immediate live target is the selector-result review.",
        },
        {
            "row_id": "no_action_variation_seam_empirical_or_promotion_claim",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "The selector preserves the bounded nonclaim boundary.",
        },
        {
            "row_id": "full_toeformal_aggregate_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full aggregate is preserved as NOT_RUN.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "master_action_surface_selection_after_ck_family_gap_review",
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


def build_master_action_surface_selection_after_ck_family_gap_review(
    *,
    review_path: Path = GAP_REVIEW_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    surface_options = _surface_options()
    planned_rows = _planned_obligation_rows()
    selection_criteria = _selection_criteria(review)
    acceptance_criteria = {
        "consumes_expected_gap_review_selector_target": (
            review.get("schema_id") == GAP_REVIEW_RESULT_REVIEW_SCHEMA_ID
            and review.get("packet_id") == GAP_REVIEW_RESULT_REVIEW_PACKET_ID
            and review.get("outcome_id") == GAP_REVIEW_RESULT_REVIEW_OUTCOME
            and review.get("review_result") == GAP_REVIEW_RESULT_REVIEW_OUTCOME
            and review.get("packet_result") == GAP_REVIEW_RESULT_REVIEW_OUTCOME
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "recommendation_preserved": (
            review.get("recommended_selector_choice") == SELECTED_FOLLOW_ON_TARGET
            and RECOMMENDED_SELECTOR_CHOICE == SELECTED_FOLLOW_ON_TARGET
        ),
        "all_gaps_remain_open": (
            review.get("gap_count") == 8
            and review.get("open_gap_count") == 8
            and review.get("closed_gap_count") == 0
            and review.get("no_gap_discharged") is True
            and review.get("no_gap_closed") is True
        ),
        "rule_architecture_context_preserved": (
            review.get("C_source_classification") == C_SOURCE_CLASSIFICATION
            and review.get("C_bridge_classification") == C_BRIDGE_CLASSIFICATION
            and review.get("C_transport_classification") == C_TRANSPORT_CLASSIFICATION
            and review.get("C_exchange_classification") == C_EXCHANGE_CLASSIFICATION
            and review.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "planned_obligation_rows_enumerated": len(planned_rows) == 12,
        "planned_obligation_fields_enumerated": len(PLANNED_OBLIGATION_ROW_FIELDS) == 10,
        "blocked_claims_enumerated": len(BLOCKED_CLAIMS) == 14,
        "exactly_one_surface_selected": (
            sum(1 for row in surface_options if row["status"] == SELECTED_SURFACE_STATUS)
            == 1
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
        else "REMEDIATE_MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_GAP_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_GAP_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_GAP_REVIEW_REQUIRES_REMEDIATION",
        "selection_result": OUTCOME_ID if accepted else "SELECTION_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID if accepted else "SELECTION_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_follow_on_target_after_review": SELECTED_FOLLOW_ON_TARGET,
        "selected_follow_on_target_kind": SELECTED_FOLLOW_ON_TARGET_KIND,
        "selected_post_review_target": SELECTED_FOLLOW_ON_TARGET,
        "selected_post_review_target_kind": SELECTED_FOLLOW_ON_TARGET_KIND,
        "gap_review_result_review_schema_id": GAP_REVIEW_RESULT_REVIEW_SCHEMA_ID,
        "gap_review_result_review_packet_id": GAP_REVIEW_RESULT_REVIEW_PACKET_ID,
        "gap_review_result_review_outcome": GAP_REVIEW_RESULT_REVIEW_OUTCOME,
        "gap_review_result_review_consumed": accepted,
        "selected_master_action_surface": SELECTED_MASTER_ACTION_SURFACE,
        "selected_surface_label": SELECTED_SURFACE_LABEL,
        "selected_surface_status": SELECTED_SURFACE_STATUS,
        "selected_surface_execution_status": SELECTED_SURFACE_EXECUTION_STATUS,
        "selected_surface_reason": SELECTED_SURFACE_REASON,
        "surface_options": surface_options,
        "surface_option_count": len(surface_options),
        "surface_options_selected_count": sum(
            1 for row in surface_options if row["status"] == SELECTED_SURFACE_STATUS
        ),
        "surface_options_deferred_count": sum(
            1 for row in surface_options if row["status"].startswith("deferred")
        ),
        "selector_choices": SELECTOR_CHOICES,
        "selector_choices_count": len(SELECTOR_CHOICES),
        "planned_obligation_row_ids": PLANNED_OBLIGATION_ROW_IDS,
        "planned_obligation_row_count": len(PLANNED_OBLIGATION_ROW_IDS),
        "planned_obligation_row_fields": PLANNED_OBLIGATION_ROW_FIELDS,
        "planned_obligation_row_field_count": len(PLANNED_OBLIGATION_ROW_FIELDS),
        "planned_obligation_rows": planned_rows,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "gap_review_inspection_questions": GAP_REVIEW_INSPECTION_QUESTIONS,
        "gap_review_inspection_question_count": len(GAP_REVIEW_INSPECTION_QUESTIONS),
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
        "master_action_surface_selector_executed": accepted,
        "master_action_surface_selection_executed": accepted,
        "next_master_action_surface_selected": accepted,
        "master_action_surface_selected": accepted,
        "selector_result_review_authorized": accepted,
        "selector_result_review_prepared": False,
        "selector_result_review_accepted": False,
        "theorem_linkage_obligation_index_selected": accepted,
        "theorem_linkage_obligation_index_authorized": accepted,
        "theorem_linkage_obligation_index_preparation_authorized_after_review": accepted,
        "theorem_linkage_obligation_index_prepared": False,
        "theorem_linkage_obligation_index_executed": False,
        "theorem_linkage_obligation_index_reviewed": False,
        "obligation_index_selected": accepted,
        "obligation_index_prepared": False,
        "obligation_index_executed": False,
        "obligation_rows_discharged": False,
        "gap_review_result_review_accepted": accepted,
        "gap_1_through_gap_8_indexed": accepted,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "no_rule_promoted": accepted,
        "no_C_k_functionalization_occurs": accepted,
        "no_C_k_variation_occurs": accepted,
        "no_seam_closure_occurs": accepted,
        "no_master_action_promotion_occurs": accepted,
        "gap_count": review.get("gap_count"),
        "open_gap_count": review.get("open_gap_count"),
        "closed_gap_count": review.get("closed_gap_count"),
        "new_physics_created": False,
        "new_field_or_interaction_expansion_selected": False,
        "immediate_new_field_or_interaction_expansion_selected": False,
        "return_to_qft_gr_source_admissibility_lane_selected": False,
        "public_plain_language_status_packet_prepared": False,
        "next_interaction_surface_selected": False,
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
            "The selector chooses a theorem-linkage obligation index as the "
            "next scientific surface, with a selector-result review first."
        ),
        "mathematical_statement": (
            "The selector does not discharge GAP-1 through GAP-8. It selects a "
            "follow-on index over C_source^phi, C_bridge^phi, C_transport^phi, "
            "C_source^A, C_bridge^A, C_transport^A, the psi-A current/source/"
            "exchange/total-conservation route, and C_exchange^{Apsi}. The "
            "index itself remains unprepared here."
        ),
        "non_claim_boundary": (
            "This selector selects the C_k family theorem-linkage obligation "
            "index as the follow-on surface after the C_k family gap review. It "
            "does not prepare the obligation index, discharge any gap, prove any "
            "row, promote any rule, embed C_k in an action, vary C_k, select a "
            "multiplier route, select a penalty route, make a direct dynamical-law "
            "claim, close any seam, claim empirical validation, or promote the "
            "master action. It records no Phase 2 authorization. The immediate "
            "live target is the selector-result review. The master action remains "
            "a working-form, noncanonical, non-promoted organizing surface. The "
            "full ToeFormal aggregate is kept as NOT_RUN."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume the post-gap-review selector target",
            "skip the selector-result review target",
            "fail to select the theorem-linkage obligation index as follow-on",
            "prepare the theorem-linkage obligation index inside this selector",
            "claim any indexed gap is discharged",
            "claim any indexed gap is closed",
            "promote any C_k rule",
            "claim any C_k family is action embedded",
            "authorize or execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "claim a direct dynamical-law interpretation",
            "claim full Maxwell closure",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "claim GR-QM closure",
            "derive the Standard Model",
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
            "ToeFormal.Derivation.MasterActionSurfaceSelectionAfterCKFamilyGapReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "gap_review_result_review_file": _ptr(review_path),
            "gap_review_result_review_lean_file": _ptr(
                GAP_REVIEW_RESULT_REVIEW_LEAN_PACKET_PATH
            ),
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
            "Select the next master-action surface after the CK-family gap review."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--review", type=Path, default=GAP_REVIEW_RESULT_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = args.review if args.review.is_absolute() else REPO_ROOT / args.review
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_master_action_surface_selection_after_ck_family_gap_review(
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
