from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_theorem_linkage_priority_selection_after_index_report import (
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
    DEFAULT_OUT as PRIORITY_SELECTION_PATH,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as PRIORITY_SELECTION_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OBLIGATION_ROW_FIELDS,
    OBLIGATION_ROW_IDS,
    OUTCOME_ID as PRIORITY_SELECTION_OUTCOME,
    PACKET_ID as PRIORITY_SELECTION_PACKET_ID,
    PRIORITY_CRITERIA,
    QFTGR_AGGREGATE_PATH,
    RANKED_ROW_IDS,
    RECOMMENDED_POST_REVIEW_TARGET,
    RECOMMENDED_POST_REVIEW_TARGET_KIND,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as PRIORITY_SELECTION_SCHEMA_ID,
    SELECTED_PROOF_TARGET,
    SELECTED_THEOREM_ROW,
    SOURCED_GAUGE_ROUTE,
    TOP_FIVE_PRIORITY_THEMES,
    TOP_OBLIGATION_CANDIDATE,
    TOP_OBLIGATION_NEXT_SLICE,
    TOP_OBLIGATION_ROW_ID,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-27T00:00:00Z"

SCHEMA_ID = (
    "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_RESULT_REVIEW_"
    "20260627_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_RESULT_REVIEW_"
    "ACCEPTS_PRIORITY_RANKING_AND_TOP_CEXCHANGE_CANDIDATE_NO_PROOF_EXECUTION_"
    "OR_MASTER_ACTION_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_RESULT_REVIEW_"
    "ACCEPTS_RANKING_ONLY_NO_THEOREM_DISCHARGE_OR_CK_RULE_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "ck_family_theorem_linkage_priority_selection_after_index_result_review_"
    "accepts_priority_ranking_and_top_cexchange_candidate_no_proof_execution_"
    "or_master_action_promotion"
)

NEXT_TARGET = RECOMMENDED_POST_REVIEW_TARGET
NEXT_TARGET_KIND = RECOMMENDED_POST_REVIEW_TARGET_KIND
TOP_OBLIGATION_PACKET_SCOPE = "C_exchange^{Apsi} theorem-linkage gap"
TOP_OBLIGATION_PACKET_PLAIN_MEANING = (
    "The next work item asks what exact theorem would make C_exchange more "
    "than an admissibility-only record."
)
SELECTED_PROOF_TARGET = "NONE_SELECTED"
SELECTED_THEOREM_ROW = "NONE_SELECTED"

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = "PASSED_SERIAL_RERUN"
LEAN_STATUS_WORDING = (
    "full ToeFormal aggregate = "
    f"{FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW}; scoped Lean targets = "
    f"{SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW}"
)

ACCEPTED_REVIEW_FINDINGS = [
    "13 obligation rows ranked",
    "C_exchange selected as top candidate",
    "post-review target preserved as prepare_ck_family_top_theorem_linkage_obligation_packet",
    "no proof execution",
    "no theorem discharge",
    "no GAP-1 through GAP-8 discharge",
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k variation",
    "no seam closure",
    "no empirical validation",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_RESULT_REVIEW_"
        "20260627_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CKFamilyTheoremLinkagePrioritySelectionAfterIndexResultReview.lean"
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


def _input_boundary_clear(priority: dict[str, Any]) -> bool:
    return all(
        priority.get(key) is False
        for key in _false_boundary_flags()
        if key in priority
    )


def _review_criteria(priority: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "priority_selection_packet_consumed",
            "status": "accepted",
            "evidence": priority.get("priority_selection_result"),
            "assessment": "The priority-selection packet is consumed by review.",
        },
        {
            "row_id": "thirteen_rows_ranked",
            "status": "accepted",
            "evidence": priority.get("ranked_row_ids"),
            "assessment": "All 13 indexed theorem-linkage rows were ranked.",
        },
        {
            "row_id": "top_cexchange_candidate_accepted",
            "status": "accepted",
            "evidence": {
                "top_obligation_candidate": priority.get("top_obligation_candidate"),
                "top_obligation_row_id": priority.get("top_obligation_row_id"),
            },
            "assessment": "C_exchange is accepted as the top obligation candidate.",
        },
        {
            "row_id": "post_review_target_preserved",
            "status": "accepted",
            "evidence": priority.get("recommended_post_review_target"),
            "assessment": "The top-obligation packet remains the post-review target.",
        },
        {
            "row_id": "top_packet_scope_bounded",
            "status": "accepted",
            "evidence": TOP_OBLIGATION_PACKET_SCOPE,
            "assessment": "The next packet is scoped to the C_exchange theorem-linkage gap.",
        },
        {
            "row_id": "no_proof_execution_or_theorem_discharge",
            "status": "accepted",
            "evidence": {
                "selected_proof_target": priority.get("selected_proof_target"),
                "selected_theorem_row": priority.get("selected_theorem_row"),
                "proof_attempt_executed": priority.get("proof_attempt_executed"),
            },
            "assessment": "The review accepts no proof execution or theorem discharge.",
        },
        {
            "row_id": "no_gap_discharge",
            "status": "accepted",
            "evidence": {
                "gap_count": priority.get("gap_count"),
                "open_gap_count": priority.get("open_gap_count"),
                "closed_gap_count": priority.get("closed_gap_count"),
            },
            "assessment": "GAP-1 through GAP-8 remain open.",
        },
        {
            "row_id": "no_ck_rule_promotion_or_action_route",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "No C_k rule promotion, action embedding, or variation is accepted.",
        },
        {
            "row_id": "claim_ladder_boundary_preserved",
            "status": "accepted",
            "evidence": [
                "below seam closure",
                "below empirical prediction",
                "below empirical confirmation",
                "below mature physical theory",
            ],
            "assessment": "The claim-ladder boundary remains below closure and validation.",
        },
        {
            "row_id": "lean_status_wording_preserved",
            "status": "accepted",
            "evidence": LEAN_STATUS_WORDING,
            "assessment": "The review does not claim the full aggregate passed.",
        },
        {
            "row_id": "review_rotates_to_top_obligation_packet",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The review rotates to the top-obligation packet preparation.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "ck_family_theorem_linkage_priority_selection_after_index_result_review"
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
        "aggregate_lean_validation_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "full_toeformal_aggregate_status_for_review": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_review": SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_ck_family_theorem_linkage_priority_selection_after_index_result_review(
    *,
    priority_path: Path = PRIORITY_SELECTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    priority = _read_json(priority_path)
    review_criteria = _review_criteria(priority)
    acceptance_criteria = {
        "consumes_expected_priority_selection_review_target": (
            priority.get("schema_id") == PRIORITY_SELECTION_SCHEMA_ID
            and priority.get("packet_id") == PRIORITY_SELECTION_PACKET_ID
            and priority.get("outcome_id") == PRIORITY_SELECTION_OUTCOME
            and priority.get("priority_selection_result") == PRIORITY_SELECTION_OUTCOME
            and priority.get("selected_next_target") == CONSUMED_TARGET
            and priority.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and priority.get("accepted") is True
        ),
        "ranking_accepted": (
            priority.get("ranked_row_ids") == RANKED_ROW_IDS
            and priority.get("ranked_row_count") == 13
            and priority.get("priority_ranking_count") == 13
            and priority.get("priority_criteria") == PRIORITY_CRITERIA
        ),
        "top_cexchange_candidate_accepted": (
            priority.get("top_obligation_candidate") == TOP_OBLIGATION_CANDIDATE
            and priority.get("top_obligation_row_id") == TOP_OBLIGATION_ROW_ID
            and priority.get("top_obligation_candidate_selected") is True
            and priority.get("ranking_selects_top_obligation_candidate") is True
        ),
        "post_review_target_preserved": (
            priority.get("recommended_post_review_target") == NEXT_TARGET
            and priority.get("recommended_post_review_target_kind") == NEXT_TARGET_KIND
        ),
        "indexed_rows_preserved": (
            priority.get("proof_obligation_row_ids") == OBLIGATION_ROW_IDS
            and priority.get("proof_obligation_row_count") == 13
            and priority.get("obligation_row_fields") == OBLIGATION_ROW_FIELDS
            and priority.get("obligation_row_field_count") == 10
        ),
        "top_five_themes_preserved": (
            priority.get("top_five_priority_themes") == TOP_FIVE_PRIORITY_THEMES
            and priority.get("top_five_priority_theme_count") == 5
        ),
        "no_proof_execution_or_theorem_discharge": (
            priority.get("selected_proof_target") == SELECTED_PROOF_TARGET
            and priority.get("selected_theorem_row") == SELECTED_THEOREM_ROW
            and priority.get("proof_attempt_executed") is False
            and priority.get("theorem_row_selected") is False
            and priority.get("proof_execution_authorized") is False
        ),
        "all_gaps_remain_open": (
            priority.get("gap_count") == 8
            and priority.get("open_gap_count") == 8
            and priority.get("closed_gap_count") == 0
            and priority.get("no_gap_discharged") is True
            and priority.get("no_gap_closed") is True
        ),
        "rule_architecture_context_preserved": (
            priority.get("C_source_classification") == C_SOURCE_CLASSIFICATION
            and priority.get("C_bridge_classification") == C_BRIDGE_CLASSIFICATION
            and priority.get("C_transport_classification") == C_TRANSPORT_CLASSIFICATION
            and priority.get("C_exchange_classification") == C_EXCHANGE_CLASSIFICATION
            and priority.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "no_input_forbidden_claims": _input_boundary_clear(priority),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
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
        else "REMEDIATE_CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_"
            "RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "post_review_target": NEXT_TARGET,
        "post_review_target_kind": NEXT_TARGET_KIND,
        "priority_selection_schema_id": PRIORITY_SELECTION_SCHEMA_ID,
        "priority_selection_packet_id": PRIORITY_SELECTION_PACKET_ID,
        "priority_selection_outcome": PRIORITY_SELECTION_OUTCOME,
        "priority_selection_consumed": accepted,
        "priority_ranking_accepted": accepted,
        "priority_criteria": PRIORITY_CRITERIA,
        "priority_criterion_count": len(PRIORITY_CRITERIA),
        "ranked_row_ids": RANKED_ROW_IDS,
        "ranked_row_count": len(RANKED_ROW_IDS),
        "priority_ranking_count": len(RANKED_ROW_IDS),
        "top_five_priority_themes": TOP_FIVE_PRIORITY_THEMES,
        "top_five_priority_theme_count": len(TOP_FIVE_PRIORITY_THEMES),
        "top_obligation_candidate": TOP_OBLIGATION_CANDIDATE,
        "top_obligation_row_id": TOP_OBLIGATION_ROW_ID,
        "top_obligation_next_possible_theorem_slice": TOP_OBLIGATION_NEXT_SLICE,
        "top_obligation_candidate_selected": accepted,
        "top_obligation_packet_scope": TOP_OBLIGATION_PACKET_SCOPE,
        "top_obligation_packet_plain_meaning": TOP_OBLIGATION_PACKET_PLAIN_MEANING,
        "top_obligation_packet_preparation_authorized": accepted,
        "selected_proof_target": SELECTED_PROOF_TARGET,
        "selected_theorem_row": SELECTED_THEOREM_ROW,
        "proof_obligation_row_ids": OBLIGATION_ROW_IDS,
        "proof_obligation_row_count": len(OBLIGATION_ROW_IDS),
        "obligation_row_fields": OBLIGATION_ROW_FIELDS,
        "obligation_row_field_count": len(OBLIGATION_ROW_FIELDS),
        "controlled_status_labels": CONTROLLED_STATUS_LABELS,
        "controlled_status_label_count": len(CONTROLLED_STATUS_LABELS),
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": accepted,
        "priority_selection_packet_reviewed": accepted,
        "priority_selection_packet_prepared": accepted,
        "priority_selection_prepared": accepted,
        "priority_selection_executed": accepted,
        "priority_rows_ranked": accepted,
        "priority_row_selected": accepted,
        "ranking_only_review": accepted,
        "theorem_linkage_obligation_index_reviewed": accepted,
        "obligation_index_reviewed": accepted,
        "proof_obligation_rows_indexed": accepted,
        "proof_debt_target_selected": False,
        "proof_target_selected": False,
        "theorem_row_selected": False,
        "proof_execution_authorized": False,
        "proof_target_execution_authorized": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "theorem_linkage_completed": False,
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
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
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
            "The review accepts the ranking only. The next work item should ask "
            "what exact theorem would make C_exchange more than an "
            "admissibility-only record."
        ),
        "mathematical_statement": (
            "The result review accepts the priority ranking of 13 indexed C_k "
            "theorem-linkage obligations, accepts C_exchange^{Apsi} as the top "
            "obligation candidate, and rotates to a bounded top-obligation "
            "packet. It records no proof execution, theorem discharge, gap "
            "discharge, C_k rule promotion, action embedding, variation, seam "
            "closure, empirical validation, or master-action promotion."
        ),
        "non_claim_boundary": (
            "This priority-selection result review accepts only that 13 "
            "obligation rows were ranked and that C_exchange is the top "
            "candidate for a future theorem-linkage obligation packet. It does "
            "not execute any proof, discharge any theorem row, discharge GAP-1 "
            "through GAP-8, promote any C_k rule, embed C_k in an action, vary "
            "C_k, select a multiplier route, select a penalty route, make a "
            "direct dynamical-law claim, close any seam, claim empirical "
            "prediction or validation, or promote the master action. The next "
            "packet remains below seam closure, empirical prediction, empirical "
            "confirmation, and mature physical theory. The master action "
            "remains a working-form, noncanonical organizing surface, not a "
            "promoted final law."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_ck_family_theorem_linkage_priority_selection_after_index_result",
            "fail to accept all 13 ranked rows",
            "fail to preserve C_exchange as the top candidate",
            "fail to rotate to prepare_ck_family_top_theorem_linkage_obligation_packet",
            "treat result review as theorem discharge",
            "select a proof target for execution",
            "authorize proof target execution",
            "discharge any GAP-1 through GAP-8 item",
            "promote any C_k rule",
            "claim any C_k family is action embedded",
            "authorize or execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "claim a direct dynamical-law interpretation",
            "claim seam closure",
            "claim empirical prediction or validation",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING,
        "full_toeformal_aggregate_status_for_review": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_review": SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
        "aggregate_lean_validation_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.CKFamilyTheoremLinkagePrioritySelectionAfterIndexResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "priority_selection_file": _ptr(priority_path),
            "priority_selection_lean_file": _ptr(PRIORITY_SELECTION_LEAN_PACKET_PATH),
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


def write_result_review(review: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(review, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Review the C_k family theorem-linkage priority-selection result."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--priority", type=Path, default=PRIORITY_SELECTION_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    priority_path = (
        args.priority if args.priority.is_absolute() else REPO_ROOT / args.priority
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_ck_family_theorem_linkage_priority_selection_after_index_result_review(
        priority_path=priority_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_result_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
                "selected_next_target": payload["selected_next_target"],
                "top_obligation_packet_scope": payload["top_obligation_packet_scope"],
                "lean_status_wording": payload["lean_status_wording"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
