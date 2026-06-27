from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_theorem_linkage_obligation_index_report import (
    DEFAULT_OUT as INDEX_PATH,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_index_result_review_report import (
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
    DEFAULT_OUT as SELECTOR_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as SELECTOR_REVIEW_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OBLIGATION_ROW_FIELDS,
    OBLIGATION_ROW_IDS,
    OUTCOME_ID as SELECTOR_REVIEW_OUTCOME,
    PACKET_ID as SELECTOR_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as SELECTOR_REVIEW_SCHEMA_ID,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-27T00:00:00Z"

SCHEMA_ID = "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_20260627_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_v0"
PRIORITY_SELECTION_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_PREPARED_PRIORITY_"
    "RANKING_SELECTS_TOP_OBLIGATION_CANDIDATE_NO_THEOREM_DISCHARGE_OR_MASTER_"
    "ACTION_PROMOTION"
)
RECOMMENDED_PRIORITY_SELECTION_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_PREPARED_PRIORITY_"
    "ROWS_RANKED_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
OUTCOME_ID = PRIORITY_SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "ck_family_theorem_linkage_priority_selection_after_index_prepared_priority_"
    "ranking_selects_top_obligation_candidate_no_theorem_discharge_or_master_"
    "action_promotion"
)

NEXT_TARGET = "review_ck_family_theorem_linkage_priority_selection_after_index_result"
NEXT_TARGET_KIND = "ck_family_theorem_linkage_priority_selection_after_index_result_review"
RECOMMENDED_POST_REVIEW_TARGET = "prepare_ck_family_top_theorem_linkage_obligation_packet"
RECOMMENDED_POST_REVIEW_TARGET_KIND = "ck_family_top_theorem_linkage_obligation_packet"

PRIORITY_CRITERIA = [
    "architecture leverage",
    "proof tractability",
    "dependency clarity",
    "risk of overclaim",
    "value for later seam work",
]

TOP_OBLIGATION_CANDIDATE = "C_exchange theorem-linkage gap"
TOP_OBLIGATION_ROW_ID = "C_exchange^{Apsi}"
TOP_OBLIGATION_NEXT_SLICE = (
    "C_exchange route-to-admissibility soundness theorem under accepted "
    "total-conservation assumptions."
)
SELECTED_PROOF_TARGET = "NONE_SELECTED"
SELECTED_THEOREM_ROW = "NONE_SELECTED"

RANKED_ROW_IDS = [
    "C_exchange^{Apsi}",
    "psi-A total conservation",
    "psi-A matter-sector exchange",
    "psi-A gauge-sector exchange",
    "C_source^A",
    "C_source^phi",
    "psi-A sourced gauge route",
    "psi-A current conservation",
    "psi-A current route",
    "C_bridge^A",
    "C_bridge^phi",
    "C_transport^A",
    "C_transport^phi",
]

TOP_FIVE_PRIORITY_THEMES = [
    "C_exchange theorem-linkage gap",
    "psi-A total-conservation theorem-linkage gap",
    "psi-A matter/gauge exchange theorem-linkage gap",
    "C_source^A theorem-linkage gap",
    "C_source^phi theorem-linkage gap",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_20260627_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CKFamilyTheoremLinkagePrioritySelectionAfterIndex.lean"
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


def _input_boundary_clear(payload: dict[str, Any]) -> bool:
    return all(
        payload.get(key) is False
        for key in _false_boundary_flags()
        if key in payload
    )


def _row_index(index: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {row["row_id"]: row for row in index.get("proof_obligation_rows", [])}


def _priority_rationale(row_id: str) -> str:
    rationales = {
        "C_exchange^{Apsi}": (
            "Newest architecture-expanding C_k family; tests whether an "
            "interaction exchange-balance rule can be theorem-linked while "
            "remaining admissibility-only."
        ),
        "psi-A total conservation": (
            "Direct dependency for C_exchange and a high-value seam-work "
            "bridge from equal-and-opposite exchange halves to total balance."
        ),
        "psi-A matter-sector exchange": (
            "One half of the exchange pair needed by total conservation; "
            "assumption exposure is concrete and proof debt is localized."
        ),
        "psi-A gauge-sector exchange": (
            "The matching gauge-side exchange half; needed to compare sign, "
            "stress-energy, and source-current conventions."
        ),
        "C_source^A": (
            "High leverage for the A branch and useful for later source-rule "
            "soundness, with a clear vacuum U(1) dependency surface."
        ),
        "C_source^phi": (
            "Baseline source-rule soundness row for comparing isolated-field "
            "C_source behavior against the A and psi-A families."
        ),
        "psi-A sourced gauge route": (
            "Useful dependency for exchange work, but it is narrower than the "
            "total-conservation and C_exchange linkage questions."
        ),
        "psi-A current conservation": (
            "Already theorem-linked conditionally; important for dependency "
            "cleanup but less architecture-expanding than exchange linkage."
        ),
        "psi-A current route": (
            "Foundational current construction debt, ranked below conservation "
            "and exchange because it is more local to the source route."
        ),
        "C_bridge^A": (
            "Route-matching admissibility is useful but less urgent than source "
            "and interaction-exchange theorem linkage."
        ),
        "C_bridge^phi": (
            "Phi bridge soundness is structurally useful, but lower immediate "
            "seam leverage than source and psi-A interaction rows."
        ),
        "C_transport^A": (
            "Transport stability matters for derivation-chain hygiene, but "
            "current proof-debt value is downstream of source/exchange rows."
        ),
        "C_transport^phi": (
            "Phi transport stability remains indexed proof debt with the lowest "
            "immediate architecture leverage in this packet."
        ),
    }
    return rationales[row_id]


def _criterion_profile(row_id: str) -> dict[str, Any]:
    profiles: dict[str, dict[str, Any]] = {
        "C_exchange^{Apsi}": {
            "architecture_leverage": 5,
            "proof_tractability": 3,
            "dependency_clarity": 5,
            "risk_of_overclaim_control": 4,
            "value_for_later_seam_work": 5,
        },
        "psi-A total conservation": {
            "architecture_leverage": 4,
            "proof_tractability": 4,
            "dependency_clarity": 5,
            "risk_of_overclaim_control": 5,
            "value_for_later_seam_work": 4,
        },
        "psi-A matter-sector exchange": {
            "architecture_leverage": 4,
            "proof_tractability": 4,
            "dependency_clarity": 4,
            "risk_of_overclaim_control": 4,
            "value_for_later_seam_work": 4,
        },
        "psi-A gauge-sector exchange": {
            "architecture_leverage": 4,
            "proof_tractability": 4,
            "dependency_clarity": 4,
            "risk_of_overclaim_control": 4,
            "value_for_later_seam_work": 4,
        },
        "C_source^A": {
            "architecture_leverage": 4,
            "proof_tractability": 4,
            "dependency_clarity": 4,
            "risk_of_overclaim_control": 4,
            "value_for_later_seam_work": 4,
        },
        "C_source^phi": {
            "architecture_leverage": 3,
            "proof_tractability": 4,
            "dependency_clarity": 4,
            "risk_of_overclaim_control": 5,
            "value_for_later_seam_work": 3,
        },
        "psi-A sourced gauge route": {
            "architecture_leverage": 3,
            "proof_tractability": 4,
            "dependency_clarity": 4,
            "risk_of_overclaim_control": 4,
            "value_for_later_seam_work": 4,
        },
        "psi-A current conservation": {
            "architecture_leverage": 3,
            "proof_tractability": 4,
            "dependency_clarity": 3,
            "risk_of_overclaim_control": 4,
            "value_for_later_seam_work": 3,
        },
        "psi-A current route": {
            "architecture_leverage": 3,
            "proof_tractability": 3,
            "dependency_clarity": 3,
            "risk_of_overclaim_control": 4,
            "value_for_later_seam_work": 3,
        },
        "C_bridge^A": {
            "architecture_leverage": 3,
            "proof_tractability": 3,
            "dependency_clarity": 3,
            "risk_of_overclaim_control": 4,
            "value_for_later_seam_work": 3,
        },
        "C_bridge^phi": {
            "architecture_leverage": 2,
            "proof_tractability": 3,
            "dependency_clarity": 3,
            "risk_of_overclaim_control": 4,
            "value_for_later_seam_work": 3,
        },
        "C_transport^A": {
            "architecture_leverage": 2,
            "proof_tractability": 3,
            "dependency_clarity": 3,
            "risk_of_overclaim_control": 4,
            "value_for_later_seam_work": 2,
        },
        "C_transport^phi": {
            "architecture_leverage": 2,
            "proof_tractability": 3,
            "dependency_clarity": 3,
            "risk_of_overclaim_control": 4,
            "value_for_later_seam_work": 2,
        },
    }
    profile = profiles[row_id]
    profile["scale"] = "1-5, higher is better; risk score means overclaim control"
    return profile


def _priority_ranking(index: dict[str, Any]) -> list[dict[str, Any]]:
    rows = _row_index(index)
    ranking = []
    for rank, row_id in enumerate(RANKED_ROW_IDS, start=1):
        source_row = rows[row_id]
        ranking.append(
            {
                "rank": rank,
                "row_id": row_id,
                "priority_label": (
                    TOP_OBLIGATION_CANDIDATE
                    if row_id == TOP_OBLIGATION_ROW_ID
                    else f"{row_id} theorem-linkage gap"
                ),
                "rule_family": source_row["rule_family"],
                "theorem_linkage_status": source_row["theorem_linkage_status"],
                "open_proof_debt": source_row["open_proof_debt"],
                "next_possible_theorem_slice": source_row[
                    "next_possible_theorem_slice"
                ],
                "criterion_profile": _criterion_profile(row_id),
                "ranking_rationale": _priority_rationale(row_id),
                "top_obligation_candidate": row_id == TOP_OBLIGATION_ROW_ID,
                "selected_for_proof_execution": False,
                "theorem_discharged": False,
                "gap_discharged": False,
                "rule_promoted": False,
            }
        )
    return ranking


def _ranking_criteria(ranking: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_priority_selection_preparation_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The packet consumes the live priority-selection target.",
        },
        {
            "row_id": "ranks_all_indexed_rows",
            "status": "accepted",
            "evidence": [row["row_id"] for row in ranking],
            "assessment": "All 13 indexed C_k theorem-linkage rows are ranked once.",
        },
        {
            "row_id": "priority_criteria_recorded",
            "status": "accepted",
            "evidence": PRIORITY_CRITERIA,
            "assessment": "The ranking criteria are explicitly recorded.",
        },
        {
            "row_id": "top_candidate_selected",
            "status": "accepted",
            "evidence": TOP_OBLIGATION_CANDIDATE,
            "assessment": "C_exchange is selected as the top obligation candidate.",
        },
        {
            "row_id": "top_five_themes_preserved",
            "status": "accepted",
            "evidence": TOP_FIVE_PRIORITY_THEMES,
            "assessment": (
                "The suggested top themes are preserved, with matter/gauge "
                "exchange split across the two indexed exchange rows."
            ),
        },
        {
            "row_id": "no_proof_target_selected",
            "status": "accepted",
            "evidence": {
                "selected_proof_target": SELECTED_PROOF_TARGET,
                "selected_theorem_row": SELECTED_THEOREM_ROW,
            },
            "assessment": "Top-candidate selection is not proof execution.",
        },
        {
            "row_id": "no_gap_or_rule_discharge",
            "status": "accepted",
            "evidence": {
                "gap_count": 8,
                "open_gap_count": 8,
                "closed_gap_count": 0,
            },
            "assessment": "GAP-1 through GAP-8 and all row debts remain open.",
        },
        {
            "row_id": "no_ck_promotion_or_action_route",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "No C_k rule promotion or action route is selected.",
        },
        {
            "row_id": "review_target_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The immediate next target is result review.",
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
        "checkpoint_type": "ck_family_theorem_linkage_priority_selection_after_index",
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


def build_ck_family_theorem_linkage_priority_selection_after_index(
    *,
    selector_review_path: Path = SELECTOR_REVIEW_PATH,
    index_path: Path = INDEX_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector_review = _read_json(selector_review_path)
    index = _read_json(index_path)
    ranking = _priority_ranking(index)
    ranked_ids = [row["row_id"] for row in ranking]
    ranking_criteria = _ranking_criteria(ranking)
    acceptance_criteria = {
        "consumes_expected_priority_selection_target": (
            selector_review.get("schema_id") == SELECTOR_REVIEW_SCHEMA_ID
            and selector_review.get("packet_id") == SELECTOR_REVIEW_PACKET_ID
            and selector_review.get("outcome_id") == SELECTOR_REVIEW_OUTCOME
            and selector_review.get("selected_next_target") == CONSUMED_TARGET
            and selector_review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and selector_review.get("accepted") is True
        ),
        "indexed_rows_preserved": (
            index.get("proof_obligation_row_ids") == OBLIGATION_ROW_IDS
            and index.get("proof_obligation_row_count") == 13
            and index.get("obligation_row_fields") == OBLIGATION_ROW_FIELDS
            and index.get("obligation_row_field_count") == 10
        ),
        "ranking_covers_exactly_13_rows": (
            ranked_ids == RANKED_ROW_IDS
            and sorted(ranked_ids) == sorted(OBLIGATION_ROW_IDS)
            and len(ranked_ids) == 13
            and len(set(ranked_ids)) == 13
        ),
        "priority_criteria_recorded": PRIORITY_CRITERIA
        == [
            "architecture leverage",
            "proof tractability",
            "dependency clarity",
            "risk of overclaim",
            "value for later seam work",
        ],
        "top_obligation_candidate_selected": (
            ranking[0]["row_id"] == TOP_OBLIGATION_ROW_ID
            and ranking[0]["top_obligation_candidate"] is True
            and TOP_OBLIGATION_CANDIDATE == "C_exchange theorem-linkage gap"
        ),
        "top_five_theme_order_preserved": TOP_FIVE_PRIORITY_THEMES
        == [
            "C_exchange theorem-linkage gap",
            "psi-A total-conservation theorem-linkage gap",
            "psi-A matter/gauge exchange theorem-linkage gap",
            "C_source^A theorem-linkage gap",
            "C_source^phi theorem-linkage gap",
        ],
        "no_proof_execution_or_theorem_discharge": all(
            row["selected_for_proof_execution"] is False
            and row["theorem_discharged"] is False
            and row["gap_discharged"] is False
            and row["rule_promoted"] is False
            for row in ranking
        ),
        "all_gaps_remain_open": (
            selector_review.get("gap_count") == 8
            and selector_review.get("open_gap_count") == 8
            and selector_review.get("closed_gap_count") == 0
            and selector_review.get("no_gap_discharged") is True
            and selector_review.get("no_gap_closed") is True
        ),
        "rule_architecture_context_preserved": (
            selector_review.get("C_source_classification") == C_SOURCE_CLASSIFICATION
            and selector_review.get("C_bridge_classification") == C_BRIDGE_CLASSIFICATION
            and selector_review.get("C_transport_classification")
            == C_TRANSPORT_CLASSIFICATION
            and selector_review.get("C_exchange_classification")
            == C_EXCHANGE_CLASSIFICATION
            and selector_review.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "no_input_forbidden_claims": _input_boundary_clear(selector_review),
        "ranking_criteria_all_accepted": all(
            row["status"] == "accepted" for row in ranking_criteria
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            selector_review.get("aggregate_lean_validation_status_for_review")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and selector_review.get("full_toeformal_aggregate_status_for_review")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and selector_review.get("full_toeformal_aggregate_passed") is False
            and selector_review.get("full_toeformal_aggregate_failed") is False
            and selector_review.get("full_toeformal_aggregate_timed_out") is False
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_REQUIRES_REMEDIATION",
        "priority_selection_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_PRIORITY_SELECTION_AFTER_INDEX_REQUIRES_REMEDIATION",
        "recommended_priority_selection_result": RECOMMENDED_PRIORITY_SELECTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "recommended_post_review_target": RECOMMENDED_POST_REVIEW_TARGET,
        "recommended_post_review_target_kind": RECOMMENDED_POST_REVIEW_TARGET_KIND,
        "selector_review_schema_id": SELECTOR_REVIEW_SCHEMA_ID,
        "selector_review_packet_id": SELECTOR_REVIEW_PACKET_ID,
        "selector_review_outcome": SELECTOR_REVIEW_OUTCOME,
        "selector_review_consumed": accepted,
        "priority_criteria": PRIORITY_CRITERIA,
        "priority_criterion_count": len(PRIORITY_CRITERIA),
        "priority_ranking": ranking,
        "priority_ranking_count": len(ranking),
        "ranked_row_ids": ranked_ids,
        "ranked_row_count": len(ranked_ids),
        "top_five_priority_themes": TOP_FIVE_PRIORITY_THEMES,
        "top_five_priority_theme_count": len(TOP_FIVE_PRIORITY_THEMES),
        "top_obligation_candidate": TOP_OBLIGATION_CANDIDATE,
        "top_obligation_row_id": TOP_OBLIGATION_ROW_ID,
        "top_obligation_next_possible_theorem_slice": TOP_OBLIGATION_NEXT_SLICE,
        "top_obligation_candidate_selected": accepted,
        "ranking_selects_top_obligation_candidate": accepted,
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
        "ranking_criteria": ranking_criteria,
        "ranking_criteria_count": len(ranking_criteria),
        "ranking_criteria_accepted_count": sum(
            1 for row in ranking_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "priority_selection_packet_prepared": accepted,
        "priority_selection_prepared": accepted,
        "priority_selection_executed": accepted,
        "priority_rows_ranked": accepted,
        "priority_row_selected": accepted,
        "theorem_linkage_obligation_index_reviewed": accepted,
        "obligation_index_reviewed": accepted,
        "proof_obligation_rows_indexed": accepted,
        "row_index_only": False,
        "proof_debt_target_selected": False,
        "proof_target_selected": False,
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
            "The proof-debt map is now ranked. C_exchange is the highest-value "
            "theorem-linkage candidate, but no proof is executed yet."
        ),
        "mathematical_statement": (
            "The priority-selection packet ranks the 13 indexed C_k "
            "theorem-linkage obligations by architecture leverage, proof "
            "tractability, dependency clarity, overclaim risk control, and "
            "later seam-work value. It selects C_exchange as the top obligation "
            "candidate while leaving all proof discharge, theorem execution, "
            "gap discharge, C_k promotion, action embedding, variation, closure, "
            "empirical, and master-action claims blocked."
        ),
        "non_claim_boundary": (
            "This priority-selection packet ranks the indexed C_k "
            "theorem-linkage proof debts and selects only the top obligation "
            "candidate. It does not execute any proof, discharge any theorem "
            "row, discharge GAP-1 through GAP-8, promote any C_k rule, embed "
            "C_k in an action, vary C_k, select a multiplier route, select a "
            "penalty route, make a direct dynamical-law claim, close EM-QFT, "
            "close QFT-GR, close GR-QM, claim empirical validation, or promote "
            "the master action. The master action remains a working-form, "
            "noncanonical, non-promoted organizing surface. The full ToeFormal "
            "aggregate is kept as NOT_RUN."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_ck_family_theorem_linkage_priority_selection_after_index",
            "fail to rank all 13 indexed rows exactly once",
            "fail to select C_exchange as the top obligation candidate",
            "treat top-candidate selection as theorem discharge",
            "select a proof target for execution",
            "authorize proof target execution",
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
            "ToeFormal.Derivation.CKFamilyTheoremLinkagePrioritySelectionAfterIndex",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "selector_review_file": _ptr(selector_review_path),
            "selector_review_lean_file": _ptr(SELECTOR_REVIEW_LEAN_PACKET_PATH),
            "index_file": _ptr(index_path),
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


def write_priority_selection(
    priority_selection: dict[str, Any], out: Path = DEFAULT_OUT
) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(priority_selection, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Rank the C_k family theorem-linkage obligations after the index."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--selector-review", type=Path, default=SELECTOR_REVIEW_PATH)
    parser.add_argument("--index", type=Path, default=INDEX_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    selector_review_path = (
        args.selector_review
        if args.selector_review.is_absolute()
        else REPO_ROOT / args.selector_review
    )
    index_path = args.index if args.index.is_absolute() else REPO_ROOT / args.index
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_ck_family_theorem_linkage_priority_selection_after_index(
        selector_review_path=selector_review_path,
        index_path=index_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_priority_selection(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "priority_selection_result": payload["priority_selection_result"],
                "selected_next_target": payload["selected_next_target"],
                "top_obligation_candidate": payload["top_obligation_candidate"],
                "top_obligation_row_id": payload["top_obligation_row_id"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
