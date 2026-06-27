from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_index_report import (
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
    DEFAULT_OUT as SELECTION_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as SELECTION_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LIKELY_FIRST_PRIORITY_CANDIDATE,
    LIKELY_PRIORITY_CANDIDATES,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OBLIGATION_ROW_FIELDS,
    OBLIGATION_ROW_IDS,
    OUTCOME_ID as SELECTION_OUTCOME,
    PACKET_ID as SELECTION_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RECOMMENDED_FIRST_PRIORITY_ROW,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as SELECTION_SCHEMA_ID,
    SELECTED_FOLLOW_ON_TARGET,
    SELECTED_FOLLOW_ON_TARGET_KIND,
    SELECTED_PACKET_EXECUTION_STATUS,
    SELECTED_PACKET_LABEL,
    SELECTED_PACKET_STATUS,
    SELECTED_PROOF_TARGET,
    SELECTED_THEOREM_ROW,
    SELECTION_RESULT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_RESULT_REVIEW_"
    "20260626_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_RESULT_REVIEW_"
    "ACCEPTS_PRIORITY_SELECTION_PACKET_HANDOFF_NO_PROOF_EXECUTION_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "ck_family_theorem_linkage_obligation_selection_after_index_result_review_"
    "accepts_priority_selection_packet_handoff_no_proof_execution_or_"
    "master_action_promotion"
)

NEXT_TARGET = SELECTED_FOLLOW_ON_TARGET
NEXT_TARGET_KIND = SELECTED_FOLLOW_ON_TARGET_KIND

ACCEPTED_REVIEW_FINDINGS = [
    "selector outcome accepted",
    "prepare_ck_family_theorem_linkage_priority_selection_after_index preserved as follow-on target",
    "no theorem row selected",
    "no proof execution",
    "no GAP-1 through GAP-8 discharge",
    "no C_k rule promotion",
    "no C_k functionalization",
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
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_RESULT_REVIEW_"
        "20260626_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CKFamilyTheoremLinkageObligationSelectionAfterIndexResultReview.lean"
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


def _input_boundary_clear(selection: dict[str, Any]) -> bool:
    return all(
        selection.get(key) is False
        for key in _false_boundary_flags()
        if key in selection
    )


def _review_criteria(selection: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_outcome_accepted",
            "status": "accepted",
            "evidence": selection.get("selection_result"),
            "assessment": "The selector outcome is accepted.",
        },
        {
            "row_id": "priority_selection_packet_handoff_preserved",
            "status": "accepted",
            "evidence": selection.get("selected_follow_on_target_after_review"),
            "assessment": (
                "The priority-selection packet remains the follow-on target."
            ),
        },
        {
            "row_id": "no_theorem_row_selected",
            "status": "accepted",
            "evidence": selection.get("selected_theorem_row"),
            "assessment": "No theorem row is selected for proof execution.",
        },
        {
            "row_id": "no_proof_execution",
            "status": "accepted",
            "evidence": {
                "proof_execution_authorized": selection.get(
                    "proof_execution_authorized"
                ),
                "proof_attempt_executed": selection.get("proof_attempt_executed"),
            },
            "assessment": "No proof execution is authorized or executed.",
        },
        {
            "row_id": "no_gap_discharge",
            "status": "accepted",
            "evidence": {
                "gap_count": selection.get("gap_count"),
                "open_gap_count": selection.get("open_gap_count"),
                "closed_gap_count": selection.get("closed_gap_count"),
            },
            "assessment": "GAP-1 through GAP-8 remain open.",
        },
        {
            "row_id": "no_rule_promotion_functionalization_or_variation",
            "status": "accepted",
            "evidence": [
                "rule_promoted=false",
                "functionalization_authorized=false",
                "C_k_action_variation_executed=false",
            ],
            "assessment": "No C_k promotion, functionalization, or variation occurs.",
        },
        {
            "row_id": "no_seam_empirical_or_master_action_promotion",
            "status": "accepted",
            "evidence": [
                "seam_closure_claim=false",
                "empirical_validation_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No seam closure, empirical validation, or promotion occurs.",
        },
        {
            "row_id": "likely_priority_candidates_preserved",
            "status": "accepted",
            "evidence": selection.get("likely_priority_candidates"),
            "assessment": "Likely priority candidates are preserved for ranking.",
        },
        {
            "row_id": "priority_packet_not_prepared_in_review",
            "status": "accepted",
            "evidence": "priority_selection_prepared=false",
            "assessment": "The result review authorizes the next target only.",
        },
        {
            "row_id": "next_target_is_priority_selection_preparation",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The review rotates to priority-selection packet preparation.",
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
        "checkpoint_type": (
            "ck_family_theorem_linkage_obligation_selection_after_index_result_review"
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
        "aggregate_lean_validation_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "aggregate_lean_validation_status_allowed_values": ["NOT_RUN"],
        "full_toeformal_aggregate_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_ck_family_theorem_linkage_obligation_selection_after_index_result_review(
    *,
    selection_path: Path = SELECTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selection = _read_json(selection_path)
    review_criteria = _review_criteria(selection)
    acceptance_criteria = {
        "consumes_expected_selector_result_review_target": (
            selection.get("schema_id") == SELECTION_SCHEMA_ID
            and selection.get("packet_id") == SELECTION_PACKET_ID
            and selection.get("outcome_id") == SELECTION_OUTCOME
            and selection.get("selection_result") == SELECTION_RESULT
            and selection.get("packet_result") == SELECTION_OUTCOME
            and selection.get("selected_next_target") == CONSUMED_TARGET
            and selection.get("accepted") is True
        ),
        "follow_on_target_preserved": (
            selection.get("selected_follow_on_target_after_review") == NEXT_TARGET
            and selection.get("selected_follow_on_target_kind") == NEXT_TARGET_KIND
        ),
        "selector_selected_packet_only": (
            selection.get("priority_selection_packet_selected") is True
            and selection.get("priority_selection_packet_prepared") is False
            and selection.get("priority_selection_prepared") is False
            and selection.get("selected_proof_target") == SELECTED_PROOF_TARGET
            and selection.get("selected_theorem_row") == SELECTED_THEOREM_ROW
            and selection.get("proof_target_selected") is False
            and selection.get("theorem_row_selected") is False
        ),
        "no_proof_execution": (
            selection.get("proof_execution_authorized") is False
            and selection.get("proof_target_execution_authorized") is False
            and selection.get("proof_attempt_executed") is False
            and selection.get("proof_debt_reduced") is False
            and selection.get("proof_debt_discharged") is False
        ),
        "rows_and_candidates_preserved": (
            selection.get("proof_obligation_row_ids") == OBLIGATION_ROW_IDS
            and selection.get("proof_obligation_row_count") == 13
            and selection.get("obligation_row_fields") == OBLIGATION_ROW_FIELDS
            and selection.get("controlled_status_labels") == CONTROLLED_STATUS_LABELS
            and selection.get("likely_priority_candidates") == LIKELY_PRIORITY_CANDIDATES
            and selection.get("likely_first_priority_candidate")
            == LIKELY_FIRST_PRIORITY_CANDIDATE
            and selection.get("recommended_first_priority_row")
            == RECOMMENDED_FIRST_PRIORITY_ROW
        ),
        "all_gaps_remain_open": (
            selection.get("gap_count") == 8
            and selection.get("open_gap_count") == 8
            and selection.get("closed_gap_count") == 0
            and selection.get("no_gap_discharged") is True
            and selection.get("no_gap_closed") is True
        ),
        "no_rule_functionalization_variation_or_promotion": (
            selection.get("no_rule_promoted") is True
            and selection.get("no_C_k_functionalization_occurs") is True
            and selection.get("no_C_k_variation_occurs") is True
            and selection.get("no_seam_closure_occurs") is True
            and selection.get("no_master_action_promotion_occurs") is True
            and selection.get("master_action_promoted") is False
        ),
        "rule_architecture_context_preserved": (
            selection.get("C_source_classification") == C_SOURCE_CLASSIFICATION
            and selection.get("C_bridge_classification") == C_BRIDGE_CLASSIFICATION
            and selection.get("C_transport_classification") == C_TRANSPORT_CLASSIFICATION
            and selection.get("C_exchange_classification") == C_EXCHANGE_CLASSIFICATION
            and selection.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "no_input_forbidden_claims": _input_boundary_clear(selection),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            selection.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and selection.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and selection.get("full_toeformal_aggregate_passed") is False
            and selection.get("full_toeformal_aggregate_failed") is False
            and selection.get("full_toeformal_aggregate_timed_out") is False
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_RESULT"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_"
            "RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_INDEX_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_follow_on_target_after_review": NEXT_TARGET,
        "selected_follow_on_target_kind": NEXT_TARGET_KIND,
        "selected_post_review_target": NEXT_TARGET,
        "selected_post_review_target_kind": NEXT_TARGET_KIND,
        "selection_schema_id": SELECTION_SCHEMA_ID,
        "selection_packet_id": SELECTION_PACKET_ID,
        "selection_outcome": SELECTION_OUTCOME,
        "selection_result": SELECTION_RESULT,
        "selection_accepted": accepted,
        "selected_packet_label": SELECTED_PACKET_LABEL,
        "selected_packet_status": "selection_reviewed_pending_preparation",
        "selected_packet_execution_status": SELECTED_PACKET_EXECUTION_STATUS,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
        "likely_priority_candidates": LIKELY_PRIORITY_CANDIDATES,
        "likely_priority_candidate_count": len(LIKELY_PRIORITY_CANDIDATES),
        "likely_first_priority_candidate": LIKELY_FIRST_PRIORITY_CANDIDATE,
        "recommended_first_priority_row": RECOMMENDED_FIRST_PRIORITY_ROW,
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
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "review_executed": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": accepted,
        "selector_result_review_prepared": accepted,
        "selector_result_review_accepted": accepted,
        "selector_outcome_accepted": accepted,
        "priority_selection_packet_handoff_accepted": accepted,
        "priority_selection_packet_selected": accepted,
        "priority_selection_packet_preparation_authorized": accepted,
        "priority_selection_packet_authorized_after_review": accepted,
        "priority_selection_packet_prepared": False,
        "priority_selection_packet_executed": False,
        "priority_selection_prepared": False,
        "priority_selection_executed": False,
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
            "The review accepts the selector-only handoff to a priority-selection "
            "packet. It does not rank rows or execute proof work."
        ),
        "mathematical_statement": (
            "The result review accepts that the selector chose "
            "prepare_ck_family_theorem_linkage_priority_selection_after_index. "
            "It preserves the indexed C_k proof obligations and records no "
            "theorem-row selection, proof execution, gap discharge, or C_k "
            "promotion."
        ),
        "non_claim_boundary": (
            "This selector-result review accepts only the handoff to the C_k "
            "family theorem-linkage priority-selection packet. It does not "
            "prepare that packet, rank rows, select a theorem row for proof "
            "execution, execute any proof target, discharge GAP-1 through "
            "GAP-8, promote any C_k rule, functionalize C_k, embed C_k in an "
            "action, vary C_k, select a multiplier route, select a penalty "
            "route, make a direct dynamical-law claim, close EM-QFT, close "
            "QFT-GR, close GR-QM, claim empirical validation, or promote the "
            "master action. The master action remains a working-form, "
            "noncanonical, non-promoted organizing surface. The full ToeFormal "
            "aggregate is kept as NOT_RUN."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_ck_family_theorem_linkage_obligation_selection_after_index_result",
            "fail to rotate to prepare_ck_family_theorem_linkage_priority_selection_after_index",
            "rank rows inside this result review",
            "select a theorem row for proof execution",
            "authorize proof target execution",
            "prepare the priority-selection packet inside this review",
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
        "aggregate_lean_validation_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterIndexResultReview",
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
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }
    payload.update(_false_boundary_flags())
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
            "Review the C_k theorem-linkage obligation selector after the index."
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
    payload = build_ck_family_theorem_linkage_obligation_selection_after_index_result_review(
        selection_path=selection_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
