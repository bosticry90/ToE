from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_theorem_linkage_obligation_index_report import (
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
    DEFAULT_OUT as INDEX_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    INDEX_RESULT,
    LEAN_PACKET_PATH as INDEX_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OBLIGATION_ROW_FIELDS,
    OBLIGATION_ROW_IDS,
    OUTCOME_ID as INDEX_OUTCOME,
    PACKET_ID as INDEX_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as INDEX_SCHEMA_ID,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_RESULT_REVIEW_20260626_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_RESULT_REVIEW_ACCEPTS_RULE_FAMILY_"
    "THEOREM_LINKAGE_AND_PROOF_DEBT_ROWS_INDEXED_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "ck_family_theorem_linkage_obligation_index_result_review_accepts_rule_family_"
    "theorem_linkage_and_proof_debt_rows_indexed_no_action_variation_or_"
    "master_action_promotion"
)

NEXT_TARGET = "select_next_ck_family_theorem_linkage_obligation_after_index"
NEXT_TARGET_KIND = "ck_family_theorem_linkage_obligation_after_index_selector"
RECOMMENDED_SELECTOR_CHOICE = (
    "prepare_ck_family_theorem_linkage_priority_selection_after_index"
)
RECOMMENDED_PRIORITY_ROW = "C_exchange^{Apsi}"

SELECTOR_CANDIDATES = [
    "C_exchange theorem-linkage gap",
    "psi-A total-conservation theorem-linkage gap",
    "C_source^A theorem-linkage gap",
    "C_source^phi theorem-linkage gap",
]

ACCEPTED_REVIEW_FINDINGS = [
    "13 obligation rows indexed",
    "phi source/bridge/transport rows included",
    "A source/bridge/transport rows included",
    "psi-A current/source/exchange/total-conservation/C_exchange rows included",
    "theorem-linkage status recorded",
    "supplied assumptions recorded",
    "open proof debt recorded",
    "functionalization and variation blockers recorded",
    "seam-closure blockers recorded",
    "next possible theorem slices recorded",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_RESULT_REVIEW_20260626_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CKFamilyTheoremLinkageObligationIndexResultReview.lean"
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
        "proof_execution_authorized": False,
        "priority_selection_prepared": False,
        "proof_debt_target_selected": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "new_physics_created": False,
        "new_field_or_interaction_expansion_selected": False,
        "immediate_new_field_or_interaction_expansion_selected": False,
    }


def _input_boundary_clear(index: dict[str, Any]) -> bool:
    return all(
        index.get(key) is False
        for key in _false_boundary_flags()
        if key in index
    )


def _review_criteria(index: dict[str, Any]) -> list[dict[str, Any]]:
    rows = index.get("proof_obligation_rows", [])
    row_ids = [row.get("row_id") for row in rows]
    row_fields_present = all(
        all(
            key in row
            for key in [
                "rule_family",
                "field_or_interaction_scope",
                "current_evidence_pointer",
                "theorem_linkage_status",
                "supplied_assumptions",
                "open_proof_debt",
                "functionalization_blocker",
                "variation_blocker",
                "seam_closure_blocker",
                "next_possible_theorem_slice",
            ]
        )
        for row in rows
    )
    return [
        {
            "row_id": "thirteen_obligation_rows_indexed",
            "status": "accepted",
            "evidence": row_ids,
            "assessment": "The review accepts that all 13 obligation rows are indexed.",
        },
        {
            "row_id": "phi_triad_rows_included",
            "status": "accepted",
            "evidence": ["C_source^phi", "C_bridge^phi", "C_transport^phi"],
            "assessment": "The phi source/bridge/transport rows are included.",
        },
        {
            "row_id": "A_triad_rows_included",
            "status": "accepted",
            "evidence": ["C_source^A", "C_bridge^A", "C_transport^A"],
            "assessment": "The A source/bridge/transport rows are included.",
        },
        {
            "row_id": "psi_A_interaction_rows_included",
            "status": "accepted",
            "evidence": [
                "psi-A current route",
                "psi-A current conservation",
                "psi-A sourced gauge route",
                "psi-A gauge-sector exchange",
                "psi-A matter-sector exchange",
                "psi-A total conservation",
                "C_exchange^{Apsi}",
            ],
            "assessment": (
                "The psi-A current/source/exchange/total-conservation/C_exchange "
                "rows are included."
            ),
        },
        {
            "row_id": "theorem_linkage_status_recorded",
            "status": "accepted",
            "evidence": index.get("controlled_status_labels"),
            "assessment": "Controlled theorem-linkage statuses are recorded.",
        },
        {
            "row_id": "assumptions_and_proof_debt_recorded",
            "status": "accepted",
            "evidence": row_fields_present,
            "assessment": "Supplied assumptions and open proof debt are recorded per row.",
        },
        {
            "row_id": "blockers_and_next_slices_recorded",
            "status": "accepted",
            "evidence": row_fields_present,
            "assessment": (
                "Functionalization, variation, seam-closure blockers, and next "
                "possible theorem slices are recorded."
            ),
        },
        {
            "row_id": "no_gap_discharge_or_rule_promotion",
            "status": "accepted",
            "evidence": {
                "closed_gap_count": index.get("closed_gap_count"),
                "obligation_rows_discharged": index.get("obligation_rows_discharged"),
                "rule_promoted": index.get("rule_promoted"),
            },
            "assessment": "No gap is discharged and no C_k rule is promoted.",
        },
        {
            "row_id": "no_action_variation_or_seam_claim",
            "status": "accepted",
            "evidence": [
                "C_k_action_embedding_claimed=false",
                "C_k_action_variation_executed=false",
                "em_qft_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "gr_qm_closure_claimed=false",
            ],
            "assessment": "No action embedding, variation, or seam closure is accepted.",
        },
        {
            "row_id": "next_selector_target_authorized_only",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The review authorizes only a selector for choosing the next "
                "obligation row; no proof execution is authorized."
            ),
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
        "checkpoint_type": "ck_family_theorem_linkage_obligation_index_result_review",
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


def build_ck_family_theorem_linkage_obligation_index_result_review(
    *,
    index_path: Path = INDEX_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    index = _read_json(index_path)
    rows = index.get("proof_obligation_rows", [])
    criteria = _review_criteria(index)
    acceptance_criteria = {
        "consumes_expected_obligation_index_result_review_target": (
            index.get("schema_id") == INDEX_SCHEMA_ID
            and index.get("packet_id") == INDEX_PACKET_ID
            and index.get("outcome_id") == INDEX_OUTCOME
            and index.get("index_result") == INDEX_RESULT
            and index.get("packet_result") == INDEX_OUTCOME
            and index.get("selected_next_target") == CONSUMED_TARGET
            and index.get("accepted") is True
        ),
        "thirteen_obligation_rows_accepted": (
            index.get("proof_obligation_row_ids") == OBLIGATION_ROW_IDS
            and index.get("proof_obligation_row_count") == 13
            and [row.get("row_id") for row in rows] == OBLIGATION_ROW_IDS
        ),
        "required_fields_and_statuses_accepted": (
            index.get("obligation_row_fields") == OBLIGATION_ROW_FIELDS
            and index.get("obligation_row_field_count") == 10
            and index.get("controlled_status_labels") == CONTROLLED_STATUS_LABELS
            and index.get("controlled_status_label_count") == 7
        ),
        "row_fields_recorded": all(
            row.get("supplied_assumptions")
            and row.get("open_proof_debt")
            and row.get("functionalization_blocker")
            and row.get("variation_blocker")
            and row.get("seam_closure_blocker")
            and row.get("next_possible_theorem_slice")
            for row in rows
        ),
        "all_rows_remain_undischarged": all(
            row.get("proof_attempt_executed") is False
            and row.get("proof_obligation_discharged") is False
            and row.get("gap_discharged") is False
            and row.get("rule_promoted") is False
            and row.get("functionalized") is False
            and row.get("varied") is False
            and row.get("seam_closed") is False
            for row in rows
        ),
        "all_gaps_remain_open": (
            index.get("gap_count") == 8
            and index.get("open_gap_count") == 8
            and index.get("closed_gap_count") == 0
            and index.get("no_gap_discharged") is True
            and index.get("no_gap_closed") is True
        ),
        "rule_architecture_context_preserved": (
            index.get("C_source_classification") == C_SOURCE_CLASSIFICATION
            and index.get("C_bridge_classification") == C_BRIDGE_CLASSIFICATION
            and index.get("C_transport_classification") == C_TRANSPORT_CLASSIFICATION
            and index.get("C_exchange_classification") == C_EXCHANGE_CLASSIFICATION
            and index.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "no_input_forbidden_claims": _input_boundary_clear(index),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in criteria
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            index.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and index.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and index.get("full_toeformal_aggregate_passed") is False
            and index.get("full_toeformal_aggregate_failed") is False
            and index.get("full_toeformal_aggregate_timed_out") is False
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_follow_on_target_after_review": NEXT_TARGET,
        "selected_follow_on_target_kind": NEXT_TARGET_KIND,
        "recommended_selector_choice": RECOMMENDED_SELECTOR_CHOICE,
        "recommended_priority_row": RECOMMENDED_PRIORITY_ROW,
        "selector_candidates": SELECTOR_CANDIDATES,
        "selector_candidate_count": len(SELECTOR_CANDIDATES),
        "priority_selection_prepared": False,
        "priority_selection_executed": False,
        "proof_debt_target_selected": False,
        "proof_execution_authorized": False,
        "index_schema_id": INDEX_SCHEMA_ID,
        "index_packet_id": INDEX_PACKET_ID,
        "index_outcome": INDEX_OUTCOME,
        "index_result": INDEX_RESULT,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
        "proof_obligation_rows": rows,
        "proof_obligation_row_ids": OBLIGATION_ROW_IDS,
        "proof_obligation_row_count": len(rows),
        "obligation_row_fields": OBLIGATION_ROW_FIELDS,
        "obligation_row_field_count": len(OBLIGATION_ROW_FIELDS),
        "controlled_status_labels": CONTROLLED_STATUS_LABELS,
        "controlled_status_label_count": len(CONTROLLED_STATUS_LABELS),
        "theorem_linkage_status_counts": index.get("theorem_linkage_status_counts"),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "review_criteria": criteria,
        "review_criteria_count": len(criteria),
        "review_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": accepted,
        "theorem_linkage_obligation_index_reviewed": accepted,
        "obligation_index_reviewed": accepted,
        "proof_obligation_rows_indexed": accepted,
        "rule_family_theorem_linkage_and_proof_debt_rows_accepted": accepted,
        "row_index_only": accepted,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
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
            "The review accepts the obligation index as an index only. The next "
            "step is a selector for choosing one high-value theorem-linkage row."
        ),
        "mathematical_statement": (
            "The review accepts the indexed rows C_source^phi, C_bridge^phi, "
            "C_transport^phi, C_source^A, C_bridge^A, C_transport^A, psi-A "
            "current route, psi-A current conservation, psi-A sourced gauge "
            "route, psi-A gauge-sector exchange, psi-A matter-sector exchange, "
            "psi-A total conservation, and C_exchange^{Apsi}. It records no "
            "proof discharge and authorizes only a selector target."
        ),
        "non_claim_boundary": (
            "This result review accepts only that the C_k family theorem-linkage "
            "obligation index recorded 13 proof-obligation rows and their "
            "theorem-linkage statuses, supplied assumptions, open proof debts, "
            "functionalization blockers, variation blockers, seam-closure "
            "blockers, and next theorem slices. It discharges no GAP-1 through "
            "GAP-8 item, proves no row, selects no proof target, authorizes no "
            "proof execution, promotes no C_k rule, embeds no C_k rule in an "
            "action, varies no C_k rule, selects no multiplier route, selects "
            "no penalty route, makes no direct dynamical-law claim, closes no "
            "EM-QFT, QFT-GR, GR-QM, empirical, or seam target, and promotes no "
            "master action. The master action remains a working-form, "
            "noncanonical, non-promoted organizing surface. The full ToeFormal "
            "aggregate is kept as NOT_RUN."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_ck_family_theorem_linkage_obligation_index_result",
            "fail to accept all 13 obligation rows",
            "claim any GAP-1 through GAP-8 item is discharged",
            "claim any row proof debt is reduced or discharged",
            "select a proof target inside the review",
            "authorize proof execution inside the review",
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
            "ToeFormal.Derivation.CKFamilyTheoremLinkageObligationIndexResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "index_file": _ptr(index_path),
            "index_lean_file": _ptr(INDEX_LEAN_PACKET_PATH),
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
        description="Review the C_k family theorem-linkage obligation index result."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--index", type=Path, default=INDEX_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    index_path = args.index if args.index.is_absolute() else REPO_ROOT / args.index
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_ck_family_theorem_linkage_obligation_index_result_review(
        index_path=index_path,
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
