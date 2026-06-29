from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_interaction_exchange_theorem_linkage_chain_closeout_report import (
    C_EXCHANGE_LINKAGE_CONCLUSION,
    C_EXCHANGE_LINKAGE_DEFINITION,
    C_EXCHANGE_LINKAGE_INPUT,
    CLAIM_BOUNDARY as CLOSEOUT_CLAIM_BOUNDARY,
    CLOSEOUT_CLAIMS,
    CLOSEOUT_RESULT,
    CLOSEOUT_STATEMENT,
    DEFAULT_OUT as CLOSEOUT_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT,
    GAUGE_SECTOR_CONCLUSION,
    GAUGE_SECTOR_INPUT_ROUTE,
    GAUGE_STRESS_DIVERGENCE_IDENTITY,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_CLOSEOUT,
    LOCAL_DEPENDENCY_CHAIN,
    MATTER_SECTOR_CONCLUSION,
    MATTER_SECTOR_INPUT_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    NONCLAIMS as CLOSEOUT_NONCLAIMS,
    OUTCOME_ID as CLOSEOUT_OUTCOME,
    PACKET_ID as CLOSEOUT_PACKET_ID,
    PLAIN_MEANING,
    SCHEMA_ID as CLOSEOUT_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT,
    SOURCED_MAXWELL_ROUTE,
    STRICT_CLOSEOUT_RESULT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_CONSERVATION_GAUGE_INPUT,
    TOTAL_CONSERVATION_MATTER_INPUT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_RESULT_REVIEW_"
    "20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_RESULT_REVIEW_"
    "ACCEPTS_LOCAL_CEXCHANGE_TOTAL_MATTER_AND_GAUGE_DEPENDENCY_CHAIN_NO_CK_RULE_"
    "PROMOTION_OR_SEAM_CLOSURE"
)
STRICT_REVIEW_RESULT = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_RESULT_REVIEW_"
    "ACCEPTS_LOCAL_EXCHANGE_BALANCE_SUPPORT_CHAIN_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_interaction_exchange_theorem_linkage_chain_closeout_result_review_"
    "accepts_local_cexchange_total_matter_and_gauge_dependency_chain_no_ck_rule_"
    "promotion_or_seam_closure"
)

NEXT_TARGET = (
    "select_next_ck_family_theorem_linkage_obligation_after_"
    "psi_A_exchange_chain_closeout"
)
NEXT_TARGET_KIND = (
    "ck_family_theorem_linkage_obligation_selection_after_"
    "psi_A_exchange_chain_closeout"
)
LIKELY_NEXT_OBLIGATION = "C_source^A theorem-linkage obligation"
SUGGESTED_SELECTOR_OUTCOME = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_CHAIN_"
    "CLOSEOUT_SELECTS_C_SOURCE_A_THEOREM_LINKAGE_GAP_NO_PROOF_EXECUTION_OR_"
    "MASTER_ACTION_PROMOTION"
)
STRICT_SUGGESTED_SELECTOR_OUTCOME = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_CHAIN_"
    "CLOSEOUT_SELECTS_A_SOURCE_LINKAGE_OBLIGATION_NO_GAP_DISCHARGE_OR_CK_RULE_"
    "PROMOTION"
)

ACCEPTED_REVIEW_FINDINGS = [
    "local psi-A interaction exchange support chain closed",
    "C_exchange linkage included",
    "total-conservation linkage included",
    "matter-sector exchange linkage included",
    "gauge-sector exchange linkage included",
    "dependency order preserved",
    "closeout boundary preserved",
    "no general C_k closure",
    "no seam closure",
    "no empirical validation",
    "no master-action promotion",
]
BOUNDARY_NONCLAIMS = [
    "no general C_k closure",
    "no GAP-1 through GAP-8 global discharge",
    "no C_k rule promotion",
    "no C_k dynamical-law status",
    "no C_k action embedding",
    "no C_k action variation",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no empirical validation",
    "no master-action promotion",
]
CLAIM_BOUNDARY = (
    "closeout result review only; accepts the local psi-A interaction exchange "
    "support chain as closed and bounded; no new proof execution, general C_k "
    "closure, seam closure, empirical validation, or master-action promotion"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_CLOSEOUT

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_RESULT_REVIEW_"
        "20260628_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiAInteractionExchangeTheoremLinkageChainCloseoutResultReview.lean"
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
        "general_C_k_theorem_linkage_closure": False,
        "general_C_k_closure": False,
        "gap_1_through_gap_8_discharged": False,
        "global_gap_discharge_claimed": False,
        "C_k_dynamical_law_status": False,
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
        "assumption_discharge_completed": False,
        "gap_review_closes_any_gap": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "rule_promoted": False,
        "obligation_row_discharged": False,
        "obligation_rows_discharged": False,
        "proof_debt_discharged": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "new_physics_created": False,
        "new_field_or_interaction_expansion_selected": False,
    }


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "psi_A_interaction_exchange_theorem_linkage_chain_closeout_result_review"
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


def _review_criteria(closeout: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "closeout_packet_consumed",
            "status": "accepted",
            "evidence": closeout.get("closeout_result"),
            "assessment": "The local psi-A interaction exchange chain closeout is consumed.",
        },
        {
            "row_id": "support_chain_closed",
            "status": "accepted",
            "evidence": closeout.get(
                "local_psi_A_interaction_exchange_support_chain_closed"
            ),
            "assessment": "The local psi-A interaction exchange support chain is closed.",
        },
        {
            "row_id": "C_exchange_linkage_included",
            "status": "accepted",
            "evidence": C_EXCHANGE_LINKAGE_CONCLUSION,
            "assessment": "The C_exchange linkage remains included.",
        },
        {
            "row_id": "total_conservation_linkage_included",
            "status": "accepted",
            "evidence": TOTAL_CONSERVATION_CONCLUSION,
            "assessment": "The total-conservation linkage remains included.",
        },
        {
            "row_id": "matter_sector_exchange_linkage_included",
            "status": "accepted",
            "evidence": MATTER_SECTOR_CONCLUSION,
            "assessment": "The matter-sector exchange linkage remains included.",
        },
        {
            "row_id": "gauge_sector_exchange_linkage_included",
            "status": "accepted",
            "evidence": GAUGE_SECTOR_CONCLUSION,
            "assessment": "The gauge-sector exchange linkage remains included.",
        },
        {
            "row_id": "boundary_preserved",
            "status": "accepted",
            "evidence": BOUNDARY_NONCLAIMS,
            "assessment": "The review preserves all non-promotion boundaries.",
        },
        {
            "row_id": "selector_target_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next live target is the bounded selector.",
        },
    ]


def _closeout_valid(closeout: dict[str, Any]) -> bool:
    linkage_ids = [row.get("linkage_id") for row in closeout.get("linkage_chain", [])]
    return (
        closeout.get("schema_id") == CLOSEOUT_SCHEMA_ID
        and closeout.get("packet_id") == CLOSEOUT_PACKET_ID
        and closeout.get("outcome_id") == CLOSEOUT_OUTCOME
        and closeout.get("closeout_result") == CLOSEOUT_RESULT
        and closeout.get("strict_closeout_result") == STRICT_CLOSEOUT_RESULT
        and closeout.get("selected_next_target") == CONSUMED_TARGET
        and closeout.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and closeout.get("accepted") is True
        and closeout.get("closed") is True
        and closeout.get("local_psi_A_interaction_exchange_support_chain_closed")
        is True
        and closeout.get("linkage_chain_count") == 4
        and linkage_ids
        == [
            "C_exchange_linkage",
            "total_conservation_linkage",
            "matter_sector_exchange_linkage",
            "gauge_sector_exchange_linkage",
        ]
        and closeout.get("new_proof_execution_in_closeout") is False
        and closeout.get("rule_promoted") is False
        and closeout.get("master_action_promoted") is False
    )


def build_psi_A_interaction_exchange_theorem_linkage_chain_closeout_result_review(
    *,
    closeout_path: Path = CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = _read_json(closeout_path)
    review_criteria = _review_criteria(closeout)
    acceptance_criteria = {
        "consumed_expected_closeout_packet": _closeout_valid(closeout),
        "closed_dependency_chain_preserved": (
            closeout.get("local_dependency_chain") == LOCAL_DEPENDENCY_CHAIN
            and closeout.get("C_exchange_linkage_conclusion")
            == C_EXCHANGE_LINKAGE_CONCLUSION
            and closeout.get("total_conservation_conclusion")
            == TOTAL_CONSERVATION_CONCLUSION
            and closeout.get("matter_sector_conclusion") == MATTER_SECTOR_CONCLUSION
            and closeout.get("gauge_sector_conclusion") == GAUGE_SECTOR_CONCLUSION
        ),
        "closeout_boundary_preserved": (
            closeout.get("general_C_k_closure") is False
            and closeout.get("gap_1_through_gap_8_discharged") is False
            and closeout.get("C_k_dynamical_law_status") is False
            and closeout.get("C_k_action_embedding_claimed") is False
            and closeout.get("C_k_action_variation_executed") is False
            and closeout.get("full_maxwell_closure_claimed") is False
            and closeout.get("em_qft_closure_claimed") is False
            and closeout.get("qft_gr_closure_claimed") is False
            and closeout.get("gr_qm_closure_claimed") is False
            and closeout.get("empirical_validation_claimed") is False
            and closeout.get("master_action_promoted") is False
        ),
        "no_new_proof_execution_in_review": (
            closeout.get("new_proof_execution_in_closeout") is False
            and closeout.get("proof_execution_authorized") is False
            and closeout.get("proof_attempt_executed") is False
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
        else "REMEDIATE_PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_"
            "RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_RESULT_REVIEW_BLOCKED",
        "review_result": REVIEW_RESULT
        if accepted
        else "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_RESULT_REVIEW_BLOCKED",
        "packet_result": OUTCOME_ID
        if accepted
        else "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_RESULT_REVIEW_BLOCKED",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if accepted else "remediation",
        "likely_next_obligation": LIKELY_NEXT_OBLIGATION,
        "suggested_selector_outcome": SUGGESTED_SELECTOR_OUTCOME,
        "strict_suggested_selector_outcome": STRICT_SUGGESTED_SELECTOR_OUTCOME,
        "closeout_schema_id": CLOSEOUT_SCHEMA_ID,
        "closeout_packet_id": CLOSEOUT_PACKET_ID,
        "closeout_outcome": CLOSEOUT_OUTCOME,
        "closeout_result": CLOSEOUT_RESULT,
        "strict_closeout_result": STRICT_CLOSEOUT_RESULT,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
        "boundary_nonclaims": BOUNDARY_NONCLAIMS,
        "claim_boundary": CLAIM_BOUNDARY,
        "closeout_claim_boundary": CLOSEOUT_CLAIM_BOUNDARY,
        "closeout_claims": CLOSEOUT_CLAIMS,
        "closeout_nonclaims": CLOSEOUT_NONCLAIMS,
        "plain_meaning": PLAIN_MEANING,
        "acceptance_criteria": acceptance_criteria,
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            row["status"] == "accepted" for row in review_criteria
        ),
        "local_dependency_chain": LOCAL_DEPENDENCY_CHAIN,
        "linkage_chain": closeout.get("linkage_chain", []),
        "linkage_chain_count": 4,
        "C_exchange_linkage_definition": C_EXCHANGE_LINKAGE_DEFINITION,
        "C_exchange_linkage_input": C_EXCHANGE_LINKAGE_INPUT,
        "C_exchange_linkage_conclusion": C_EXCHANGE_LINKAGE_CONCLUSION,
        "total_conservation_gauge_input": TOTAL_CONSERVATION_GAUGE_INPUT,
        "total_conservation_matter_input": TOTAL_CONSERVATION_MATTER_INPUT,
        "total_conservation_conclusion": TOTAL_CONSERVATION_CONCLUSION,
        "matter_sector_input_route": MATTER_SECTOR_INPUT_ROUTE,
        "matter_sector_conclusion": MATTER_SECTOR_CONCLUSION,
        "gauge_sector_input_route": GAUGE_SECTOR_INPUT_ROUTE,
        "gauge_stress_divergence_identity": GAUGE_STRESS_DIVERGENCE_IDENTITY,
        "sourced_maxwell_route": SOURCED_MAXWELL_ROUTE,
        "gauge_sector_conclusion": GAUGE_SECTOR_CONCLUSION,
        "local_psi_A_interaction_exchange_support_chain_closed": accepted,
        "C_exchange_linkage_included": accepted,
        "total_conservation_linkage_included": accepted,
        "matter_sector_exchange_linkage_included": accepted,
        "gauge_sector_exchange_linkage_included": accepted,
        "dependency_order_preserved": accepted,
        "closeout_boundary_preserved": accepted,
        "selector_target_authorized": accepted,
        "new_proof_execution_in_review": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "proof_debt_discharged": False,
        "rule_promoted": False,
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_REVIEW,
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
        "source_packet_report": _ptr(CLOSEOUT_PATH),
        "source_packet_evidence": _ptr(CLOSEOUT_LEAN_PACKET_PATH),
        "report_path": _ptr(DEFAULT_OUT),
        "lean_packet_path": _ptr(LEAN_PACKET_PATH),
        "qftgr_aggregate_path": _ptr(QFTGR_AGGREGATE_PATH),
        "current_target_aggregate_path": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
        "release_current_authority_aggregate_path": _ptr(
            RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
        ),
        "validation_policy": _validation_policy(),
    }
    payload.update(_blocked_boundary_flags())
    payload.update(_validation_policy())
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
            "Review the local psi-A interaction exchange theorem-linkage chain "
            "closeout result."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--closeout", type=Path, default=CLOSEOUT_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    closeout_path = (
        args.closeout if args.closeout.is_absolute() else REPO_ROOT / args.closeout
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_psi_A_interaction_exchange_theorem_linkage_chain_closeout_result_review(
        closeout_path=closeout_path,
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
                "general_C_k_theorem_linkage_closure": payload[
                    "general_C_k_theorem_linkage_closure"
                ],
                "rule_promoted": payload["rule_promoted"],
                "lean_status_wording": payload["lean_status_wording"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
