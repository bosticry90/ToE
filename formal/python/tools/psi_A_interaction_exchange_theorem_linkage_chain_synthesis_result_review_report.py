from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_cexchange_total_matter_and_gauge_closeouts_report import (
    C_EXCHANGE_LINKAGE_CONCLUSION,
    C_EXCHANGE_LINKAGE_DEFINITION,
    C_EXCHANGE_LINKAGE_INPUT,
    CLAIM_BOUNDARY as SYNTHESIS_CLAIM_BOUNDARY,
    DEFAULT_OUT as SYNTHESIS_PACKET_PATH,
    GAUGE_SECTOR_CONCLUSION,
    GAUGE_SECTOR_INPUT_ROUTE,
    GAUGE_STRESS_DIVERGENCE_IDENTITY,
    LEAN_PACKET_PATH as SYNTHESIS_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_SYNTHESIS,
    LOCAL_DEPENDENCY_CHAIN,
    MATTER_SECTOR_CONCLUSION,
    MATTER_SECTOR_INPUT_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    NONCLAIMS as SYNTHESIS_NONCLAIMS,
    OUTCOME_ID as SYNTHESIS_PACKET_OUTCOME,
    PACKET_ID as SYNTHESIS_PACKET_ID,
    PACKET_RESULT as SYNTHESIS_PACKET_RESULT,
    PLAIN_MEANING,
    SCHEMA_ID as SYNTHESIS_PACKET_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_SYNTHESIS,
    SOURCED_MAXWELL_ROUTE,
    STRICT_PACKET_RESULT as SYNTHESIS_STRICT_PACKET_RESULT,
    SYNTHESIS_CLAIMS,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_CONSERVATION_GAUGE_INPUT,
    TOTAL_CONSERVATION_MATTER_INPUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SYNTHESIS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_RESULT_REVIEW_"
    "20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_RESULT_REVIEW_"
    "ACCEPTS_LOCAL_DEPENDENCY_CHAIN_SYNTHESIS_NO_CK_RULE_PROMOTION_OR_SEAM_CLOSURE"
)
STRICT_REVIEW_RESULT = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_RESULT_REVIEW_"
    "ACCEPTS_CEXCHANGE_TOTAL_MATTER_AND_GAUGE_LINKAGE_CHAIN_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_interaction_exchange_theorem_linkage_chain_synthesis_result_review_"
    "accepts_local_dependency_chain_synthesis_no_ck_rule_promotion_or_seam_closure"
)

NEXT_TARGET = "prepare_psi_A_interaction_exchange_theorem_linkage_chain_closeout"
NEXT_TARGET_KIND = "psi_A_interaction_exchange_theorem_linkage_chain_closeout_preparation"
CLOSEOUT_OUTCOME_HINT = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSED_AS_LOCAL_CEXCHANGE_"
    "TOTAL_MATTER_AND_GAUGE_DEPENDENCY_CHAIN_NO_CK_RULE_PROMOTION_OR_SEAM_CLOSURE"
)
LIKELY_SELECTOR_AFTER_CLOSEOUT = (
    "select_next_ck_family_theorem_linkage_obligation_after_psi_A_exchange_chain_closeout"
)

ACCEPTED_REVIEW_FINDINGS = [
    "C_exchange linkage included",
    "total-conservation linkage included",
    "matter-sector exchange linkage included",
    "gauge-sector exchange linkage included",
    "dependency order preserved",
    "all linkages remain local and bounded",
    "no new proof execution in the synthesis review",
    "no C_k rule promotion",
    "no action embedding",
    "no variation",
    "no seam closure",
    "no empirical validation",
    "no master-action promotion",
]
BOUNDARY_NONCLAIMS = [
    "no general C_k closure",
    "no GAP-1 through GAP-8 global discharge",
    "no C_k dynamical-law status",
    "no C_k action embedding",
    "no C_k action variation",
    "no multiplier route",
    "no penalty route",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no Standard Model derivation",
    "no empirical validation",
    "no master-action promotion",
]
CLAIM_BOUNDARY = (
    "synthesis result review only; accepts the local psi-A C_exchange, total, "
    "matter, and gauge dependency chain as bounded theorem-linkage architecture; "
    "no new proof execution, C_k promotion, seam closure, empirical validation, "
    "or master-action promotion"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SYNTHESIS
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_SYNTHESIS
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_SYNTHESIS

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_RESULT_REVIEW_20260628_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiAInteractionExchangeTheoremLinkageChainSynthesisResultReview.lean"
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
            "psi_A_interaction_exchange_theorem_linkage_chain_synthesis_result_review"
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


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "synthesis_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("packet_result"),
            "assessment": "The prepared local dependency-chain synthesis packet is consumed.",
        },
        {
            "row_id": "C_exchange_linkage_included",
            "status": "accepted",
            "evidence": C_EXCHANGE_LINKAGE_CONCLUSION,
            "assessment": "The C_exchange = 0 linkage from total conservation is included.",
        },
        {
            "row_id": "total_conservation_linkage_included",
            "status": "accepted",
            "evidence": TOTAL_CONSERVATION_CONCLUSION,
            "assessment": "The total-conservation linkage from the exchange halves is included.",
        },
        {
            "row_id": "matter_sector_exchange_linkage_included",
            "status": "accepted",
            "evidence": MATTER_SECTOR_CONCLUSION,
            "assessment": "The matter-sector exchange linkage from the Dirac-pair route is included.",
        },
        {
            "row_id": "gauge_sector_exchange_linkage_included",
            "status": "accepted",
            "evidence": GAUGE_SECTOR_CONCLUSION,
            "assessment": "The gauge-sector exchange linkage from stress divergence plus sourced Maxwell is included.",
        },
        {
            "row_id": "dependency_order_preserved",
            "status": "accepted",
            "evidence": LOCAL_DEPENDENCY_CHAIN,
            "assessment": "The dependency order is preserved.",
        },
        {
            "row_id": "no_new_proof_execution_or_promotion",
            "status": "accepted",
            "evidence": [
                "new_proof_execution_in_packet=false",
                "proof_execution_authorized=false",
                "rule_promoted=false",
                "master_action_promoted=false",
            ],
            "assessment": "The review executes no new proof and accepts no promotion claim.",
        },
        {
            "row_id": "closeout_preparation_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is the local chain closeout preparation.",
        },
    ]


def _packet_valid(packet: dict[str, Any]) -> bool:
    linkage_ids = [row.get("linkage_id") for row in packet.get("linkage_chain", [])]
    return (
        packet.get("schema_id") == SYNTHESIS_PACKET_SCHEMA_ID
        and packet.get("packet_id") == SYNTHESIS_PACKET_ID
        and packet.get("outcome_id") == SYNTHESIS_PACKET_OUTCOME
        and packet.get("packet_result") == SYNTHESIS_PACKET_RESULT
        and packet.get("strict_packet_result") == SYNTHESIS_STRICT_PACKET_RESULT
        and packet.get("selected_next_target") == CONSUMED_TARGET
        and packet.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and packet.get("accepted") is True
        and packet.get("synthesis_packet_prepared") is True
        and packet.get("linkage_chain_count") == 4
        and linkage_ids
        == [
            "C_exchange_linkage",
            "total_conservation_linkage",
            "matter_sector_exchange_linkage",
            "gauge_sector_exchange_linkage",
        ]
        and packet.get("new_proof_execution_in_packet") is False
        and packet.get("proof_execution_authorized") is False
        and packet.get("theorem_discharged") is False
        and packet.get("rule_promoted") is False
        and packet.get("master_action_promoted") is False
    )


def build_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_result_review(
    *,
    synthesis_packet_path: Path = SYNTHESIS_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(synthesis_packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_synthesis_packet": _packet_valid(packet),
        "local_linkage_chain_preserved": (
            packet.get("C_exchange_linkage_conclusion")
            == C_EXCHANGE_LINKAGE_CONCLUSION
            and packet.get("total_conservation_conclusion")
            == TOTAL_CONSERVATION_CONCLUSION
            and packet.get("matter_sector_conclusion") == MATTER_SECTOR_CONCLUSION
            and packet.get("gauge_sector_conclusion") == GAUGE_SECTOR_CONCLUSION
            and packet.get("local_dependency_chain") == LOCAL_DEPENDENCY_CHAIN
        ),
        "boundary_preserved": (
            packet.get("general_C_k_closure") is False
            and packet.get("C_k_dynamical_law_status") is False
            and packet.get("C_k_action_embedding_claimed") is False
            and packet.get("C_k_action_variation_executed") is False
            and packet.get("full_maxwell_closure_claimed") is False
            and packet.get("em_qft_closure_claimed") is False
            and packet.get("qft_gr_closure_claimed") is False
            and packet.get("gr_qm_closure_claimed") is False
            and packet.get("empirical_validation_claimed") is False
            and packet.get("master_action_promoted") is False
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
        else "REMEDIATE_PSI_A_INTERACTION_EXCHANGE_CHAIN_SYNTHESIS_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_"
            "RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID if accepted else "SYNTHESIS_RESULT_REVIEW_BLOCKED",
        "review_result": REVIEW_RESULT if accepted else "SYNTHESIS_RESULT_REVIEW_BLOCKED",
        "packet_result": OUTCOME_ID if accepted else "SYNTHESIS_RESULT_REVIEW_BLOCKED",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "synthesis_packet_outcome": SYNTHESIS_PACKET_OUTCOME,
        "synthesis_packet_result": SYNTHESIS_PACKET_RESULT,
        "synthesis_strict_packet_result": SYNTHESIS_STRICT_PACKET_RESULT,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if accepted else "remediation",
        "closeout_outcome_hint": CLOSEOUT_OUTCOME_HINT,
        "likely_selector_after_closeout": LIKELY_SELECTOR_AFTER_CLOSEOUT,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
        "boundary_nonclaims": BOUNDARY_NONCLAIMS,
        "claim_boundary": CLAIM_BOUNDARY,
        "synthesis_claim_boundary": SYNTHESIS_CLAIM_BOUNDARY,
        "synthesis_claims": SYNTHESIS_CLAIMS,
        "synthesis_nonclaims": SYNTHESIS_NONCLAIMS,
        "plain_meaning": PLAIN_MEANING,
        "acceptance_criteria": acceptance_criteria,
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            row["status"] == "accepted" for row in review_criteria
        ),
        "local_dependency_chain": LOCAL_DEPENDENCY_CHAIN,
        "linkage_chain": packet.get("linkage_chain", []),
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
        "C_exchange_linkage_included": accepted,
        "total_conservation_linkage_included": accepted,
        "matter_sector_exchange_linkage_included": accepted,
        "gauge_sector_exchange_linkage_included": accepted,
        "dependency_order_preserved": accepted,
        "all_linkages_remain_local_and_bounded": accepted,
        "local_dependency_chain_synthesis_accepted": accepted,
        "closeout_preparation_authorized": accepted,
        "closeout_prepared": False,
        "new_proof_execution_in_review": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_REVIEW,
        "full_toeformal_aggregate_status_for_review": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_review": SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
        "source_packet_report": _ptr(SYNTHESIS_PACKET_PATH),
        "source_packet_evidence": _ptr(SYNTHESIS_LEAN_PACKET_PATH),
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


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Review the psi-A interaction exchange theorem-linkage chain "
            "synthesis result."
        )
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=DEFAULT_OUT,
        help="Path for the generated result-review JSON.",
    )
    args = parser.parse_args()

    payload = build_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_result_review()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(args.out)


if __name__ == "__main__":
    main()
