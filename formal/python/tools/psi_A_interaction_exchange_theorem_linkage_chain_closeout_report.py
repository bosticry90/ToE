from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_interaction_exchange_theorem_linkage_chain_synthesis_result_review_report import (
    C_EXCHANGE_LINKAGE_CONCLUSION,
    C_EXCHANGE_LINKAGE_DEFINITION,
    C_EXCHANGE_LINKAGE_INPUT,
    CLAIM_BOUNDARY as REVIEW_CLAIM_BOUNDARY,
    CLOSEOUT_OUTCOME_HINT,
    DEFAULT_OUT as SYNTHESIS_RESULT_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    GAUGE_SECTOR_CONCLUSION,
    GAUGE_SECTOR_INPUT_ROUTE,
    GAUGE_STRESS_DIVERGENCE_IDENTITY,
    LEAN_PACKET_PATH as SYNTHESIS_RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LOCAL_DEPENDENCY_CHAIN,
    MATTER_SECTOR_CONCLUSION,
    MATTER_SECTOR_INPUT_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as SYNTHESIS_RESULT_REVIEW_OUTCOME,
    PACKET_ID as SYNTHESIS_RESULT_REVIEW_PACKET_ID,
    PLAIN_MEANING as SYNTHESIS_PLAIN_MEANING,
    REVIEW_RESULT as SYNTHESIS_RESULT_REVIEW_RESULT,
    SCHEMA_ID as SYNTHESIS_RESULT_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SOURCED_MAXWELL_ROUTE,
    STRICT_REVIEW_RESULT as SYNTHESIS_RESULT_REVIEW_STRICT_OUTCOME,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_CONSERVATION_GAUGE_INPUT,
    TOTAL_CONSERVATION_MATTER_INPUT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_20260628_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_v0"
CLOSEOUT_RESULT = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSED_AS_LOCAL_CEXCHANGE_"
    "TOTAL_MATTER_AND_GAUGE_DEPENDENCY_CHAIN_NO_CK_RULE_PROMOTION_OR_SEAM_CLOSURE"
)
STRICT_CLOSEOUT_RESULT = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSED_AS_LOCAL_EXCHANGE_"
    "BALANCE_SUPPORT_CHAIN_NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_interaction_exchange_theorem_linkage_chain_closed_as_local_cexchange_"
    "total_matter_and_gauge_dependency_chain_no_ck_rule_promotion_or_seam_closure"
)

NEXT_TARGET = "review_psi_A_interaction_exchange_theorem_linkage_chain_closeout_result"
NEXT_TARGET_KIND = "psi_A_interaction_exchange_theorem_linkage_chain_closeout_result_review"
SUGGESTED_REVIEW_OUTCOME = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_RESULT_REVIEW_"
    "ACCEPTS_LOCAL_CEXCHANGE_TOTAL_MATTER_AND_GAUGE_DEPENDENCY_CHAIN_NO_CK_RULE_"
    "PROMOTION_OR_SEAM_CLOSURE"
)
LIKELY_SELECTOR_AFTER_REVIEW = (
    "select_next_ck_family_theorem_linkage_obligation_after_psi_A_exchange_chain_"
    "closeout"
)

PLAIN_MEANING = (
    "Matter gains what gauge loses. The combined system conserves. C_exchange "
    "records that conserved balance."
)
CLAIM_BOUNDARY = (
    "local psi-A interaction exchange theorem-linkage chain closeout only; "
    "no new proof execution, general C_k closure, C_k rule promotion, seam "
    "closure, empirical validation, or master-action promotion"
)
CLOSEOUT_STATEMENT = (
    "The local psi-A interaction exchange support chain is closed in dependency "
    "order: C_exchange = 0 depends on total conservation; total conservation "
    "depends on the matter-sector and gauge-sector exchange halves; the matter "
    "half depends on the Dirac-pair route; and the gauge half depends on the "
    "stress-divergence identity plus sourced Maxwell route."
)

CLOSEOUT_CLAIMS = [
    "C_exchange linkage locally closed",
    "total-conservation linkage locally closed",
    "matter-sector exchange linkage locally closed",
    "gauge-sector exchange linkage locally closed",
    "dependency order synthesized and accepted",
    "local psi-A interaction exchange support chain closed",
    "no new proof execution in closeout",
]
NONCLAIMS = [
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

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT = SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_CLOSEOUT = LEAN_STATUS_WORDING_FOR_REVIEW

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_20260628_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiAInteractionExchangeTheoremLinkageChainCloseout.lean"
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
            "psi_A_interaction_exchange_theorem_linkage_chain_closeout"
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
        "full_toeformal_aggregate_status_for_closeout": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
        ),
        "scoped_lean_targets_status_for_closeout": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
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


def _review_valid(review: dict[str, Any]) -> bool:
    linkage_ids = [row.get("linkage_id") for row in review.get("linkage_chain", [])]
    return (
        review.get("schema_id") == SYNTHESIS_RESULT_REVIEW_SCHEMA_ID
        and review.get("packet_id") == SYNTHESIS_RESULT_REVIEW_PACKET_ID
        and review.get("outcome_id") == SYNTHESIS_RESULT_REVIEW_OUTCOME
        and review.get("review_result") == SYNTHESIS_RESULT_REVIEW_RESULT
        and review.get("strict_review_result") == SYNTHESIS_RESULT_REVIEW_STRICT_OUTCOME
        and review.get("selected_next_target") == CONSUMED_TARGET
        and review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and review.get("closeout_outcome_hint") == CLOSEOUT_OUTCOME_HINT
        and review.get("accepted") is True
        and review.get("reviewed") is True
        and review.get("local_dependency_chain_synthesis_accepted") is True
        and review.get("linkage_chain_count") == 4
        and linkage_ids
        == [
            "C_exchange_linkage",
            "total_conservation_linkage",
            "matter_sector_exchange_linkage",
            "gauge_sector_exchange_linkage",
        ]
        and review.get("new_proof_execution_in_review") is False
        and review.get("rule_promoted") is False
        and review.get("master_action_promoted") is False
    )


def build_psi_A_interaction_exchange_theorem_linkage_chain_closeout(
    *,
    synthesis_result_review_path: Path = SYNTHESIS_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(synthesis_result_review_path)
    acceptance_criteria = {
        "consumed_expected_synthesis_result_review": _review_valid(review),
        "dependency_chain_preserved": (
            review.get("local_dependency_chain") == LOCAL_DEPENDENCY_CHAIN
            and review.get("C_exchange_linkage_conclusion")
            == C_EXCHANGE_LINKAGE_CONCLUSION
            and review.get("total_conservation_conclusion")
            == TOTAL_CONSERVATION_CONCLUSION
            and review.get("matter_sector_conclusion") == MATTER_SECTOR_CONCLUSION
            and review.get("gauge_sector_conclusion") == GAUGE_SECTOR_CONCLUSION
        ),
        "closeout_is_local_and_bounded": (
            review.get("general_C_k_closure") is False
            and review.get("gap_1_through_gap_8_discharged") is False
            and review.get("C_k_dynamical_law_status") is False
            and review.get("C_k_action_embedding_claimed") is False
            and review.get("C_k_action_variation_executed") is False
            and review.get("full_maxwell_closure_claimed") is False
            and review.get("em_qft_closure_claimed") is False
            and review.get("qft_gr_closure_claimed") is False
            and review.get("gr_qm_closure_claimed") is False
            and review.get("empirical_validation_claimed") is False
            and review.get("master_action_promoted") is False
        ),
        "no_new_proof_execution": (
            review.get("new_proof_execution_in_review") is False
            and review.get("proof_execution_authorized") is False
            and review.get("proof_attempt_executed") is False
        ),
        "lean_status_wording_careful": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "closed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_REQUIRES_REMEDIATION",
        "closeout_result": OUTCOME_ID
        if accepted
        else "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_CLOSEOUT_REQUIRES_REMEDIATION",
        "strict_closeout_result": STRICT_CLOSEOUT_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "suggested_review_outcome": SUGGESTED_REVIEW_OUTCOME,
        "likely_selector_after_review": LIKELY_SELECTOR_AFTER_REVIEW,
        "synthesis_result_review_schema_id": SYNTHESIS_RESULT_REVIEW_SCHEMA_ID,
        "synthesis_result_review_packet_id": SYNTHESIS_RESULT_REVIEW_PACKET_ID,
        "synthesis_result_review_outcome": SYNTHESIS_RESULT_REVIEW_OUTCOME,
        "synthesis_result_review_strict_outcome": (
            SYNTHESIS_RESULT_REVIEW_STRICT_OUTCOME
        ),
        "synthesis_result_review_consumed": accepted,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "closeout_claims": CLOSEOUT_CLAIMS,
        "closeout_claim_count": len(CLOSEOUT_CLAIMS),
        "nonclaims": NONCLAIMS,
        "nonclaim_count": len(NONCLAIMS),
        "claim_boundary": CLAIM_BOUNDARY,
        "review_claim_boundary": REVIEW_CLAIM_BOUNDARY,
        "plain_meaning": PLAIN_MEANING,
        "synthesis_plain_meaning": SYNTHESIS_PLAIN_MEANING,
        "local_dependency_chain": LOCAL_DEPENDENCY_CHAIN,
        "local_dependency_chain_step_count": len(LOCAL_DEPENDENCY_CHAIN),
        "linkage_chain": review.get("linkage_chain", []),
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
        "C_exchange_linkage_locally_closed": accepted,
        "total_conservation_linkage_locally_closed": accepted,
        "matter_sector_exchange_linkage_locally_closed": accepted,
        "gauge_sector_exchange_linkage_locally_closed": accepted,
        "dependency_order_synthesized_and_accepted": accepted,
        "local_psi_A_interaction_exchange_support_chain_closed": accepted,
        "all_linkages_remain_local_and_bounded": accepted,
        "closeout_executes_new_proof": False,
        "new_proof_execution_in_closeout": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_linkage_chain_closed": accepted,
        "theorem_linkage_obligation_discharged": accepted,
        "proof_debt_reduced": accepted,
        "proof_debt_discharged": False,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "blocked_claims": NONCLAIMS,
        "blocked_claim_count": len(NONCLAIMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This closeout records only the local psi-A interaction exchange "
            "support chain: C_exchange = 0 from total conservation, total "
            "conservation from equal-and-opposite matter/gauge exchange, "
            "matter exchange from the Dirac-pair route, and gauge exchange "
            "from stress-divergence plus sourced Maxwell. It does not claim "
            "general C_k closure, GAP-1 through GAP-8 global discharge, C_k "
            "dynamical-law status, C_k action embedding or variation, full "
            "Maxwell closure, EM-QFT closure, QFT-GR closure, GR-QM closure, "
            "empirical validation, seam closure, or master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_psi_A_interaction_exchange_theorem_linkage_chain_closeout",
            "fail to close the local psi-A interaction exchange support chain",
            "fail to preserve the C_exchange linkage",
            "fail to preserve the total-conservation linkage",
            "fail to preserve the matter-sector exchange linkage",
            "fail to preserve the gauge-sector exchange linkage",
            "claim general C_k closure",
            "discharge GAP-1 through GAP-8 globally",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "claim full Maxwell closure",
            "claim EM-QFT, QFT-GR, or GR-QM closure",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_CLOSEOUT,
        "full_toeformal_aggregate_status_for_closeout": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
        ),
        "scoped_lean_targets_status_for_closeout": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
        ),
        "aggregate_lean_validation_status_for_closeout": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PsiAInteractionExchangeTheoremLinkageChainCloseout",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "synthesis_result_review_file": _ptr(synthesis_result_review_path),
            "synthesis_result_review_lean_file": _ptr(
                SYNTHESIS_RESULT_REVIEW_LEAN_PACKET_PATH
            ),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
    payload["C_exchange_linkage_locally_closed"] = accepted
    payload["total_conservation_linkage_locally_closed"] = accepted
    payload["matter_sector_exchange_linkage_locally_closed"] = accepted
    payload["gauge_sector_exchange_linkage_locally_closed"] = accepted
    payload["dependency_order_synthesized_and_accepted"] = accepted
    payload["local_psi_A_interaction_exchange_support_chain_closed"] = accepted
    payload["all_linkages_remain_local_and_bounded"] = accepted
    payload["theorem_linkage_chain_closed"] = accepted
    payload["theorem_linkage_obligation_discharged"] = accepted
    payload["proof_debt_reduced"] = accepted
    payload["proof_debt_discharged"] = False
    return payload


def write_closeout(closeout: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(closeout, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Close out the local psi-A interaction exchange theorem-linkage "
            "support chain."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--review", type=Path, default=SYNTHESIS_RESULT_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = args.review if args.review.is_absolute() else REPO_ROOT / args.review
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_psi_A_interaction_exchange_theorem_linkage_chain_closeout(
        synthesis_result_review_path=review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_closeout(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "closeout_result": payload["closeout_result"],
                "selected_next_target": payload["selected_next_target"],
                "local_psi_A_interaction_exchange_support_chain_closed": payload[
                    "local_psi_A_interaction_exchange_support_chain_closed"
                ],
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
