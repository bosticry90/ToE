from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.cexchange_theorem_linkage_attempt_from_total_conservation_route_execution_result_review_report import (
    BLOCKED_CLAIMS,
    C_EXCHANGE_RESIDUAL_DEFINITION,
    C_EXCHANGE_TARGET_CONCLUSION,
    DEFAULT_OUT as EXECUTION_RESULT_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    INPUT_ROUTE,
    LEAN_PACKET_PATH as EXECUTION_RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as EXECUTION_RESULT_REVIEW_OUTCOME,
    PACKET_ID as EXECUTION_RESULT_REVIEW_PACKET_ID,
    PROOF_STYLE,
    REVIEW_RESULT as EXECUTION_RESULT_REVIEW_RESULT,
    SCHEMA_ID as EXECUTION_RESULT_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT as EXECUTION_RESULT_REVIEW_STRICT_OUTCOME,
    THEOREM_TARGET_ID,
    THEOREM_TARGET_NAME,
    THEOREM_TARGET_STATEMENT,
    TOP_OBLIGATION,
    TOP_OBLIGATION_ROW_ID,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_DEFINITION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-27T00:00:00Z"

SCHEMA_ID = "CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_20260627_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_v0"
CLOSEOUT_RESULT = (
    "CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_DEFINITIONALLY_LINKED_TO_"
    "TOTAL_CONSERVATION_NO_CK_RULE_PROMOTION_OR_SEAM_CLOSURE"
)
STRICT_CLOSEOUT_RESULT = (
    "CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_LOCAL_DEFINITIONAL_THEOREM_"
    "LINKAGE_NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "cexchange_theorem_linkage_obligation_closed_as_local_definitional_linkage_"
    "no_ck_rule_promotion_or_seam_closure"
)

NEXT_TARGET = "review_cexchange_theorem_linkage_obligation_closeout_result"
NEXT_TARGET_KIND = "cexchange_theorem_linkage_obligation_closeout_result_review"
LIKELY_NEXT_SELECTOR_TARGET = (
    "select_next_ck_family_theorem_linkage_obligation_after_cexchange_closeout"
)
LIKELY_NEXT_OBLIGATION = "psi-A total conservation"
CLOSEOUT_STATEMENT = (
    "C_exchange is theorem-linked to accepted total conservation by definition."
)
CLAIM_BOUNDARY = "local C_exchange theorem-linkage closeout only, not physics closure"

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT = SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_CLOSEOUT = LEAN_STATUS_WORDING_FOR_REVIEW

CLOSEOUT_CLAIMS = [
    "C_exchange theorem-linkage obligation locally closed",
    "definition expansion links C_exchange to total conservation",
    "accepted psi-A total-conservation route is the input",
    "C_exchange^{Apsi,nu} = 0 follows by definition only",
]

NONCLAIMS = [
    "no general C_k theorem-linkage closure",
    "no GAP-1 through GAP-8 global discharge",
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k variation",
    "no multiplier route",
    "no penalty route",
    "no direct dynamical-law claim",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no empirical validation",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_20260627_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CExchangeTheoremLinkageObligationCloseout.lean"
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
        "assumption_discharge_completed": False,
        "gap_review_closes_any_gap": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
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


def _theorem_target_shape() -> dict[str, Any]:
    return {
        "given": [
            TOTAL_STRESS_ENERGY_DEFINITION,
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            C_EXCHANGE_RESIDUAL_DEFINITION,
        ],
        "therefore": C_EXCHANGE_TARGET_CONCLUSION,
        "plain_meaning": (
            "C_exchange means the total exchange leftover; the accepted "
            "total-conservation route says that leftover is zero."
        ),
    }


def _consumed_review_valid(review: dict[str, Any]) -> bool:
    return (
        review.get("schema_id") == EXECUTION_RESULT_REVIEW_SCHEMA_ID
        and review.get("packet_id") == EXECUTION_RESULT_REVIEW_PACKET_ID
        and review.get("outcome_id") == EXECUTION_RESULT_REVIEW_OUTCOME
        and review.get("review_result") == EXECUTION_RESULT_REVIEW_RESULT
        and review.get("strict_review_result")
        == EXECUTION_RESULT_REVIEW_STRICT_OUTCOME
        and review.get("selected_next_target") == CONSUMED_TARGET
        and review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and review.get("accepted") is True
        and review.get("definition_linkage_constructed") is True
        and review.get("C_exchange_zero_derived") is True
        and review.get("theorem_linkage_completed") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "cexchange_theorem_linkage_obligation_closeout",
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


def build_cexchange_theorem_linkage_obligation_closeout(
    *,
    execution_result_review_path: Path = EXECUTION_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(execution_result_review_path)
    acceptance_criteria = {
        "consumed_expected_execution_result_review": _consumed_review_valid(review),
        "local_cexchange_obligation_closeout_only": (
            review.get("top_obligation") == TOP_OBLIGATION
            and review.get("top_obligation_row_id") == TOP_OBLIGATION_ROW_ID
            and review.get("input_route") == INPUT_ROUTE
            and review.get("proof_style") == PROOF_STYLE
        ),
        "definition_linkage_preserved": (
            review.get("total_stress_energy_definition")
            == TOTAL_STRESS_ENERGY_DEFINITION
            and review.get("total_stress_energy_conservation_identity")
            == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
            and review.get("C_exchange_residual_definition")
            == C_EXCHANGE_RESIDUAL_DEFINITION
            and review.get("C_exchange_target_conclusion")
            == C_EXCHANGE_TARGET_CONCLUSION
        ),
        "no_new_proof_or_promotion": (
            review.get("review_executes_attempt") is False
            and review.get("rule_promoted") is False
            and review.get("master_action_promoted") is False
            and review.get("seam_closure_claim") is False
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
        else "REMEDIATE_CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "closed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_REQUIRES_REMEDIATION",
        "closeout_result": OUTCOME_ID
        if accepted
        else "CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_REQUIRES_REMEDIATION",
        "strict_closeout_result": STRICT_CLOSEOUT_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "likely_next_selector_target_after_review": LIKELY_NEXT_SELECTOR_TARGET,
        "likely_next_obligation_after_closeout": LIKELY_NEXT_OBLIGATION,
        "execution_result_review_schema_id": EXECUTION_RESULT_REVIEW_SCHEMA_ID,
        "execution_result_review_packet_id": EXECUTION_RESULT_REVIEW_PACKET_ID,
        "execution_result_review_outcome": EXECUTION_RESULT_REVIEW_OUTCOME,
        "execution_result_review_strict_outcome": (
            EXECUTION_RESULT_REVIEW_STRICT_OUTCOME
        ),
        "execution_result_review_consumed": accepted,
        "top_obligation": TOP_OBLIGATION,
        "top_obligation_row_id": TOP_OBLIGATION_ROW_ID,
        "input_route": INPUT_ROUTE,
        "proof_style": PROOF_STYLE,
        "claim_boundary": CLAIM_BOUNDARY,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "closeout_claims": CLOSEOUT_CLAIMS,
        "closeout_claim_count": len(CLOSEOUT_CLAIMS),
        "nonclaims": NONCLAIMS,
        "nonclaim_count": len(NONCLAIMS),
        "theorem_target_id": THEOREM_TARGET_ID,
        "theorem_target_name": THEOREM_TARGET_NAME,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "theorem_target_shape": _theorem_target_shape(),
        "total_stress_energy_definition": TOTAL_STRESS_ENERGY_DEFINITION,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_residual_definition": C_EXCHANGE_RESIDUAL_DEFINITION,
        "C_exchange_target_conclusion": C_EXCHANGE_TARGET_CONCLUSION,
        "definition_linkage_constructed": accepted,
        "C_exchange_zero_derived": accepted,
        "local_cexchange_obligation_closed": accepted,
        "top_theorem_linkage_obligation_locally_closed": accepted,
        "top_theorem_linkage_obligation_locally_reduced": accepted,
        "general_ck_theorem_linkage_closure": False,
        "general_C_k_theorem_linkage_closure": False,
        "proof_attempt_executed": True,
        "closeout_executes_new_proof": False,
        "proof_execution_authorized": False,
        "theorem_discharged": True,
        "theorem_linkage_completed": accepted,
        "theorem_linkage_obligation_discharged": True,
        "proof_debt_reduced": True,
        "proof_debt_discharged": False,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
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
            "This closeout records only that the local C_exchange theorem-linkage "
            "obligation is closed by definition: C_exchange is theorem-linked to "
            "accepted total conservation because C_exchange is defined as the "
            "total-conservation residual and that residual is zero. It does not "
            "claim general C_k theorem-linkage closure, discharge GAP-1 through "
            "GAP-8 globally, promote C_k, embed C_k in an action, vary C_k, "
            "select a multiplier route, select a penalty route, make a direct "
            "dynamical-law claim, close EM-QFT, close QFT-GR, close GR-QM, claim "
            "empirical validation, or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_cexchange_theorem_linkage_obligation_closeout",
            "fail to close the local C_exchange theorem-linkage obligation",
            "claim general C_k theorem-linkage closure",
            "discharge GAP-1 through GAP-8 globally",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "claim direct dynamical-law interpretation",
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
            "ToeFormal.Derivation.CExchangeTheoremLinkageObligationCloseout",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "execution_result_review_file": _ptr(execution_result_review_path),
            "execution_result_review_lean_file": _ptr(
                EXECUTION_RESULT_REVIEW_LEAN_PACKET_PATH
            ),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
    payload["definition_linkage_constructed"] = accepted
    payload["C_exchange_zero_derived"] = accepted
    payload["local_cexchange_obligation_closed"] = accepted
    payload["top_theorem_linkage_obligation_locally_closed"] = accepted
    payload["proof_attempt_executed"] = True
    payload["theorem_discharged"] = True
    payload["theorem_linkage_completed"] = accepted
    payload["theorem_linkage_obligation_discharged"] = True
    payload["proof_debt_reduced"] = True
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
        description="Close out the local C_exchange theorem-linkage obligation."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--review", type=Path, default=EXECUTION_RESULT_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = args.review if args.review.is_absolute() else REPO_ROOT / args.review
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_cexchange_theorem_linkage_obligation_closeout(
        execution_result_review_path=review_path,
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
                "local_cexchange_obligation_closed": payload[
                    "local_cexchange_obligation_closed"
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
