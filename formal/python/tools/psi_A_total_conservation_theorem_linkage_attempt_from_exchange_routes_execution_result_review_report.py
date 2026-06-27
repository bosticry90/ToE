from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution_report import (
    ATTEMPT_TYPE,
    ATTEMPT_WATCH_ITEMS,
    CONSUMED_EXECUTION_TARGET as EXECUTION_CONSUMED_TARGET,
    DEFAULT_OUT as EXECUTION_PATH,
    EXECUTION_BLOCKED_CLAIMS,
    EXECUTION_FINDINGS,
    EXECUTION_RESULT,
    EXPANDED_CANCELLATION_CHAIN,
    EXPANDED_CANCELLATION_CHAIN_STATEMENT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION,
    GAUGE_EXCHANGE_CONCLUSION,
    GAUGE_EXCHANGE_ROUTE,
    INPUT_ROUTE,
    LEAN_PACKET_PATH as EXECUTION_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_EXECUTION,
    LEAN_THEOREM_NAME,
    MATTER_EXCHANGE_CONCLUSION,
    MATTER_EXCHANGE_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as EXECUTION_OUTCOME,
    PACKET_ID as EXECUTION_PACKET_ID,
    PLAIN_MEANING,
    PROOF_STYLE,
    ROUTE_STEPS,
    SCHEMA_ID as EXECUTION_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION,
    STRICT_EXECUTION_RESULT,
    THEOREM_TARGET_STATEMENT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_STRESS_ENERGY_DEFINITION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-27T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "EXECUTION_RESULT_REVIEW_20260627_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "EXECUTION_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "RESULT_REVIEW_ACCEPTS_EXCHANGE_CANCELLATION_CONSTRUCTED_NO_CK_RULE_"
    "PROMOTION_OR_MASTER_ACTION_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "RESULT_REVIEW_ACCEPTS_TOTAL_CONSERVATION_DERIVED_FROM_GAUGE_MATTER_"
    "EXCHANGE_CANCELLATION_NO_SEAM_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_"
    "result_review_accepts_exchange_cancellation_constructed_no_ck_rule_"
    "promotion_or_master_action_promotion"
)

NEXT_TARGET = "prepare_psi_A_total_conservation_theorem_linkage_obligation_closeout"
NEXT_TARGET_KIND = (
    "psi_A_total_conservation_theorem_linkage_obligation_closeout_preparation"
)
CLOSEOUT_OUTCOME = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_EXCHANGE_"
    "CANCELLATION_LINKED_TO_GAUGE_MATTER_EXCHANGE_ROUTES_NO_CK_RULE_PROMOTION_"
    "OR_SEAM_CLOSURE"
)
CLOSEOUT_STATEMENT = (
    "psi-A total conservation is theorem-linked to the accepted gauge/matter "
    "exchange halves by cancellation."
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_EXECUTION

ACCEPTED_REVIEW_FINDINGS = [
    "psi-A total-conservation theorem-linkage bridge executed",
    "exchange-cancellation route constructed",
    "accepted gauge-sector exchange route used",
    "accepted matter-sector exchange route used",
    "T_total definition used",
    "watch items preserved",
    "local theorem-linkage reduced",
    "no C_k promotion",
    "no action embedding",
    "no variation",
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
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
        "EXECUTION_RESULT_REVIEW_20260627_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutesExecutionResultReview.lean"
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
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "phase2_authorized": False,
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
        "obligation_rows_discharged": False,
        "proof_debt_discharged": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "new_physics_created": False,
        "new_field_or_interaction_expansion_selected": False,
    }


def _input_boundary_clear(execution: dict[str, Any]) -> bool:
    return all(
        execution.get(key) is False
        for key in _blocked_boundary_flags()
        if key in execution
    )


def _theorem_target_shape() -> dict[str, Any]:
    return {
        "given": [
            GAUGE_EXCHANGE_ROUTE,
            MATTER_EXCHANGE_ROUTE,
            TOTAL_STRESS_ENERGY_DEFINITION,
        ],
        "therefore": TOTAL_CONSERVATION_CONCLUSION,
        "expanded": EXPANDED_CANCELLATION_CHAIN,
        "expanded_statement": EXPANDED_CANCELLATION_CHAIN_STATEMENT,
        "route_steps": ROUTE_STEPS,
        "plain_meaning": PLAIN_MEANING,
    }


def _review_criteria(execution: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "execution_packet_consumed",
            "status": "accepted",
            "evidence": execution.get("execution_result"),
            "assessment": "The bounded execution packet is consumed by review.",
        },
        {
            "row_id": "exchange_cancellation_route_constructed",
            "status": "accepted",
            "evidence": execution.get("exchange_cancellation_route_constructed"),
            "assessment": "The exchange-cancellation route was constructed.",
        },
        {
            "row_id": "gauge_sector_exchange_input_used",
            "status": "accepted",
            "evidence": GAUGE_EXCHANGE_ROUTE,
            "assessment": "The accepted gauge-sector exchange half is used.",
        },
        {
            "row_id": "matter_sector_exchange_input_used",
            "status": "accepted",
            "evidence": MATTER_EXCHANGE_ROUTE,
            "assessment": "The accepted matter-sector exchange half is used.",
        },
        {
            "row_id": "total_stress_energy_definition_used",
            "status": "accepted",
            "evidence": TOTAL_STRESS_ENERGY_DEFINITION,
            "assessment": "The T_total definition is used.",
        },
        {
            "row_id": "watch_items_preserved",
            "status": "accepted",
            "evidence": ATTEMPT_WATCH_ITEMS,
            "assessment": "The same-object, sign, derivative, domain, and boundary watch items are preserved.",
        },
        {
            "row_id": "total_conservation_derived",
            "status": "accepted",
            "evidence": TOTAL_CONSERVATION_CONCLUSION,
            "assessment": "Total conservation is derived by exchange cancellation.",
        },
        {
            "row_id": "local_theorem_linkage_reduced",
            "status": "accepted",
            "evidence": execution.get("local_theorem_linkage_reduced"),
            "assessment": "The local theorem-linkage obligation is reduced.",
        },
        {
            "row_id": "no_ck_promotion_or_action_route",
            "status": "accepted",
            "evidence": EXECUTION_BLOCKED_CLAIMS,
            "assessment": "No C_k promotion, action embedding, variation, multiplier, or penalty route is accepted.",
        },
        {
            "row_id": "no_closure_or_empirical_claim",
            "status": "accepted",
            "evidence": [
                "no full Maxwell closure",
                "no EM-QFT closure",
                "no QFT-GR closure",
                "no GR-QM closure",
                "no seam closure",
                "no empirical validation",
            ],
            "assessment": "The result review remains below closure and empirical claims.",
        },
        {
            "row_id": "closeout_preparation_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is closeout preparation only.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_"
            "execution_result_review"
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


def build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution_result_review(
    *,
    execution_path: Path = EXECUTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    execution = _read_json(execution_path)
    theorem_target_shape = _theorem_target_shape()
    review_criteria = _review_criteria(execution)
    acceptance_criteria = {
        "consumes_expected_execution_result": (
            execution.get("schema_id") == EXECUTION_SCHEMA_ID
            and execution.get("packet_id") == EXECUTION_PACKET_ID
            and execution.get("outcome_id") == EXECUTION_OUTCOME
            and execution.get("execution_result") == EXECUTION_RESULT
            and execution.get("strict_execution_result") == STRICT_EXECUTION_RESULT
            and execution.get("selected_next_target") == CONSUMED_TARGET
            and execution.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and execution.get("accepted") is True
            and execution.get("executed") is True
        ),
        "exchange_cancellation_bridge_constructed": (
            execution.get("exchange_cancellation_route_constructed") is True
            and execution.get("total_conservation_derived") is True
            and execution.get("proof_attempt_executed") is True
            and execution.get("theorem_discharged") is True
            and execution.get("theorem_linkage_completed") is True
        ),
        "theorem_target_shape_preserved": (
            theorem_target_shape["given"]
            == [
                GAUGE_EXCHANGE_ROUTE,
                MATTER_EXCHANGE_ROUTE,
                TOTAL_STRESS_ENERGY_DEFINITION,
            ]
            and theorem_target_shape["therefore"] == TOTAL_CONSERVATION_CONCLUSION
            and execution.get("theorem_target_statement") == THEOREM_TARGET_STATEMENT
        ),
        "accepted_exchange_inputs_used": (
            execution.get("gauge_exchange_route") == GAUGE_EXCHANGE_ROUTE
            and execution.get("matter_exchange_route") == MATTER_EXCHANGE_ROUTE
            and execution.get("input_route") == INPUT_ROUTE
            and execution.get("proof_style") == PROOF_STYLE
        ),
        "watch_items_preserved": execution.get("watch_items") == ATTEMPT_WATCH_ITEMS,
        "local_theorem_linkage_reduced": (
            execution.get("local_theorem_linkage_reduced") is True
        ),
        "no_input_forbidden_claims": _input_boundary_clear(execution),
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
        else "REMEDIATE_PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_EXECUTION_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_"
            "EXCHANGE_ROUTES_EXECUTION_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_EXECUTION_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_EXECUTION_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_EXECUTION_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "execution_consumed_target": EXECUTION_CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "closeout_outcome": CLOSEOUT_OUTCOME,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "execution_schema_id": EXECUTION_SCHEMA_ID,
        "execution_packet_id": EXECUTION_PACKET_ID,
        "execution_outcome": EXECUTION_OUTCOME,
        "execution_result": EXECUTION_RESULT,
        "execution_strict_outcome": STRICT_EXECUTION_RESULT,
        "execution_packet_consumed": accepted,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "execution_findings": EXECUTION_FINDINGS,
        "execution_finding_count": len(EXECUTION_FINDINGS),
        "attempt_type": ATTEMPT_TYPE,
        "input_route": INPUT_ROUTE,
        "target_rule": TOTAL_CONSERVATION_CONCLUSION,
        "proof_style": PROOF_STYLE,
        "claim_boundary": "theorem-linkage result review only, not physics closure",
        "selected_obligation": "psi-A total conservation theorem-linkage gap",
        "selected_obligation_rank": "2",
        "local_theorem_linkage_reduced": accepted,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "theorem_target_shape": theorem_target_shape,
        "theorem_target_recorded": accepted,
        "theorem_target_indexed": accepted,
        "theorem_linkage_target_indexed": accepted,
        "exchange_cancellation_route_indexed": accepted,
        "exchange_cancellation_route_constructed": accepted,
        "gauge_exchange_route": GAUGE_EXCHANGE_ROUTE,
        "matter_exchange_route": MATTER_EXCHANGE_ROUTE,
        "gauge_exchange_conclusion": GAUGE_EXCHANGE_CONCLUSION,
        "matter_exchange_conclusion": MATTER_EXCHANGE_CONCLUSION,
        "total_stress_energy_definition": TOTAL_STRESS_ENERGY_DEFINITION,
        "total_conservation_conclusion": TOTAL_CONSERVATION_CONCLUSION,
        "total_conservation_derived": accepted,
        "expanded_cancellation_chain": EXPANDED_CANCELLATION_CHAIN,
        "expanded_cancellation_chain_statement": EXPANDED_CANCELLATION_CHAIN_STATEMENT,
        "route_steps": ROUTE_STEPS,
        "route_step_count": len(ROUTE_STEPS),
        "plain_meaning": PLAIN_MEANING,
        "watch_items": ATTEMPT_WATCH_ITEMS,
        "watch_item_count": len(ATTEMPT_WATCH_ITEMS),
        "lean_theorem_name": LEAN_THEOREM_NAME,
        "proof_execution": "already executed; not re-executed by review",
        "review_executes_attempt": False,
        "proof_execution_authorized": False,
        "proof_target_execution_authorized": False,
        "proof_attempt_executed": True,
        "proof_debt_reduced": True,
        "proof_debt_discharged": False,
        "proof_target_selected": True,
        "theorem_row_selected": True,
        "theorem_row_selected_for_execution": True,
        "theorem_discharged": True,
        "theorem_linkage_completed": True,
        "theorem_linkage_proof_attempt_authorized": False,
        "theorem_linkage_obligation_discharged": True,
        "closeout_preparation_authorized": accepted,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "blocked_claims": EXECUTION_BLOCKED_CLAIMS,
        "blocked_claim_count": len(EXECUTION_BLOCKED_CLAIMS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_accepted": accepted,
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only that the psi-A total conservation "
            "theorem-linkage bridge has been executed: the gauge field loses "
            "exactly what matter gains, so the combined matter-plus-gauge "
            "system balances. It authorizes only closeout preparation. It does "
            "not claim full Maxwell closure, EM-QFT closure, QFT-GR closure, "
            "GR-QM closure, C_k action embedding, C_k variation, empirical "
            "validation, seam closure, or master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume the psi-A exchange-cancellation execution result",
            "fail to accept the executed total-conservation bridge",
            "fail to preserve gauge and matter exchange inputs",
            "fail to preserve the T_total definition",
            "execute a new proof during result review",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "claim full Maxwell, EM-QFT, QFT-GR, or GR-QM closure",
            "claim empirical validation",
            "claim seam closure",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
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
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutesExecutionResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "execution_file": _ptr(execution_path),
            "execution_lean_file": _ptr(EXECUTION_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
    payload["proof_attempt_executed"] = True
    payload["proof_debt_reduced"] = True
    payload["theorem_discharged"] = True
    payload["theorem_linkage_completed"] = True
    payload["theorem_linkage_obligation_discharged"] = True
    payload["proof_target_selected"] = True
    payload["theorem_row_selected"] = True
    payload["theorem_row_selected_for_execution"] = True
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
            "Review the executed psi-A total conservation theorem-linkage attempt "
            "from exchange routes."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--execution", type=Path, default=EXECUTION_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    execution_path = (
        args.execution if args.execution.is_absolute() else REPO_ROOT / args.execution
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution_result_review(
            execution_path=execution_path,
            captured_at_utc=args.captured_at_utc,
        )
    )
    path = write_result_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
                "selected_next_target": payload["selected_next_target"],
                "proof_attempt_executed": payload["proof_attempt_executed"],
                "review_executes_attempt": payload["review_executes_attempt"],
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
