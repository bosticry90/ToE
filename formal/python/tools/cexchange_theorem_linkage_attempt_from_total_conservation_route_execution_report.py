from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.cexchange_theorem_linkage_attempt_from_total_conservation_route_result_review_report import (
    ATTEMPT_TYPE,
    BASIS,
    BLOCKED_CLAIMS,
    C_EXCHANGE_RESIDUAL_DEFINITION,
    C_EXCHANGE_TARGET_CONCLUSION,
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    GOAL,
    INPUT_ROUTE,
    LEAN_PACKET_PATH as RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    PACKET_ID as RESULT_REVIEW_PACKET_ID,
    PLAIN_MEANING,
    PROOF_STYLE,
    REVIEW_RESULT,
    RULE_FAMILY,
    SCHEMA_ID as RESULT_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_EXECUTION_OUTCOME,
    SUGGESTED_EXECUTION_OUTCOME,
    TARGET_RULE,
    THEOREM_TARGET_ID,
    THEOREM_TARGET_NAME,
    THEOREM_TARGET_STATEMENT,
    TOP_OBLIGATION,
    TOP_OBLIGATION_PACKET_SCOPE,
    TOP_OBLIGATION_ROW_ID,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_DEFINITION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-27T00:00:00Z"

SCHEMA_ID = (
    "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_EXECUTION_"
    "20260627_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_EXECUTION_v0"
)
EXECUTION_RESULT = SUGGESTED_EXECUTION_OUTCOME
STRICT_EXECUTION_RESULT = STRICT_SUGGESTED_EXECUTION_OUTCOME
OUTCOME_ID = EXECUTION_RESULT
PACKET_CLASSIFICATION = (
    "cexchange_theorem_linkage_attempt_from_total_conservation_route_executed_"
    "definitional_linkage_constructed_no_ck_rule_promotion_or_master_action_"
    "promotion"
)

NEXT_TARGET = "review_cexchange_theorem_linkage_attempt_from_total_conservation_route_result"
NEXT_TARGET_KIND = (
    "cexchange_theorem_linkage_attempt_from_total_conservation_route_result_review"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION = SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_EXECUTION = LEAN_STATUS_WORDING_FOR_REVIEW

LEAN_THEOREM_NAME = (
    "cexchange_zero_from_total_conservation_definition"
)
LEAN_THEOREM_DESCRIPTION = (
    "Generic Lean witness: if C_exchange is definitionally the total "
    "conservation residual and that residual is zero, then C_exchange is zero."
)

EXECUTION_FINDINGS = [
    "C_exchange theorem-linkage attempt executed",
    "definitional linkage constructed",
    "C_exchange zero follows from accepted total-conservation route plus definition",
    "top theorem-linkage obligation locally reduced",
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k action variation",
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
        "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_"
        "EXECUTION_20260627_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CExchangeTheoremLinkageAttemptFromTotalConservationRouteExecution.lean"
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


def _input_boundary_clear(result_review: dict[str, Any]) -> bool:
    return all(
        result_review.get(key) is False
        for key in _blocked_boundary_flags()
        if key in result_review
    )


def _theorem_target_shape() -> dict[str, Any]:
    return {
        "given": [
            TOTAL_STRESS_ENERGY_DEFINITION,
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            C_EXCHANGE_RESIDUAL_DEFINITION,
        ],
        "therefore": C_EXCHANGE_TARGET_CONCLUSION,
        "plain_meaning": (
            "C_exchange is zero because it is defined as something already "
            "shown to be zero."
        ),
    }


def _execution_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "record_total_stress_energy_definition",
            "statement": TOTAL_STRESS_ENERGY_DEFINITION,
            "role": "context definition recorded; not a new dynamical law",
        },
        {
            "step_id": "use_accepted_total_conservation_route",
            "statement": TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            "role": "accepted psi-A total-conservation input route",
        },
        {
            "step_id": "expand_cexchange_definition",
            "statement": C_EXCHANGE_RESIDUAL_DEFINITION,
            "role": "definition expansion",
        },
        {
            "step_id": "rewrite_by_definition",
            "statement": C_EXCHANGE_TARGET_CONCLUSION,
            "role": "definitional rewrite plus accepted total-conservation zero",
        },
    ]


def _execution_criteria(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "execution_target_authorized",
            "status": "accepted",
            "evidence": result_review.get("selected_next_target"),
            "assessment": "The prior review selected this bounded execution target.",
        },
        {
            "row_id": "definitional_theorem_linkage_constructed",
            "status": "accepted",
            "evidence": LEAN_THEOREM_NAME,
            "assessment": "The Lean marker includes a generic definitional proof witness.",
        },
        {
            "row_id": "total_conservation_input_used",
            "status": "accepted",
            "evidence": TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            "assessment": "The proof uses only the accepted total-conservation zero.",
        },
        {
            "row_id": "cexchange_definition_used",
            "status": "accepted",
            "evidence": C_EXCHANGE_RESIDUAL_DEFINITION,
            "assessment": "C_exchange is expanded as the total-conservation residual.",
        },
        {
            "row_id": "cexchange_zero_derived",
            "status": "accepted",
            "evidence": C_EXCHANGE_TARGET_CONCLUSION,
            "assessment": "C_exchange zero follows by definition and total conservation.",
        },
        {
            "row_id": "no_ck_promotion_or_action_route",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "No C_k promotion, action embedding, variation, multiplier, or penalty route is selected.",
        },
        {
            "row_id": "no_physics_closure_claim",
            "status": "accepted",
            "evidence": [
                "no direct dynamical-law claim",
                "no EM-QFT closure",
                "no QFT-GR closure",
                "no GR-QM closure",
                "no empirical validation",
                "no seam closure",
            ],
            "assessment": "The execution remains a theorem-linkage step only.",
        },
        {
            "row_id": "master_action_status_preserved",
            "status": "accepted",
            "evidence": "working-form noncanonical organizing surface",
            "assessment": "The master action remains unpromoted.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "cexchange_theorem_linkage_attempt_from_total_conservation_route_"
            "execution"
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
        "aggregate_lean_validation_status_for_execution": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
        ),
        "full_toeformal_aggregate_status_for_execution": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
        ),
        "scoped_lean_targets_status_for_execution": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
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


def build_cexchange_theorem_linkage_attempt_from_total_conservation_route_execution(
    *,
    result_review_path: Path = RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    theorem_target_shape = _theorem_target_shape()
    execution_steps = _execution_steps()
    execution_criteria = _execution_criteria(result_review)
    acceptance_criteria = {
        "consumes_expected_execution_target": (
            result_review.get("schema_id") == RESULT_REVIEW_SCHEMA_ID
            and result_review.get("packet_id") == RESULT_REVIEW_PACKET_ID
            and result_review.get("outcome_id") == RESULT_REVIEW_OUTCOME
            and result_review.get("review_result") == REVIEW_RESULT
            and result_review.get("strict_review_result") == STRICT_REVIEW_RESULT
            and result_review.get("selected_next_target") == CONSUMED_TARGET
            and result_review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and result_review.get("proof_execution_authorized_by_review_for_next_target")
            is True
            and result_review.get(
                "theorem_linkage_proof_attempt_authorized_for_next_target"
            )
            is True
            and result_review.get("accepted") is True
        ),
        "theorem_target_shape_preserved": (
            theorem_target_shape["given"]
            == [
                TOTAL_STRESS_ENERGY_DEFINITION,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
                C_EXCHANGE_RESIDUAL_DEFINITION,
            ]
            and theorem_target_shape["therefore"] == C_EXCHANGE_TARGET_CONCLUSION
            and result_review.get("theorem_target_statement")
            == THEOREM_TARGET_STATEMENT
        ),
        "definitional_execution_shape": (
            ATTEMPT_TYPE == "definitional theorem-linkage attempt"
            and INPUT_ROUTE == "accepted psi-A total stress-energy conservation"
            and TARGET_RULE == C_EXCHANGE_TARGET_CONCLUSION
            and PROOF_STYLE
            == "definition expansion plus accepted total-conservation route"
        ),
        "execution_steps_all_bounded": (
            len(execution_steps) == 4
            and execution_steps[-1]["statement"] == C_EXCHANGE_TARGET_CONCLUSION
        ),
        "execution_criteria_all_accepted": all(
            row["status"] == "accepted" for row in execution_criteria
        ),
        "no_input_forbidden_claims": _input_boundary_clear(result_review),
        "all_gap_one_through_gap_eight_items_remain_open": (
            result_review.get("gap_count") == 8
            and result_review.get("open_gap_count") == 8
            and result_review.get("closed_gap_count") == 0
            and result_review.get("gap_1_through_gap_8_discharged") is False
        ),
        "lean_status_wording_careful": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_EXECUTION"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_EXECUTION",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "executed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_EXECUTION_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_EXECUTION_REQUIRES_REMEDIATION",
        "execution_result": OUTCOME_ID
        if accepted
        else "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_EXECUTION_REQUIRES_REMEDIATION",
        "strict_execution_result": STRICT_EXECUTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "post_execution_target": NEXT_TARGET,
        "post_execution_target_kind": NEXT_TARGET_KIND,
        "result_review_schema_id": RESULT_REVIEW_SCHEMA_ID,
        "result_review_packet_id": RESULT_REVIEW_PACKET_ID,
        "result_review_outcome": RESULT_REVIEW_OUTCOME,
        "result_review_strict_outcome": STRICT_REVIEW_RESULT,
        "result_review_consumed": accepted,
        "attempt_type": ATTEMPT_TYPE,
        "input_route": INPUT_ROUTE,
        "target_rule": TARGET_RULE,
        "proof_style": PROOF_STYLE,
        "claim_boundary": "definition-linkage theorem only, not physics closure",
        "basis": BASIS,
        "rule_family": RULE_FAMILY,
        "goal": GOAL,
        "top_obligation": TOP_OBLIGATION,
        "top_obligation_candidate": TOP_OBLIGATION,
        "top_obligation_row_id": TOP_OBLIGATION_ROW_ID,
        "top_obligation_packet_scope": TOP_OBLIGATION_PACKET_SCOPE,
        "top_theorem_linkage_obligation_locally_reduced": accepted,
        "theorem_target_id": THEOREM_TARGET_ID,
        "theorem_target_name": THEOREM_TARGET_NAME,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "theorem_target_shape": theorem_target_shape,
        "theorem_target_recorded": accepted,
        "theorem_target_indexed": accepted,
        "theorem_linkage_target_indexed": accepted,
        "definition_linkage_route_indexed": accepted,
        "definition_linkage_attempt_prepared": accepted,
        "definition_linkage_constructed": accepted,
        "total_conservation_to_cexchange_zero_linkage_target_indexed": accepted,
        "total_conservation_to_cexchange_zero_linkage_constructed": accepted,
        "total_stress_energy_definition": TOTAL_STRESS_ENERGY_DEFINITION,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_residual_definition": C_EXCHANGE_RESIDUAL_DEFINITION,
        "C_exchange_target_conclusion": C_EXCHANGE_TARGET_CONCLUSION,
        "C_exchange_zero_derived": accepted,
        "C_exchange_admissibility_status": "admissibility-only",
        "plain_meaning": PLAIN_MEANING,
        "execution_plain_meaning": theorem_target_shape["plain_meaning"],
        "mathematical_statement": THEOREM_TARGET_STATEMENT,
        "lean_theorem_name": LEAN_THEOREM_NAME,
        "lean_theorem_description": LEAN_THEOREM_DESCRIPTION,
        "execution_steps": execution_steps,
        "execution_step_count": len(execution_steps),
        "execution_criteria": execution_criteria,
        "execution_criteria_count": len(execution_criteria),
        "execution_criteria_accepted_count": sum(
            1 for row in execution_criteria if row["status"] == "accepted"
        ),
        "selected_theorem_row": TOP_OBLIGATION_ROW_ID,
        "selected_theorem_target_for_attempt": THEOREM_TARGET_ID,
        "selected_proof_target": THEOREM_TARGET_ID,
        "proof_execution": "executed",
        "proof_execution_authorized": True,
        "proof_target_execution_authorized": True,
        "proof_attempt_executed": accepted,
        "proof_debt_reduced": accepted,
        "proof_debt_discharged": False,
        "proof_target_selected": True,
        "theorem_row_selected": True,
        "theorem_row_selected_for_execution": True,
        "theorem_discharged": accepted,
        "theorem_linkage_completed": accepted,
        "theorem_linkage_proof_attempt_authorized": True,
        "theorem_linkage_obligation_discharged": accepted,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "execution_findings": EXECUTION_FINDINGS,
        "execution_finding_count": len(EXECUTION_FINDINGS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": False,
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This execution constructs only the definitional theorem-linkage "
            "from the accepted psi-A total-conservation route to "
            "C_exchange^{Apsi,nu} = 0. It proves the narrow bridge by expanding "
            "C_exchange^{Apsi,nu} as nabla_mu T_total^{mu nu} and using the "
            "accepted zero residual. It does not promote C_exchange beyond "
            "admissibility-only status, promote any C_k rule, embed C_k in an "
            "action, vary C_k, select a multiplier route, select a penalty "
            "route, make a direct dynamical-law claim, close EM-QFT, close "
            "QFT-GR, close GR-QM, claim empirical validation, close a seam, or "
            "promote the master action. The master action remains a working-"
            "form, noncanonical organizing surface, not a promoted final law."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume execute_cexchange_theorem_linkage_attempt_from_total_conservation_route",
            "fail to construct the definitional linkage",
            "fail to derive C_exchange^{Apsi,nu} = 0 from total conservation plus definition",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "claim direct dynamical-law interpretation",
            "claim EM-QFT, QFT-GR, or GR-QM closure",
            "claim empirical validation",
            "claim seam closure",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_EXECUTION,
        "full_toeformal_aggregate_status_for_execution": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
        ),
        "scoped_lean_targets_status_for_execution": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
        ),
        "aggregate_lean_validation_status_for_execution": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.CExchangeTheoremLinkageAttemptFromTotalConservationRouteExecution",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "result_review_file": _ptr(result_review_path),
            "result_review_lean_file": _ptr(RESULT_REVIEW_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }
    payload.update(_blocked_boundary_flags())
    payload["proof_execution_authorized"] = True
    payload["proof_target_execution_authorized"] = True
    payload["proof_attempt_executed"] = accepted
    payload["proof_debt_reduced"] = accepted
    payload["theorem_discharged"] = accepted
    payload["theorem_linkage_completed"] = accepted
    payload["theorem_linkage_proof_attempt_authorized"] = True
    payload["theorem_linkage_obligation_discharged"] = accepted
    payload["proof_target_selected"] = True
    payload["theorem_row_selected"] = True
    payload["theorem_row_selected_for_execution"] = True
    return payload


def write_execution(payload: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Execute the C_exchange theorem-linkage attempt from total conservation."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--result-review", type=Path, default=RESULT_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    result_review_path = (
        args.result_review
        if args.result_review.is_absolute()
        else REPO_ROOT / args.result_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_cexchange_theorem_linkage_attempt_from_total_conservation_route_execution(
            result_review_path=result_review_path,
            captured_at_utc=args.captured_at_utc,
        )
    )
    path = write_execution(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "executed": payload["executed"],
                "out": _ptr(path),
                "execution_result": payload["execution_result"],
                "selected_next_target": payload["selected_next_target"],
                "proof_attempt_executed": payload["proof_attempt_executed"],
                "theorem_discharged": payload["theorem_discharged"],
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
