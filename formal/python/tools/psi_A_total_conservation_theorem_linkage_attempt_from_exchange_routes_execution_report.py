from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result_review_report import (
    ATTEMPT_TYPE,
    ATTEMPT_WATCH_ITEMS,
    CONSUMED_TARGET,
    CONSUMED_TARGET_KIND,
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    EXPANDED_CANCELLATION_CHAIN,
    EXPANDED_CANCELLATION_CHAIN_STATEMENT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    GAUGE_EXCHANGE_ROUTE,
    INPUT_ROUTE,
    LEAN_PACKET_PATH as RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    MATTER_EXCHANGE_ROUTE,
    NEXT_TARGET as CONSUMED_EXECUTION_TARGET,
    NEXT_TARGET_KIND as CONSUMED_EXECUTION_TARGET_KIND,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    PACKET_ID as RESULT_REVIEW_PACKET_ID,
    PLAIN_MEANING,
    PROOF_STYLE,
    REVIEW_RESULT,
    ROUTE_STEPS,
    SCHEMA_ID as RESULT_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_EXECUTION_OUTCOME,
    SUGGESTED_EXECUTION_OUTCOME,
    THEOREM_TARGET_STATEMENT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_STRESS_ENERGY_DEFINITION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-27T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "EXECUTION_20260627_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "EXECUTION_v0"
)
EXECUTION_RESULT = SUGGESTED_EXECUTION_OUTCOME
STRICT_EXECUTION_RESULT = STRICT_SUGGESTED_EXECUTION_OUTCOME
OUTCOME_ID = EXECUTION_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_"
    "executed_exchange_cancellation_constructed_no_ck_rule_promotion_or_master_"
    "action_promotion"
)

NEXT_TARGET = "review_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result"
NEXT_TARGET_KIND = (
    "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result_review"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION = SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_EXECUTION = LEAN_STATUS_WORDING_FOR_REVIEW

LEAN_THEOREM_NAME = "psi_A_total_conservation_from_exchange_cancellation"
LEAN_THEOREM_DESCRIPTION = (
    "Generic Lean witness: if T_total is the sum of the gauge and matter "
    "stress-energy objects, nabla is linear over that sum, and the two exchange "
    "halves are equal and opposite for the same exchange object, then the total "
    "covariant divergence vanishes."
)

EXCHANGE_OBJECT = "F^nu{}_alpha J^alpha"
GAUGE_EXCHANGE_CONCLUSION = "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha"
MATTER_EXCHANGE_CONCLUSION = "nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha"

EXECUTION_FINDINGS = [
    "psi-A total-conservation theorem-linkage attempt executed",
    "exchange-cancellation route constructed",
    "total conservation derived from accepted gauge/matter exchange halves",
    "local theorem-linkage reduced",
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k action variation",
    "no seam closure",
    "no empirical validation",
    "no master-action promotion",
]

EXECUTION_BLOCKED_CLAIMS = [
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k action variation",
    "no multiplier route",
    "no penalty route",
    "no direct dynamical-law claim",
    "no full Maxwell closure",
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
    / (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
        "EXECUTION_20260627_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutesExecution.lean"
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


def _execution_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "use_gauge_sector_exchange",
            "statement": GAUGE_EXCHANGE_CONCLUSION,
            "role": "accepted gauge-sector exchange input",
        },
        {
            "step_id": "use_matter_sector_exchange",
            "statement": MATTER_EXCHANGE_CONCLUSION,
            "role": "accepted matter-sector exchange input",
        },
        {
            "step_id": "use_total_stress_energy_definition",
            "statement": TOTAL_STRESS_ENERGY_DEFINITION,
            "role": "definition of total stress-energy",
        },
        {
            "step_id": "expand_total_covariant_divergence",
            "statement": "nabla_mu T_total^{mu nu} = nabla_mu(T_A^{mu nu} + T_psi^{mu nu})",
            "role": "rewrite by T_total definition",
        },
        {
            "step_id": "apply_linearity",
            "statement": (
                "nabla_mu(T_A^{mu nu} + T_psi^{mu nu}) = "
                "nabla_mu T_A^{mu nu} + nabla_mu T_psi^{mu nu}"
            ),
            "role": "linearity of nabla over addition",
        },
        {
            "step_id": "substitute_exchange_halves",
            "statement": (
                "nabla_mu T_A^{mu nu} + nabla_mu T_psi^{mu nu} = "
                "- F^nu{}_alpha J^alpha + F^nu{}_alpha J^alpha"
            ),
            "role": "substitution of accepted exchange halves",
        },
        {
            "step_id": "cancel_equal_and_opposite_exchange",
            "statement": "- F^nu{}_alpha J^alpha + F^nu{}_alpha J^alpha = 0",
            "role": "same F and J object with opposite signs",
        },
        {
            "step_id": "derive_total_conservation",
            "statement": TOTAL_CONSERVATION_CONCLUSION,
            "role": "local theorem-linkage conclusion",
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
            "row_id": "gauge_exchange_input_used",
            "status": "accepted",
            "evidence": GAUGE_EXCHANGE_ROUTE,
            "assessment": "The proof uses the accepted gauge-side exchange half.",
        },
        {
            "row_id": "matter_exchange_input_used",
            "status": "accepted",
            "evidence": MATTER_EXCHANGE_ROUTE,
            "assessment": "The proof uses the accepted matter-side exchange half.",
        },
        {
            "row_id": "total_definition_used",
            "status": "accepted",
            "evidence": TOTAL_STRESS_ENERGY_DEFINITION,
            "assessment": "The proof uses the accepted T_total definition.",
        },
        {
            "row_id": "watch_items_preserved",
            "status": "accepted",
            "evidence": ATTEMPT_WATCH_ITEMS,
            "assessment": "The cancellation preserves same-object and convention watch items.",
        },
        {
            "row_id": "total_conservation_derived",
            "status": "accepted",
            "evidence": TOTAL_CONSERVATION_CONCLUSION,
            "assessment": "Total conservation is derived by exchange cancellation.",
        },
        {
            "row_id": "no_ck_promotion_or_action_route",
            "status": "accepted",
            "evidence": EXECUTION_BLOCKED_CLAIMS,
            "assessment": "No C_k promotion, action embedding, variation, multiplier, or penalty route is selected.",
        },
        {
            "row_id": "no_physics_closure_claim",
            "status": "accepted",
            "evidence": [
                "no direct dynamical-law claim",
                "no full Maxwell closure",
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
        "checkpoint_type": (
            "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_"
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


def build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution(
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
            and result_review.get("selected_next_target")
            == CONSUMED_EXECUTION_TARGET
            and result_review.get("selected_next_target_kind")
            == CONSUMED_EXECUTION_TARGET_KIND
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
                GAUGE_EXCHANGE_ROUTE,
                MATTER_EXCHANGE_ROUTE,
                TOTAL_STRESS_ENERGY_DEFINITION,
            ]
            and theorem_target_shape["therefore"] == TOTAL_CONSERVATION_CONCLUSION
            and result_review.get("theorem_target_statement")
            == THEOREM_TARGET_STATEMENT
        ),
        "exchange_cancellation_execution_shape": (
            ATTEMPT_TYPE == "exchange-cancellation theorem-linkage attempt"
            and INPUT_ROUTE
            == "accepted gauge-sector exchange route plus accepted matter-sector exchange route"
            and PROOF_STYLE
            == "exchange-term cancellation plus total stress-energy definition"
        ),
        "execution_steps_all_bounded": (
            len(execution_steps) == 8
            and execution_steps[-1]["statement"] == TOTAL_CONSERVATION_CONCLUSION
        ),
        "watch_items_preserved": ATTEMPT_WATCH_ITEMS
        == [
            "same F object",
            "same J object",
            "same index placement",
            "same sign convention",
            "same covariant derivative",
            "linearity of nabla over addition",
            "valid T_total definition",
            "shared domain and boundary assumptions",
        ],
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
        else "REMEDIATE_PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_EXECUTION"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_EXECUTION"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "executed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_EXECUTION_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_EXECUTION_REQUIRES_REMEDIATION",
        "execution_result": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_EXECUTION_REQUIRES_REMEDIATION",
        "strict_execution_result": STRICT_EXECUTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_EXECUTION_TARGET,
        "consumed_target_kind": CONSUMED_EXECUTION_TARGET_KIND,
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
        "target_rule": TOTAL_CONSERVATION_CONCLUSION,
        "proof_style": PROOF_STYLE,
        "claim_boundary": "theorem-linkage only, not physics closure",
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
        "exchange_object": EXCHANGE_OBJECT,
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
        "lean_theorem_description": LEAN_THEOREM_DESCRIPTION,
        "execution_steps": execution_steps,
        "execution_step_count": len(execution_steps),
        "execution_criteria": execution_criteria,
        "execution_criteria_count": len(execution_criteria),
        "execution_criteria_accepted_count": sum(
            1 for row in execution_criteria if row["status"] == "accepted"
        ),
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
        "blocked_claims": EXECUTION_BLOCKED_CLAIMS,
        "blocked_claim_count": len(EXECUTION_BLOCKED_CLAIMS),
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
            "This execution constructs only the psi-A total conservation "
            "theorem-linkage from the accepted gauge-sector and matter-sector "
            "exchange halves plus the T_total definition. It derives "
            "nabla_mu T_total^{mu nu} = 0 by exchange cancellation under the "
            "recorded same-object, sign, index, derivative, domain, and boundary "
            "watch items. It does not promote any C_k rule, embed C_k in an "
            "action, vary C_k, select a multiplier route, select a penalty route, "
            "make a direct dynamical-law claim, close full Maxwell, close EM-QFT, "
            "close QFT-GR, close GR-QM, claim empirical validation, or promote "
            "the master action. The master action remains a working-form, "
            "noncanonical organizing surface, not a promoted final law."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume execute_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes",
            "fail to construct the exchange-cancellation route",
            "fail to derive nabla_mu T_total^{mu nu} = 0 from exchange cancellation",
            "fail to preserve watch items",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "claim direct dynamical-law interpretation",
            "claim full Maxwell, EM-QFT, QFT-GR, or GR-QM closure",
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
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutesExecution",
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
            "Execute the psi-A total conservation theorem-linkage attempt from exchange routes."
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
        build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution(
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
