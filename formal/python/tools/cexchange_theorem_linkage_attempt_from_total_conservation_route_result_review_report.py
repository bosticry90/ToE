from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.cexchange_theorem_linkage_attempt_from_total_conservation_route_report import (
    ATTEMPT_TYPE,
    BASIS,
    BLOCKED_CLAIMS,
    C_EXCHANGE_RESIDUAL_DEFINITION,
    C_EXCHANGE_TARGET_CONCLUSION,
    CLAIM_BOUNDARY,
    DEFAULT_OUT as ATTEMPT_PACKET_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    GOAL,
    INPUT_ROUTE,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as ATTEMPT_PACKET_OUTCOME,
    PACKET_ID as ATTEMPT_PACKET_ID,
    PLAIN_MEANING,
    PROOF_STYLE,
    RULE_FAMILY,
    SCHEMA_ID as ATTEMPT_PACKET_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_PACKET_RESULT as ATTEMPT_STRICT_PACKET_RESULT,
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
    "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_RESULT_"
    "REVIEW_20260627_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_RESULT_"
    "REVIEW_v0"
)
REVIEW_RESULT = (
    "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_RESULT_REVIEW_"
    "ACCEPTS_DEFINITIONAL_LINKAGE_ROUTE_PREPARATION_NO_THEOREM_DISCHARGE_OR_"
    "CK_RULE_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_RESULT_REVIEW_"
    "ACCEPTS_PREPARED_TOTAL_CONSERVATION_TO_CEXCHANGE_ZERO_LINKAGE_TARGET_NO_"
    "ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "cexchange_theorem_linkage_attempt_from_total_conservation_route_result_"
    "review_accepts_definitional_linkage_route_preparation_no_theorem_discharge_"
    "or_ck_rule_promotion"
)

NEXT_TARGET = "execute_cexchange_theorem_linkage_attempt_from_total_conservation_route"
NEXT_TARGET_KIND = "cexchange_theorem_linkage_attempt_from_total_conservation_route_execution"
SUGGESTED_EXECUTION_OUTCOME = (
    "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_EXECUTED_"
    "DEFINITIONAL_LINKAGE_CONSTRUCTED_NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_PROMOTION"
)
STRICT_SUGGESTED_EXECUTION_OUTCOME = (
    "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_EXECUTED_"
    "CEXCHANGE_ZERO_DERIVED_FROM_TOTAL_CONSERVATION_DEFINITION_ONLY_NO_SEAM_CLOSURE"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_PACKET

ACCEPTED_REVIEW_FINDINGS = [
    "C_exchange theorem-linkage attempt prepared",
    "target theorem shape recorded",
    "input route is accepted psi-A total conservation",
    "proof style is definitional linkage",
    "no theorem execution",
    "no theorem discharge",
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
        "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_RESULT_"
        "REVIEW_20260627_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CExchangeTheoremLinkageAttemptFromTotalConservationRouteResultReview.lean"
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
        "theorem_linkage_obligation_discharged": False,
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
        "proof_target_execution_authorized": False,
        "proof_execution_authorized": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "new_physics_created": False,
        "new_field_or_interaction_expansion_selected": False,
    }


def _input_boundary_clear(packet: dict[str, Any]) -> bool:
    return all(
        packet.get(key) is False
        for key in _false_boundary_flags()
        if key in packet
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
            "If C_exchange means the leftover total exchange, and the total "
            "exchange leftover is zero, then C_exchange is zero."
        ),
    }


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The prepared definitional linkage route is accepted for the "
                "next bounded execution target. This review does not execute "
                "or discharge the theorem."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The result-review target is consumed by this checkpoint.",
        },
        {
            "target": "promote_cexchange_to_ck_rule",
            "decision": "not_authorized",
            "reason": "The review accepts theorem-linkage preparation only.",
        },
        {
            "target": "embed_cexchange_in_master_action",
            "decision": "not_authorized",
            "reason": "No C_k action embedding or master-action promotion is authorized.",
        },
        {
            "target": "claim_em_qft_closure",
            "decision": "not_authorized",
            "reason": "The review does not claim EM-QFT closure.",
        },
    ]


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    theorem_target_shape = _theorem_target_shape()
    return [
        {
            "row_id": "attempt_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("packet_result"),
            "assessment": "The C_exchange theorem-linkage attempt packet is consumed by review.",
        },
        {
            "row_id": "cexchange_attempt_prepared",
            "status": "accepted",
            "evidence": packet.get("attempt_preparation_packet_prepared"),
            "assessment": "The attempt was prepared only, with no proof execution.",
        },
        {
            "row_id": "target_theorem_shape_recorded",
            "status": "accepted",
            "evidence": theorem_target_shape,
            "assessment": "The exact total-conservation to C_exchange zero target is recorded.",
        },
        {
            "row_id": "accepted_total_conservation_input_route",
            "status": "accepted",
            "evidence": packet.get("input_route"),
            "assessment": "The input route is accepted psi-A total conservation.",
        },
        {
            "row_id": "definitional_linkage_proof_style",
            "status": "accepted",
            "evidence": packet.get("proof_style"),
            "assessment": "The proof style is definitional linkage.",
        },
        {
            "row_id": "no_theorem_execution_or_discharge",
            "status": "accepted",
            "evidence": {
                "proof_attempt_executed": packet.get("proof_attempt_executed"),
                "theorem_discharged": packet.get("theorem_discharged"),
            },
            "assessment": "The review executes no theorem and discharges no theorem.",
        },
        {
            "row_id": "no_ck_promotion_or_action_route",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "No C_k promotion, action embedding, variation, multiplier, or penalty route is accepted.",
        },
        {
            "row_id": "no_seam_or_empirical_closure",
            "status": "accepted",
            "evidence": [
                "no seam closure",
                "no empirical validation",
                "no EM-QFT closure",
                "no QFT-GR closure",
                "no GR-QM closure",
            ],
            "assessment": "The review remains below physics closure claims.",
        },
        {
            "row_id": "master_action_status_preserved",
            "status": "accepted",
            "evidence": "working-form noncanonical organizing surface",
            "assessment": "The master action remains unpromoted.",
        },
        {
            "row_id": "lean_status_wording_preserved",
            "status": "accepted",
            "evidence": LEAN_STATUS_WORDING_FOR_REVIEW,
            "assessment": "The review records scoped Lean pass and no full aggregate pass.",
        },
        {
            "row_id": "execution_target_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next live target is the bounded definitional linkage execution attempt.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "cexchange_theorem_linkage_attempt_from_total_conservation_route_"
            "result_review"
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
        "aggregate_lean_validation_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
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


def build_cexchange_theorem_linkage_attempt_from_total_conservation_route_result_review(
    *,
    packet_path: Path = ATTEMPT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    theorem_target_shape = _theorem_target_shape()
    candidate_next_targets = _candidate_next_targets()
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_attempt_result_review_target": (
            packet.get("schema_id") == ATTEMPT_PACKET_SCHEMA_ID
            and packet.get("packet_id") == ATTEMPT_PACKET_ID
            and packet.get("outcome_id") == ATTEMPT_PACKET_OUTCOME
            and packet.get("packet_result") == ATTEMPT_PACKET_OUTCOME
            and packet.get("strict_packet_result") == ATTEMPT_STRICT_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and packet.get("accepted") is True
        ),
        "attempt_preparation_accepted": (
            packet.get("attempt_preparation_packet_prepared") is True
            and packet.get("definition_linkage_attempt_prepared") is True
            and packet.get("definition_linkage_route_indexed") is True
        ),
        "theorem_target_shape_recorded": (
            theorem_target_shape["given"]
            == [
                TOTAL_STRESS_ENERGY_DEFINITION,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
                C_EXCHANGE_RESIDUAL_DEFINITION,
            ]
            and theorem_target_shape["therefore"] == C_EXCHANGE_TARGET_CONCLUSION
            and packet.get("theorem_target_statement") == THEOREM_TARGET_STATEMENT
        ),
        "accepted_total_conservation_input_route": (
            packet.get("input_route") == INPUT_ROUTE
            and packet.get("basis") == BASIS
            and packet.get("goal") == GOAL
        ),
        "definitional_linkage_proof_style": (
            packet.get("attempt_type") == ATTEMPT_TYPE
            and packet.get("proof_style") == PROOF_STYLE
            and packet.get("claim_boundary") == CLAIM_BOUNDARY
        ),
        "selected_target_preserved": (
            packet.get("target_rule") == TARGET_RULE
            and packet.get("selected_proof_target") == THEOREM_TARGET_ID
            and packet.get("selected_theorem_row") == TOP_OBLIGATION_ROW_ID
        ),
        "review_does_not_execute_or_discharge": (
            packet.get("proof_execution_authorized") is False
            and packet.get("proof_attempt_executed") is False
            and packet.get("theorem_discharged") is False
            and packet.get("theorem_linkage_completed") is False
            and packet.get("rule_promoted") is False
        ),
        "all_gaps_remain_open": (
            packet.get("gap_count") == 8
            and packet.get("open_gap_count") == 8
            and packet.get("closed_gap_count") == 0
            and packet.get("gap_1_through_gap_8_discharged") is False
        ),
        "no_input_forbidden_claims": _input_boundary_clear(packet),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "exactly_one_next_execution_target_selected": (
            sum(1 for row in candidate_next_targets if row["decision"] == "selected")
            == 1
            and candidate_next_targets[0]["target"] == NEXT_TARGET
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
        else "REMEDIATE_CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "post_review_target": NEXT_TARGET,
        "post_review_target_kind": NEXT_TARGET_KIND,
        "suggested_execution_outcome": SUGGESTED_EXECUTION_OUTCOME,
        "strict_suggested_execution_outcome": STRICT_SUGGESTED_EXECUTION_OUTCOME,
        "attempt_packet_schema_id": ATTEMPT_PACKET_SCHEMA_ID,
        "attempt_packet_id": ATTEMPT_PACKET_ID,
        "attempt_packet_outcome": ATTEMPT_PACKET_OUTCOME,
        "attempt_packet_strict_outcome": ATTEMPT_STRICT_PACKET_RESULT,
        "attempt_packet_consumed": accepted,
        "C_exchange_theorem_linkage_attempt_prepared": accepted,
        "target_theorem_shape_recorded": accepted,
        "input_route_is_accepted_psi_A_total_conservation": accepted,
        "proof_style_is_definitional_linkage": accepted,
        "execution_target_selected_after_review": accepted,
        "review_does_not_execute_theorem": accepted,
        "top_obligation": TOP_OBLIGATION,
        "top_obligation_candidate": TOP_OBLIGATION,
        "top_obligation_row_id": TOP_OBLIGATION_ROW_ID,
        "top_obligation_packet_scope": TOP_OBLIGATION_PACKET_SCOPE,
        "top_obligation_packet_prepared": accepted,
        "top_obligation_packet_reviewed": accepted,
        "attempt_type": ATTEMPT_TYPE,
        "input_route": INPUT_ROUTE,
        "target_rule": TARGET_RULE,
        "proof_style": PROOF_STYLE,
        "claim_boundary": CLAIM_BOUNDARY,
        "basis": BASIS,
        "rule_family": RULE_FAMILY,
        "goal": GOAL,
        "theorem_target_id": THEOREM_TARGET_ID,
        "theorem_target_name": THEOREM_TARGET_NAME,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "theorem_target_shape": theorem_target_shape,
        "theorem_target_recorded": accepted,
        "theorem_target_indexed": accepted,
        "theorem_linkage_target_indexed": accepted,
        "definition_linkage_route_indexed": accepted,
        "definition_linkage_attempt_prepared": accepted,
        "total_conservation_to_cexchange_zero_linkage_target_indexed": accepted,
        "total_stress_energy_definition": TOTAL_STRESS_ENERGY_DEFINITION,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_residual_definition": C_EXCHANGE_RESIDUAL_DEFINITION,
        "C_exchange_target_conclusion": C_EXCHANGE_TARGET_CONCLUSION,
        "plain_meaning": PLAIN_MEANING,
        "review_plain_meaning": theorem_target_shape["plain_meaning"],
        "mathematical_statement": THEOREM_TARGET_STATEMENT,
        "selected_theorem_row": TOP_OBLIGATION_ROW_ID,
        "selected_theorem_target_for_attempt": THEOREM_TARGET_ID,
        "selected_proof_target": THEOREM_TARGET_ID,
        "proof_execution": "not yet",
        "proof_execution_authorized": False,
        "proof_execution_authorized_by_review_for_next_target": accepted,
        "proof_target_execution_authorized": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "proof_target_selected": True,
        "theorem_row_selected": True,
        "theorem_row_selected_for_execution": True,
        "theorem_discharged": False,
        "theorem_linkage_completed": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "theorem_linkage_proof_attempt_authorized_for_next_target": accepted,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "candidate_next_targets": candidate_next_targets,
        "candidate_next_target_count": len(candidate_next_targets),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": accepted,
        "attempt_result_review_accepted": accepted,
        "attempt_preparation_packet_reviewed": accepted,
        "attempt_execution_target_authorized": accepted,
        "attempt_execution_authorized_as_next_target": accepted,
        "attempt_execution_authorized_after_review_only": accepted,
        "review_executes_attempt": False,
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only that the C_exchange theorem-linkage "
            "attempt from total conservation has been prepared. It records the "
            "target shape: given T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}, "
            "nabla_mu T_total^{mu nu} = 0, and C_exchange^{Apsi,nu} := "
            "nabla_mu T_total^{mu nu}, therefore C_exchange^{Apsi,nu} = 0. "
            "It confirms the input route is accepted psi-A total conservation "
            "and the proof style is definitional linkage. It selects the "
            "bounded execution attempt as the next target, but this review does "
            "not execute the theorem, discharge the theorem, promote any C_k "
            "rule, embed C_k in an action, vary C_k, select a multiplier route, "
            "select a penalty route, make a direct dynamical-law claim, close "
            "any seam, close EM-QFT, close QFT-GR, close GR-QM, claim empirical "
            "validation, or promote the master action. The master action "
            "remains a working-form, noncanonical organizing surface, not a "
            "promoted final law."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_cexchange_theorem_linkage_attempt_from_total_conservation_route_result",
            "fail to accept prepared C_exchange theorem-linkage attempt",
            "fail to preserve the total-conservation to C_exchange zero theorem shape",
            "fail to record accepted psi-A total conservation as input route",
            "fail to record definitional linkage as proof style",
            "execute a theorem during review",
            "discharge the theorem during review",
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
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.CExchangeTheoremLinkageAttemptFromTotalConservationRouteResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "attempt_packet_file": _ptr(packet_path),
            "attempt_packet_lean_file": _ptr(ATTEMPT_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }
    payload.update(_false_boundary_flags())
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
            "Review the C_exchange theorem-linkage attempt preparation result."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--packet", type=Path, default=ATTEMPT_PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    packet_path = args.packet if args.packet.is_absolute() else REPO_ROOT / args.packet
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_cexchange_theorem_linkage_attempt_from_total_conservation_route_result_review(
            packet_path=packet_path,
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
                "theorem_discharged": payload["theorem_discharged"],
                "lean_status_wording": payload["lean_status_wording"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
