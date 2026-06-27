from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_theorem_linkage_priority_selection_after_index_result_review_report import (
    BLOCKED_CLAIMS,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CLASSIFICATION,
    C_EXCHANGE_CONSTRAINT_FORM,
    DEFAULT_OUT as PRIORITY_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH as PRIORITY_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as PRIORITY_REVIEW_OUTCOME,
    PACKET_ID as PRIORITY_REVIEW_PACKET_ID,
    PRIORITY_CRITERIA,
    RANKED_ROW_IDS,
    SCHEMA_ID as PRIORITY_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    TOP_OBLIGATION_CANDIDATE,
    TOP_OBLIGATION_PACKET_PLAIN_MEANING as PRIORITY_REVIEW_TOP_SCOPE_MEANING,
    TOP_OBLIGATION_PACKET_SCOPE,
    TOP_OBLIGATION_ROW_ID,
)
from formal.python.tools.toe_native_psi_a_u1_total_stress_energy_conservation_route_result_review_report import (
    DEFAULT_OUT as TOTAL_CONSERVATION_REVIEW_PATH,
    OUTCOME_ID as TOTAL_CONSERVATION_REVIEW_OUTCOME,
    PACKET_ID as TOTAL_CONSERVATION_REVIEW_PACKET_ID,
    SCHEMA_ID as TOTAL_CONSERVATION_REVIEW_SCHEMA_ID,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-27T00:00:00Z"

SCHEMA_ID = "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_20260627_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_v0"
PACKET_RESULT = (
    "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_CEXCHANGE_"
    "THEOREM_LINKAGE_OBLIGATION_SCOPED_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
STRICT_PACKET_RESULT = (
    "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_CEXCHANGE_FROM_"
    "TOTAL_CONSERVATION_THEOREM_TARGET_INDEXED_NO_ACTION_VARIATION_OR_MASTER_"
    "ACTION_PROMOTION"
)
OUTCOME_ID = PACKET_RESULT
PACKET_CLASSIFICATION = (
    "ck_family_top_theorem_linkage_obligation_packet_prepared_cexchange_"
    "theorem_linkage_obligation_scoped_no_proof_execution_or_ck_rule_promotion"
)

NEXT_TARGET = "review_ck_family_top_theorem_linkage_obligation_packet_result"
NEXT_TARGET_KIND = "ck_family_top_theorem_linkage_obligation_packet_result_review"
LIKELY_FOLLOW_ON_TARGET = (
    "prepare_cexchange_theorem_linkage_attempt_from_total_conservation_route"
)
LIKELY_FOLLOW_ON_TARGET_KIND = (
    "cexchange_theorem_linkage_attempt_from_total_conservation_route_preparation"
)

TOP_OBLIGATION = "C_exchange theorem-linkage gap"
BASIS = "accepted psi-A total-conservation route"
RULE_FAMILY = "interaction exchange-balance admissibility"
GOAL = "theorem-link C_exchange to total conservation"
PROOF_EXECUTION_STATUS = "not yet"
RULE_PROMOTION_STATUS = "not authorized"

TOTAL_STRESS_ENERGY_DEFINITION = "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}"
C_EXCHANGE_RESIDUAL_DEFINITION = (
    "C_exchange^{Apsi,nu} := nabla_mu T_total^{mu nu}"
)
C_EXCHANGE_TARGET_CONCLUSION = "C_exchange^{Apsi,nu} = 0"
THEOREM_TARGET_ID = "cexchange_from_total_conservation"
THEOREM_TARGET_NAME = (
    "C_exchange theorem-linkage from accepted total conservation"
)
THEOREM_TARGET_STATEMENT = (
    "Given T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}, "
    "nabla_mu T_total^{mu nu} = 0, and "
    "C_exchange^{Apsi,nu} := nabla_mu T_total^{mu nu}, then "
    "C_exchange^{Apsi,nu} = 0."
)
PLAIN_MEANING = (
    "If total matter-plus-gauge energy-momentum is conserved, and C_exchange "
    "is defined as the total-conservation residual, then C_exchange vanishes."
)

SELECTED_PROOF_TARGET = "NONE_SELECTED"
SELECTED_THEOREM_ROW = TOP_OBLIGATION_ROW_ID
SELECTED_THEOREM_TARGET_FOR_ATTEMPT = THEOREM_TARGET_ID

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET = SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_PACKET = LEAN_STATUS_WORDING

ACCEPTED_PACKET_FINDINGS = [
    "top obligation: C_exchange theorem-linkage gap",
    "basis: accepted psi-A total-conservation route",
    "rule family: interaction exchange-balance admissibility",
    "goal: theorem-link C_exchange to total conservation",
    "theorem target indexed",
    "proof execution: not yet",
    "rule promotion: not authorized",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_20260627_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CKFamilyTopTheoremLinkageObligationPacket.lean"
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


def _input_boundary_clear(*payloads: dict[str, Any]) -> bool:
    for payload in payloads:
        for key, expected in _false_boundary_flags().items():
            if key in payload and payload.get(key) is not expected:
                return False
    return True


def _theorem_target_rows() -> list[dict[str, Any]]:
    return [
        {
            "row_id": THEOREM_TARGET_ID,
            "target_name": THEOREM_TARGET_NAME,
            "top_obligation": TOP_OBLIGATION,
            "basis": BASIS,
            "rule_family": RULE_FAMILY,
            "goal": GOAL,
            "given": [
                TOTAL_STRESS_ENERGY_DEFINITION,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
                C_EXCHANGE_RESIDUAL_DEFINITION,
            ],
            "then": C_EXCHANGE_TARGET_CONCLUSION,
            "plain_meaning": PLAIN_MEANING,
            "proof_execution": PROOF_EXECUTION_STATUS,
            "theorem_discharged": False,
            "rule_promotion": RULE_PROMOTION_STATUS,
            "selected_for_attempt_now": False,
            "prepared_for_result_review": True,
        }
    ]


def _packet_criteria(
    priority_review: dict[str, Any],
    total_review: dict[str, Any],
) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "top_obligation_packet_target_consumed",
            "status": "accepted",
            "evidence": priority_review.get("selected_next_target"),
            "assessment": "The packet consumes the live top-obligation preparation target.",
        },
        {
            "row_id": "cexchange_top_obligation_preserved",
            "status": "accepted",
            "evidence": {
                "candidate": priority_review.get("top_obligation_candidate"),
                "row_id": priority_review.get("top_obligation_row_id"),
            },
            "assessment": "C_exchange remains the top theorem-linkage obligation.",
        },
        {
            "row_id": "accepted_total_conservation_route_basis",
            "status": "accepted",
            "evidence": total_review.get("outcome_id"),
            "assessment": "The theorem target is based on the accepted psi-A total-conservation route.",
        },
        {
            "row_id": "total_stress_energy_definition_recorded",
            "status": "accepted",
            "evidence": TOTAL_STRESS_ENERGY_DEFINITION,
            "assessment": "The theorem target preserves T_total = T_A + T_psi.",
        },
        {
            "row_id": "total_conservation_assumption_recorded",
            "status": "accepted",
            "evidence": TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            "assessment": "The theorem target preserves nabla_mu T_total^{mu nu} = 0.",
        },
        {
            "row_id": "cexchange_residual_definition_recorded",
            "status": "accepted",
            "evidence": C_EXCHANGE_RESIDUAL_DEFINITION,
            "assessment": "The target defines C_exchange as the total-conservation residual.",
        },
        {
            "row_id": "cexchange_vanishing_target_indexed",
            "status": "accepted",
            "evidence": C_EXCHANGE_TARGET_CONCLUSION,
            "assessment": "The theorem-linkage target conclusion is indexed but not proved.",
        },
        {
            "row_id": "no_proof_execution_or_discharge",
            "status": "accepted",
            "evidence": {
                "proof_execution": PROOF_EXECUTION_STATUS,
                "theorem_discharged": False,
            },
            "assessment": "The packet prepares the target only and executes no proof.",
        },
        {
            "row_id": "no_ck_promotion_or_action_route",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "No C_k promotion, action embedding, variation, multiplier, or penalty route is authorized.",
        },
        {
            "row_id": "claim_ladder_boundary_preserved",
            "status": "accepted",
            "evidence": [
                "below seam closure",
                "below empirical prediction",
                "below empirical confirmation",
                "below mature physical theory",
            ],
            "assessment": "The packet remains below closure, validation, and mature theory claims.",
        },
        {
            "row_id": "next_result_review_target_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The immediate next target is packet result review.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "ck_family_top_theorem_linkage_obligation_packet",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
        ),
        "full_toeformal_aggregate_status_for_packet": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_packet": SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_ck_family_top_theorem_linkage_obligation_packet(
    *,
    priority_review_path: Path = PRIORITY_REVIEW_PATH,
    total_conservation_review_path: Path = TOTAL_CONSERVATION_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    priority_review = _read_json(priority_review_path)
    total_review = _read_json(total_conservation_review_path)
    theorem_target_rows = _theorem_target_rows()
    packet_criteria = _packet_criteria(priority_review, total_review)
    acceptance_criteria = {
        "consumes_expected_top_obligation_packet_target": (
            priority_review.get("schema_id") == PRIORITY_REVIEW_SCHEMA_ID
            and priority_review.get("packet_id") == PRIORITY_REVIEW_PACKET_ID
            and priority_review.get("outcome_id") == PRIORITY_REVIEW_OUTCOME
            and priority_review.get("selected_next_target") == CONSUMED_TARGET
            and priority_review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and priority_review.get("accepted") is True
        ),
        "top_cexchange_obligation_preserved": (
            priority_review.get("top_obligation_candidate") == TOP_OBLIGATION_CANDIDATE
            and priority_review.get("top_obligation_row_id") == TOP_OBLIGATION_ROW_ID
            and priority_review.get("top_obligation_packet_scope")
            == TOP_OBLIGATION_PACKET_SCOPE
        ),
        "accepted_total_conservation_route_basis": (
            total_review.get("schema_id") == TOTAL_CONSERVATION_REVIEW_SCHEMA_ID
            and total_review.get("packet_id") == TOTAL_CONSERVATION_REVIEW_PACKET_ID
            and total_review.get("outcome_id") == TOTAL_CONSERVATION_REVIEW_OUTCOME
            and total_review.get("accepted") is True
            and total_review.get("total_stress_energy_conservation_identity")
            == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "theorem_target_exactly_scoped": (
            theorem_target_rows[0]["given"]
            == [
                TOTAL_STRESS_ENERGY_DEFINITION,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
                C_EXCHANGE_RESIDUAL_DEFINITION,
            ]
            and theorem_target_rows[0]["then"] == C_EXCHANGE_TARGET_CONCLUSION
        ),
        "classification_recorded": (
            TOP_OBLIGATION == "C_exchange theorem-linkage gap"
            and BASIS == "accepted psi-A total-conservation route"
            and RULE_FAMILY == "interaction exchange-balance admissibility"
            and GOAL == "theorem-link C_exchange to total conservation"
        ),
        "no_proof_execution_or_theorem_discharge": (
            SELECTED_PROOF_TARGET == "NONE_SELECTED"
            and theorem_target_rows[0]["selected_for_attempt_now"] is False
            and theorem_target_rows[0]["theorem_discharged"] is False
        ),
        "all_gaps_remain_open": (
            priority_review.get("gap_count") == 8
            and priority_review.get("open_gap_count") == 8
            and priority_review.get("closed_gap_count") == 0
        ),
        "no_input_forbidden_claims": _input_boundary_clear(
            priority_review,
            total_review,
        ),
        "packet_criteria_all_accepted": all(
            row["status"] == "accepted" for row in packet_criteria
        ),
        "lean_status_wording_careful": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_REQUIRES_REMEDIATION",
        "strict_packet_result": STRICT_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "likely_follow_on_target_after_review": LIKELY_FOLLOW_ON_TARGET,
        "likely_follow_on_target_kind_after_review": LIKELY_FOLLOW_ON_TARGET_KIND,
        "priority_review_schema_id": PRIORITY_REVIEW_SCHEMA_ID,
        "priority_review_packet_id": PRIORITY_REVIEW_PACKET_ID,
        "priority_review_outcome": PRIORITY_REVIEW_OUTCOME,
        "priority_review_consumed": accepted,
        "total_conservation_review_schema_id": TOTAL_CONSERVATION_REVIEW_SCHEMA_ID,
        "total_conservation_review_packet_id": TOTAL_CONSERVATION_REVIEW_PACKET_ID,
        "total_conservation_review_outcome": TOTAL_CONSERVATION_REVIEW_OUTCOME,
        "total_conservation_review_basis_consumed": accepted,
        "top_obligation": TOP_OBLIGATION,
        "top_obligation_candidate": TOP_OBLIGATION_CANDIDATE,
        "top_obligation_row_id": TOP_OBLIGATION_ROW_ID,
        "top_obligation_packet_scope": TOP_OBLIGATION_PACKET_SCOPE,
        "top_obligation_packet_plain_meaning": PRIORITY_REVIEW_TOP_SCOPE_MEANING,
        "basis": BASIS,
        "rule_family": RULE_FAMILY,
        "rule_family_classification": C_EXCHANGE_CLASSIFICATION,
        "goal": GOAL,
        "theorem_target_id": THEOREM_TARGET_ID,
        "theorem_target_name": THEOREM_TARGET_NAME,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "theorem_target_rows": theorem_target_rows,
        "theorem_target_row_count": len(theorem_target_rows),
        "theorem_target_indexed": accepted,
        "theorem_linkage_target_indexed": accepted,
        "top_obligation_packet_prepared": accepted,
        "top_obligation_prepared": accepted,
        "C_exchange_theorem_linkage_obligation_scoped": accepted,
        "C_exchange_from_total_conservation_theorem_target_indexed": accepted,
        "total_stress_energy_definition": TOTAL_STRESS_ENERGY_DEFINITION,
        "total_stress_energy_object": TOTAL_STRESS_ENERGY_OBJECT,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_residual_definition": C_EXCHANGE_RESIDUAL_DEFINITION,
        "C_exchange_constraint_form": C_EXCHANGE_CONSTRAINT_FORM,
        "C_exchange_admissibility_condition": C_EXCHANGE_ADMISSIBILITY_CONDITION,
        "C_exchange_target_conclusion": C_EXCHANGE_TARGET_CONCLUSION,
        "selected_theorem_row": SELECTED_THEOREM_ROW,
        "selected_theorem_target_for_attempt": SELECTED_THEOREM_TARGET_FOR_ATTEMPT,
        "selected_proof_target": SELECTED_PROOF_TARGET,
        "proof_execution": PROOF_EXECUTION_STATUS,
        "proof_execution_authorized": False,
        "proof_target_execution_authorized": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "proof_target_selected": False,
        "theorem_row_selected_for_execution": False,
        "theorem_discharged": False,
        "theorem_linkage_completed": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "rule_promotion": RULE_PROMOTION_STATUS,
        "rule_promoted": False,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "priority_criteria": PRIORITY_CRITERIA,
        "priority_criterion_count": len(PRIORITY_CRITERIA),
        "ranked_row_ids": RANKED_ROW_IDS,
        "ranked_row_count": len(RANKED_ROW_IDS),
        "priority_ranking_accepted": accepted,
        "priority_rows_ranked": accepted,
        "accepted_packet_findings": ACCEPTED_PACKET_FINDINGS,
        "accepted_packet_finding_count": len(ACCEPTED_PACKET_FINDINGS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "packet_criteria": packet_criteria,
        "packet_criteria_count": len(packet_criteria),
        "packet_criteria_accepted_count": sum(
            1 for row in packet_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "review_result_preparation_target": NEXT_TARGET,
        "review_result_preparation_authorized": accepted,
        "cexchange_attempt_preparation_likely_after_review": LIKELY_FOLLOW_ON_TARGET,
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "plain_meaning": PLAIN_MEANING,
        "mathematical_statement": THEOREM_TARGET_STATEMENT,
        "non_claim_boundary": (
            "This top-obligation packet prepares only the exact C_exchange "
            "theorem-linkage target from the accepted psi-A total-conservation "
            "route. It indexes the target that, given T_total^{mu nu} = "
            "T_A^{mu nu} + T_psi^{mu nu}, nabla_mu T_total^{mu nu} = 0, "
            "and C_exchange^{Apsi,nu} := nabla_mu T_total^{mu nu}, the "
            "conclusion C_exchange^{Apsi,nu} = 0 should follow. It does not "
            "execute any proof, discharge any theorem row, discharge GAP-1 "
            "through GAP-8, promote any C_k rule, embed C_k in an action, vary "
            "C_k, select a multiplier route, select a penalty route, make a "
            "direct dynamical-law claim, close EM-QFT, close QFT-GR, close "
            "GR-QM, claim empirical validation, or promote the master action. "
            "The master action remains a working-form, noncanonical organizing "
            "surface, not a promoted final law."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_ck_family_top_theorem_linkage_obligation_packet",
            "fail to preserve C_exchange as the top obligation",
            "fail to cite accepted psi-A total-conservation route as basis",
            "fail to record T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}",
            "fail to record nabla_mu T_total^{mu nu} = 0",
            "fail to define C_exchange as nabla_mu T_total^{mu nu}",
            "fail to index C_exchange^{Apsi,nu} = 0 as target conclusion",
            "execute a proof",
            "discharge a theorem row",
            "discharge any GAP-1 through GAP-8 item",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "claim direct dynamical-law interpretation",
            "claim EM-QFT, QFT-GR, or GR-QM closure",
            "claim empirical prediction or validation",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_PACKET,
        "full_toeformal_aggregate_status_for_packet": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_packet": SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
        "aggregate_lean_validation_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.CKFamilyTopTheoremLinkageObligationPacket",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "priority_review_file": _ptr(priority_review_path),
            "priority_review_lean_file": _ptr(PRIORITY_REVIEW_LEAN_PACKET_PATH),
            "total_conservation_review_file": _ptr(total_conservation_review_path),
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


def write_top_obligation_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the top C_k theorem-linkage obligation packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--priority-review", type=Path, default=PRIORITY_REVIEW_PATH)
    parser.add_argument(
        "--total-conservation-review",
        type=Path,
        default=TOTAL_CONSERVATION_REVIEW_PATH,
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    priority_review_path = (
        args.priority_review
        if args.priority_review.is_absolute()
        else REPO_ROOT / args.priority_review
    )
    total_conservation_review_path = (
        args.total_conservation_review
        if args.total_conservation_review.is_absolute()
        else REPO_ROOT / args.total_conservation_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_ck_family_top_theorem_linkage_obligation_packet(
        priority_review_path=priority_review_path,
        total_conservation_review_path=total_conservation_review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_top_obligation_packet(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "packet_result": payload["packet_result"],
                "selected_next_target": payload["selected_next_target"],
                "theorem_target_id": payload["theorem_target_id"],
                "lean_status_wording": payload["lean_status_wording"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
