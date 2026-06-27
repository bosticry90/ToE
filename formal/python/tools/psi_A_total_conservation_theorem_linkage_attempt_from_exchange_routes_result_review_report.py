from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_report import (
    ATTEMPT_PREPARATION_RESULT,
    ATTEMPT_TYPE,
    ATTEMPT_WATCH_ITEMS,
    BLOCKED_CLAIMS,
    DEFAULT_OUT as ATTEMPT_PACKET_PATH,
    EXPANDED_CANCELLATION_CHAIN,
    EXPANDED_CANCELLATION_CHAIN_STATEMENT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    GAUGE_EXCHANGE_ROUTE,
    INPUT_ROUTE,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    MATTER_EXCHANGE_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as ATTEMPT_PACKET_OUTCOME,
    PACKET_ID as ATTEMPT_PACKET_ID,
    PLAIN_MEANING,
    PROOF_STYLE,
    ROUTE_STEPS,
    SCHEMA_ID as ATTEMPT_PACKET_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_ATTEMPT_PREPARATION_RESULT,
    THEOREM_TARGET_STATEMENT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_STRESS_ENERGY_DEFINITION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-27T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "RESULT_REVIEW_20260627_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "RESULT_REVIEW_ACCEPTS_EXCHANGE_CANCELLATION_ROUTE_PREPARATION_NO_THEOREM_"
    "DISCHARGE_OR_CK_RULE_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "RESULT_REVIEW_ACCEPTS_PREPARED_GAUGE_MATTER_EXCHANGE_CANCELLATION_ROUTE_"
    "NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_"
    "result_review_accepts_exchange_cancellation_route_preparation_no_theorem_"
    "discharge_or_ck_rule_promotion"
)

NEXT_TARGET = "execute_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes"
NEXT_TARGET_KIND = (
    "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution"
)
SUGGESTED_EXECUTION_OUTCOME = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "EXECUTED_EXCHANGE_CANCELLATION_CONSTRUCTED_NO_CK_RULE_PROMOTION_OR_"
    "MASTER_ACTION_PROMOTION"
)
STRICT_SUGGESTED_EXECUTION_OUTCOME = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "EXECUTED_TOTAL_CONSERVATION_DERIVED_FROM_GAUGE_MATTER_EXCHANGE_"
    "CANCELLATION_NO_SEAM_CLOSURE"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_PACKET

ACCEPTED_REVIEW_FINDINGS = [
    "exchange-cancellation route prepared",
    "gauge-sector exchange input preserved",
    "matter-sector exchange input preserved",
    "T_total definition preserved",
    "watch items preserved",
    "no proof execution",
    "no theorem discharge",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no seam closure",
    "no empirical validation",
    "no master-action promotion",
]

REVIEW_BLOCKED_CLAIMS = [
    "no proof execution during review",
    "no theorem discharge during review",
    "no GAP-1 through GAP-8 discharge",
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k variation",
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
        "RESULT_REVIEW_20260627_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutesResultReview.lean"
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
        "preparation_executes_proof": False,
        "review_executes_attempt": False,
        "proof_execution_authorized": False,
        "proof_target_execution_authorized": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "theorem_discharged": False,
        "theorem_linkage_completed": False,
        "theorem_linkage_obligation_discharged": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "gap_1_through_gap_8_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
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
        "rule_promoted": False,
        "obligation_row_discharged": False,
        "obligation_rows_discharged": False,
        "new_physics_created": False,
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
            GAUGE_EXCHANGE_ROUTE,
            MATTER_EXCHANGE_ROUTE,
            TOTAL_STRESS_ENERGY_DEFINITION,
        ],
        "then": TOTAL_CONSERVATION_CONCLUSION,
        "expanded": EXPANDED_CANCELLATION_CHAIN,
        "expanded_statement": EXPANDED_CANCELLATION_CHAIN_STATEMENT,
        "route_steps": ROUTE_STEPS,
        "plain_meaning": PLAIN_MEANING,
    }


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The prepared exchange-cancellation route is accepted for the "
                "next bounded theorem-linkage execution attempt."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The result-review target is consumed by this checkpoint.",
        },
        {
            "target": "promote_psi_A_total_conservation_to_physics_closure",
            "decision": "not_authorized",
            "reason": "The review accepts preparation only and does not claim closure.",
        },
        {
            "target": "embed_C_k_in_master_action",
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
    return [
        {
            "row_id": "attempt_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("packet_result"),
            "assessment": "The prepared psi-A total conservation attempt is consumed.",
        },
        {
            "row_id": "exchange_cancellation_route_prepared",
            "status": "accepted",
            "evidence": packet.get("route_steps"),
            "assessment": "The exchange-cancellation route is indexed but not executed.",
        },
        {
            "row_id": "gauge_sector_exchange_input_preserved",
            "status": "accepted",
            "evidence": packet.get("gauge_exchange_route"),
            "assessment": "The gauge-side exchange input is preserved.",
        },
        {
            "row_id": "matter_sector_exchange_input_preserved",
            "status": "accepted",
            "evidence": packet.get("matter_exchange_route"),
            "assessment": "The matter-side exchange input is preserved.",
        },
        {
            "row_id": "total_stress_energy_definition_preserved",
            "status": "accepted",
            "evidence": packet.get("total_stress_energy_definition"),
            "assessment": "The T_total definition is preserved.",
        },
        {
            "row_id": "watch_items_preserved",
            "status": "accepted",
            "evidence": packet.get("watch_items"),
            "assessment": "The convention and domain watch items are preserved.",
        },
        {
            "row_id": "no_proof_execution_or_discharge",
            "status": "accepted",
            "evidence": {
                "proof_attempt_executed": packet.get("proof_attempt_executed"),
                "theorem_discharged": packet.get("theorem_discharged"),
            },
            "assessment": "The review executes no proof and discharges no theorem.",
        },
        {
            "row_id": "no_ck_promotion_or_action_route",
            "status": "accepted",
            "evidence": REVIEW_BLOCKED_CLAIMS,
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
            "assessment": "The review remains below closure and validation claims.",
        },
        {
            "row_id": "master_action_status_preserved",
            "status": "accepted",
            "evidence": "working-form noncanonical organizing surface",
            "assessment": "The master action remains unpromoted.",
        },
        {
            "row_id": "execution_target_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next live target is the bounded execution attempt.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_"
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


def build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result_review(
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
            and packet.get("attempt_preparation_result") == ATTEMPT_PREPARATION_RESULT
            and packet.get("strict_attempt_preparation_result")
            == STRICT_ATTEMPT_PREPARATION_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and packet.get("accepted") is True
        ),
        "exchange_cancellation_route_prepared": (
            packet.get("route_steps") == ROUTE_STEPS
            and packet.get("expanded_cancellation_chain") == EXPANDED_CANCELLATION_CHAIN
            and packet.get("theorem_target_statement") == THEOREM_TARGET_STATEMENT
        ),
        "exchange_inputs_preserved": (
            packet.get("gauge_exchange_route") == GAUGE_EXCHANGE_ROUTE
            and packet.get("matter_exchange_route") == MATTER_EXCHANGE_ROUTE
            and packet.get("total_stress_energy_definition")
            == TOTAL_STRESS_ENERGY_DEFINITION
        ),
        "watch_items_preserved": packet.get("watch_items") == ATTEMPT_WATCH_ITEMS,
        "preparation_only_boundary_preserved": (
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
        else "REMEDIATE_PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_RESULT_REVIEW_REQUIRES_REMEDIATION",
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
        "attempt_preparation_result": ATTEMPT_PREPARATION_RESULT,
        "attempt_packet_strict_outcome": STRICT_ATTEMPT_PREPARATION_RESULT,
        "attempt_packet_consumed": accepted,
        "exchange_cancellation_route_prepared": accepted,
        "gauge_sector_exchange_input_preserved": accepted,
        "matter_sector_exchange_input_preserved": accepted,
        "total_stress_energy_definition_preserved": accepted,
        "watch_items_preserved": accepted,
        "execution_target_selected_after_review": accepted,
        "review_does_not_execute_theorem": accepted,
        "selected_obligation": "psi-A total conservation theorem-linkage gap",
        "selected_obligation_rank": "2",
        "attempt_type": ATTEMPT_TYPE,
        "input_route": INPUT_ROUTE,
        "target_rule": TOTAL_CONSERVATION_CONCLUSION,
        "proof_style": PROOF_STYLE,
        "claim_boundary": "theorem-linkage only, not physics closure",
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "theorem_target_shape": theorem_target_shape,
        "theorem_target_recorded": accepted,
        "theorem_target_indexed": accepted,
        "theorem_linkage_target_indexed": accepted,
        "exchange_cancellation_route_indexed": accepted,
        "gauge_exchange_route": GAUGE_EXCHANGE_ROUTE,
        "matter_exchange_route": MATTER_EXCHANGE_ROUTE,
        "total_stress_energy_definition": TOTAL_STRESS_ENERGY_DEFINITION,
        "total_conservation_conclusion": TOTAL_CONSERVATION_CONCLUSION,
        "expanded_cancellation_chain": EXPANDED_CANCELLATION_CHAIN,
        "expanded_cancellation_chain_statement": EXPANDED_CANCELLATION_CHAIN_STATEMENT,
        "route_steps": ROUTE_STEPS,
        "route_step_count": len(ROUTE_STEPS),
        "plain_meaning": PLAIN_MEANING,
        "watch_items": ATTEMPT_WATCH_ITEMS,
        "watch_item_count": len(ATTEMPT_WATCH_ITEMS),
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "review_blocked_claims": REVIEW_BLOCKED_CLAIMS,
        "blocked_claims": REVIEW_BLOCKED_CLAIMS,
        "blocked_claim_count": len(REVIEW_BLOCKED_CLAIMS),
        "preparation_blocked_claims": BLOCKED_CLAIMS,
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
        "theorem_linkage_obligation_discharged": False,
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
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only that the psi-A total conservation "
            "theorem-linkage attempt from exchange routes has been prepared. It "
            "preserves the gauge-sector exchange input, matter-sector exchange "
            "input, T_total definition, expanded cancellation route, and watch "
            "items. It selects the bounded execution attempt as the next target, "
            "but this review does not execute the proof, discharge the theorem, "
            "discharge GAP-1 through GAP-8, promote any C_k rule, embed C_k in an "
            "action, vary C_k, select a multiplier route, select a penalty route, "
            "make a direct dynamical-law claim, close full Maxwell, close EM-QFT, "
            "close QFT-GR, close GR-QM, claim empirical validation, or promote the "
            "master action. The master action remains a working-form, noncanonical "
            "organizing surface, not a promoted final law."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result",
            "fail to accept prepared exchange-cancellation route",
            "fail to preserve gauge-sector exchange input",
            "fail to preserve matter-sector exchange input",
            "fail to preserve T_total definition",
            "fail to preserve watch items",
            "execute a proof during review",
            "discharge the theorem during review",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "claim direct dynamical-law interpretation",
            "claim full Maxwell, EM-QFT, QFT-GR, or GR-QM closure",
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
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutesResultReview",
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
        },
    }
    payload.update(_false_boundary_flags())
    payload["proof_execution_authorized_by_review_for_next_target"] = accepted
    payload["theorem_linkage_proof_attempt_authorized_for_next_target"] = accepted
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
            "Review the psi-A total conservation theorem-linkage attempt preparation result."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--packet", type=Path, default=ATTEMPT_PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    packet_path = args.packet if args.packet.is_absolute() else REPO_ROOT / args.packet
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result_review(
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
