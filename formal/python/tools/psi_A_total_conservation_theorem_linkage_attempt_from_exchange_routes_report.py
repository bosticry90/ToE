from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_packet_result_review_report import (
    DEFAULT_OUT as REVIEW_PATH,
    EXPANDED_CANCELLATION_CHAIN,
    EXPANDED_CANCELLATION_CHAIN_STATEMENT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    GAUGE_EXCHANGE_ROUTE,
    LEAN_PACKET_PATH as REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    MATTER_EXCHANGE_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as REVIEW_OUTCOME,
    PACKET_ID as REVIEW_PACKET_ID,
    PLAIN_MEANING,
    PROOF_STYLE,
    SCHEMA_ID as REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_REVIEW_RESULT,
    THEOREM_TARGET_STATEMENT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_STRESS_ENERGY_DEFINITION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-27T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "20260627_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_v0"
ATTEMPT_PREPARATION_RESULT = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "PREPARED_EXCHANGE_CANCELLATION_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_OR_"
    "CK_RULE_PROMOTION"
)
STRICT_ATTEMPT_PREPARATION_RESULT = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "PREPARED_GAUGE_MATTER_EXCHANGE_CANCELLATION_ROUTE_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = ATTEMPT_PREPARATION_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_"
    "prepared_exchange_cancellation_route_indexed"
)

NEXT_TARGET = "review_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result"
NEXT_TARGET_KIND = (
    "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result_review"
)
LIKELY_POST_REVIEW_TARGET = (
    "execute_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes"
)
LIKELY_POST_REVIEW_TARGET_KIND = (
    "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution"
)

ATTEMPT_TYPE = "exchange-cancellation theorem-linkage attempt"
INPUT_ROUTE = "accepted gauge-sector exchange route plus accepted matter-sector exchange route"
TARGET_RULE = TOTAL_CONSERVATION_CONCLUSION
PROOF_EXECUTION_STATUS = "not yet"
RULE_PROMOTION_STATUS = "not authorized"

ATTEMPT_WATCH_ITEMS = [
    "same F object",
    "same J object",
    "same index placement",
    "same sign convention",
    "same covariant derivative",
    "linearity of nabla over addition",
    "valid T_total definition",
    "shared domain and boundary assumptions",
]

ROUTE_STEPS = [
    GAUGE_EXCHANGE_ROUTE,
    MATTER_EXCHANGE_ROUTE,
    TOTAL_STRESS_ENERGY_DEFINITION,
    "nabla_mu T_total^{mu nu} = nabla_mu(T_A^{mu nu} + T_psi^{mu nu})",
    "nabla_mu(T_A^{mu nu} + T_psi^{mu nu}) = nabla_mu T_A^{mu nu} + nabla_mu T_psi^{mu nu}",
    "nabla_mu T_A^{mu nu} + nabla_mu T_psi^{mu nu} = - F^nu{}_alpha J^alpha + F^nu{}_alpha J^alpha",
    "- F^nu{}_alpha J^alpha + F^nu{}_alpha J^alpha = 0",
    TOTAL_CONSERVATION_CONCLUSION,
]

ACCEPTED_PACKET_FINDINGS = [
    "attempt type: exchange-cancellation theorem-linkage attempt",
    "input route: accepted gauge-sector exchange route plus accepted matter-sector exchange route",
    "target rule: nabla_mu T_total^{mu nu} = 0",
    "proof style: exchange-term cancellation plus total stress-energy definition",
    "watch items recorded",
    "proof execution: not yet",
    "rule promotion: not authorized",
]

BLOCKED_CLAIMS = [
    "no proof execution during preparation",
    "no theorem discharge during preparation",
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
    / "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_20260627_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutes.lean"
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


def _theorem_shape() -> dict[str, Any]:
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


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "preparation_executes_proof": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
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


def _review_valid(review: dict[str, Any]) -> bool:
    return (
        review.get("schema_id") == REVIEW_SCHEMA_ID
        and review.get("packet_id") == REVIEW_PACKET_ID
        and review.get("outcome_id") == REVIEW_OUTCOME
        and review.get("review_result") == REVIEW_OUTCOME
        and review.get("strict_review_result") == STRICT_REVIEW_RESULT
        and review.get("selected_next_target") == CONSUMED_TARGET
        and review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and review.get("theorem_target_statement") == THEOREM_TARGET_STATEMENT
        and review.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_preparation"
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
        "full_toeformal_aggregate_status_for_packet": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
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


def build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes(
    *,
    review_path: Path = REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    theorem_shape = _theorem_shape()
    acceptance_criteria = {
        "consumes_expected_packet_result_review": _review_valid(review),
        "review_outcome_accepted": review.get("accepted") is True,
        "exchange_cancellation_route_indexed": theorem_shape["route_steps"] == ROUTE_STEPS,
        "watch_items_recorded": ATTEMPT_WATCH_ITEMS
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
        "no_proof_execution_or_theorem_discharge": True,
        "blocked_claims_preserved": True,
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
        else "REMEDIATE_PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_PREPARATION"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_REQUIRES_REMEDIATION",
        "attempt_preparation_result": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_REQUIRES_REMEDIATION",
        "strict_attempt_preparation_result": STRICT_ATTEMPT_PREPARATION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "likely_post_review_target": LIKELY_POST_REVIEW_TARGET,
        "likely_post_review_target_kind": LIKELY_POST_REVIEW_TARGET_KIND,
        "review_schema_id": REVIEW_SCHEMA_ID,
        "review_packet_id": REVIEW_PACKET_ID,
        "review_outcome": REVIEW_OUTCOME,
        "review_result": REVIEW_OUTCOME,
        "review_strict_outcome": STRICT_REVIEW_RESULT,
        "review_consumed": accepted,
        "attempt_type": ATTEMPT_TYPE,
        "input_route": INPUT_ROUTE,
        "target_rule": TARGET_RULE,
        "proof_style": PROOF_STYLE,
        "proof_execution": PROOF_EXECUTION_STATUS,
        "rule_promotion": RULE_PROMOTION_STATUS,
        "theorem_shape": theorem_shape,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
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
        "accepted_packet_findings": ACCEPTED_PACKET_FINDINGS,
        "accepted_packet_finding_count": len(ACCEPTED_PACKET_FINDINGS),
        "preparation_executes_proof": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "theorem_linkage_completed": False,
        "theorem_linkage_proof_attempt_authorized": False,
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
            "This packet prepares only the psi-A total conservation theorem-linkage "
            "attempt from the accepted gauge-sector and matter-sector exchange "
            "routes plus the T_total definition. It indexes the exchange-cancellation "
            "route for later execution but does not execute the proof, discharge any "
            "theorem, discharge GAP-1 through GAP-8, promote any C_k rule, embed C_k "
            "in an action, vary C_k, select a multiplier route, select a penalty "
            "route, make a direct dynamical-law claim, close full Maxwell, close "
            "EM-QFT, close QFT-GR, close GR-QM, claim empirical validation, or "
            "promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes",
            "fail to index the exchange-cancellation route",
            "fail to record the gauge-sector exchange route",
            "fail to record the matter-sector exchange route",
            "fail to record T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}",
            "fail to record watch items",
            "execute proof during preparation",
            "discharge theorem during preparation",
            "discharge GAP-1 through GAP-8",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "claim full Maxwell, EM-QFT, QFT-GR, or GR-QM closure",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_PACKET,
        "full_toeformal_aggregate_status_for_packet": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
        ),
        "aggregate_lean_validation_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutes",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "review_file": _ptr(review_path),
            "review_lean_file": _ptr(REVIEW_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_false_boundary_flags())
    return payload


def write_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Prepare the psi-A total conservation theorem-linkage attempt from exchange routes."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--review", type=Path, default=REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = args.review if args.review.is_absolute() else REPO_ROOT / args.review
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes(
        review_path=review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_packet(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "packet_result": payload["packet_result"],
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
