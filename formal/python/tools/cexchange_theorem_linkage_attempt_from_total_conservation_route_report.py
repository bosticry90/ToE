from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_top_theorem_linkage_obligation_packet_result_review_report import (
    BASIS,
    BLOCKED_CLAIMS,
    C_EXCHANGE_RESIDUAL_DEFINITION,
    C_EXCHANGE_TARGET_CONCLUSION,
    DEFAULT_OUT as SCOPE_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    GOAL,
    LEAN_PACKET_PATH as SCOPE_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as SCOPE_REVIEW_OUTCOME,
    PACKET_ID as SCOPE_REVIEW_PACKET_ID,
    RULE_FAMILY,
    SCHEMA_ID as SCOPE_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT as SCOPE_REVIEW_STRICT_OUTCOME,
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

SCHEMA_ID = "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_20260627_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_v0"
PACKET_RESULT = (
    "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_PREPARED_"
    "DEFINITIONAL_LINKAGE_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_OR_CK_RULE_PROMOTION"
)
STRICT_PACKET_RESULT = (
    "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_PREPARED_"
    "TOTAL_CONSERVATION_TO_CEXCHANGE_ZERO_LINKAGE_TARGET_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = PACKET_RESULT
PACKET_CLASSIFICATION = (
    "cexchange_theorem_linkage_attempt_from_total_conservation_route_prepared_"
    "definitional_linkage_route_indexed_no_theorem_discharge_or_ck_rule_promotion"
)

NEXT_TARGET = "review_cexchange_theorem_linkage_attempt_from_total_conservation_route_result"
NEXT_TARGET_KIND = "cexchange_theorem_linkage_attempt_from_total_conservation_route_result_review"
LIKELY_FOLLOW_ON_TARGET = "execute_cexchange_theorem_linkage_attempt_from_total_conservation_route"
LIKELY_FOLLOW_ON_TARGET_KIND = (
    "cexchange_theorem_linkage_attempt_from_total_conservation_route_execution"
)

ATTEMPT_TYPE = "definitional theorem-linkage attempt"
INPUT_ROUTE = "accepted psi-A total stress-energy conservation"
TARGET_RULE = "C_exchange^{Apsi,nu} = 0"
PROOF_STYLE = "definition expansion plus accepted total-conservation route"
CLAIM_BOUNDARY = "theorem-linkage only, not physics closure"
PLAIN_MEANING = (
    "If C_exchange is defined as the total-conservation leftover, and the "
    "total-conservation leftover is zero, then C_exchange is zero."
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET = SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_PACKET = LEAN_STATUS_WORDING_FOR_REVIEW

ACCEPTED_PACKET_FINDINGS = [
    "attempt type: definitional theorem-linkage attempt",
    "input route: accepted psi-A total stress-energy conservation",
    "target rule: C_exchange^{Apsi,nu} = 0",
    "proof style: definition expansion plus accepted total-conservation route",
    "claim boundary: theorem-linkage only, not physics closure",
    "no theorem discharge yet",
    "no C_k rule promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_20260627_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CExchangeTheoremLinkageAttemptFromTotalConservationRoute.lean"
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
        "theorem_row_selected": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "new_physics_created": False,
        "new_field_or_interaction_expansion_selected": False,
    }


def _input_boundary_clear(scope_review: dict[str, Any]) -> bool:
    return all(
        scope_review.get(key) is False
        for key in _false_boundary_flags()
        if key in scope_review
    )


def _attempt_route_rows() -> list[dict[str, Any]]:
    return [
        {
            "row_id": THEOREM_TARGET_ID,
            "attempt_type": ATTEMPT_TYPE,
            "input_route": INPUT_ROUTE,
            "target_rule": TARGET_RULE,
            "proof_style": PROOF_STYLE,
            "claim_boundary": CLAIM_BOUNDARY,
            "given": [
                TOTAL_STRESS_ENERGY_DEFINITION,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
                C_EXCHANGE_RESIDUAL_DEFINITION,
            ],
            "therefore": C_EXCHANGE_TARGET_CONCLUSION,
            "plain_meaning": PLAIN_MEANING,
            "prepared_for_attempt": True,
            "proof_execution_authorized": False,
            "proof_attempt_executed": False,
            "theorem_discharged": False,
            "rule_promoted": False,
        }
    ]


def _packet_criteria(scope_review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "scope_review_consumed",
            "status": "accepted",
            "evidence": scope_review.get("review_result"),
            "assessment": "The scope review is consumed by the attempt-preparation packet.",
        },
        {
            "row_id": "definitional_attempt_type_recorded",
            "status": "accepted",
            "evidence": ATTEMPT_TYPE,
            "assessment": "The packet records a definitional theorem-linkage attempt type.",
        },
        {
            "row_id": "accepted_total_conservation_input_route_recorded",
            "status": "accepted",
            "evidence": INPUT_ROUTE,
            "assessment": "The accepted psi-A total stress-energy conservation route is the input route.",
        },
        {
            "row_id": "target_rule_recorded",
            "status": "accepted",
            "evidence": TARGET_RULE,
            "assessment": "The target rule is C_exchange^{Apsi,nu} = 0.",
        },
        {
            "row_id": "proof_style_recorded",
            "status": "accepted",
            "evidence": PROOF_STYLE,
            "assessment": "The intended proof style is definition expansion plus the accepted route.",
        },
        {
            "row_id": "logical_shape_preserved",
            "status": "accepted",
            "evidence": [
                TOTAL_STRESS_ENERGY_DEFINITION,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
                C_EXCHANGE_RESIDUAL_DEFINITION,
                C_EXCHANGE_TARGET_CONCLUSION,
            ],
            "assessment": "The exact given/therefore linkage shape is indexed.",
        },
        {
            "row_id": "no_theorem_discharge_yet",
            "status": "accepted",
            "evidence": {
                "proof_attempt_executed": False,
                "theorem_discharged": False,
            },
            "assessment": "The packet prepares the attempt only and discharges no theorem.",
        },
        {
            "row_id": "no_ck_rule_promotion_or_action_route",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "No C_k promotion, action embedding, variation, multiplier, or penalty route is authorized.",
        },
        {
            "row_id": "claim_boundary_preserved",
            "status": "accepted",
            "evidence": CLAIM_BOUNDARY,
            "assessment": "The attempt remains theorem-linkage only, not physics closure.",
        },
        {
            "row_id": "next_result_review_target_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The packet rotates to result review before any execution target.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "cexchange_theorem_linkage_attempt_from_total_conservation_route",
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


def build_cexchange_theorem_linkage_attempt_from_total_conservation_route(
    *,
    scope_review_path: Path = SCOPE_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    scope_review = _read_json(scope_review_path)
    route_rows = _attempt_route_rows()
    packet_criteria = _packet_criteria(scope_review)
    acceptance_criteria = {
        "consumes_expected_attempt_preparation_target": (
            scope_review.get("schema_id") == SCOPE_REVIEW_SCHEMA_ID
            and scope_review.get("packet_id") == SCOPE_REVIEW_PACKET_ID
            and scope_review.get("outcome_id") == SCOPE_REVIEW_OUTCOME
            and scope_review.get("strict_review_result") == SCOPE_REVIEW_STRICT_OUTCOME
            and scope_review.get("selected_next_target") == CONSUMED_TARGET
            and scope_review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and scope_review.get("accepted") is True
        ),
        "theorem_target_preserved": (
            scope_review.get("theorem_target_id") == THEOREM_TARGET_ID
            and scope_review.get("theorem_target_statement") == THEOREM_TARGET_STATEMENT
            and scope_review.get("theorem_target_recorded") is True
            and scope_review.get("theorem_target_indexed") is True
        ),
        "attempt_classification_recorded": (
            ATTEMPT_TYPE == "definitional theorem-linkage attempt"
            and INPUT_ROUTE == "accepted psi-A total stress-energy conservation"
            and TARGET_RULE == C_EXCHANGE_TARGET_CONCLUSION
            and PROOF_STYLE
            == "definition expansion plus accepted total-conservation route"
            and CLAIM_BOUNDARY == "theorem-linkage only, not physics closure"
        ),
        "logical_shape_exactly_indexed": (
            route_rows[0]["given"]
            == [
                TOTAL_STRESS_ENERGY_DEFINITION,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
                C_EXCHANGE_RESIDUAL_DEFINITION,
            ]
            and route_rows[0]["therefore"] == C_EXCHANGE_TARGET_CONCLUSION
        ),
        "no_proof_execution_or_theorem_discharge": (
            route_rows[0]["proof_execution_authorized"] is False
            and route_rows[0]["proof_attempt_executed"] is False
            and route_rows[0]["theorem_discharged"] is False
            and route_rows[0]["rule_promoted"] is False
        ),
        "all_gaps_remain_open": (
            scope_review.get("gap_count") == 8
            and scope_review.get("open_gap_count") == 8
            and scope_review.get("closed_gap_count") == 0
            and scope_review.get("gap_1_through_gap_8_discharged") is False
        ),
        "no_input_forbidden_claims": _input_boundary_clear(scope_review),
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
        else "REMEDIATE_CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_REQUIRES_REMEDIATION",
        "strict_packet_result": STRICT_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "likely_follow_on_target_after_review": LIKELY_FOLLOW_ON_TARGET,
        "likely_follow_on_target_kind_after_review": LIKELY_FOLLOW_ON_TARGET_KIND,
        "scope_review_schema_id": SCOPE_REVIEW_SCHEMA_ID,
        "scope_review_packet_id": SCOPE_REVIEW_PACKET_ID,
        "scope_review_outcome": SCOPE_REVIEW_OUTCOME,
        "scope_review_strict_outcome": SCOPE_REVIEW_STRICT_OUTCOME,
        "scope_review_consumed": accepted,
        "top_obligation": TOP_OBLIGATION,
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
        "theorem_target_recorded": accepted,
        "theorem_target_indexed": accepted,
        "theorem_linkage_target_indexed": accepted,
        "definition_linkage_route_indexed": accepted,
        "definition_linkage_attempt_prepared": accepted,
        "total_conservation_to_cexchange_zero_linkage_target_indexed": accepted,
        "attempt_route_rows": route_rows,
        "attempt_route_row_count": len(route_rows),
        "total_stress_energy_definition": TOTAL_STRESS_ENERGY_DEFINITION,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_residual_definition": C_EXCHANGE_RESIDUAL_DEFINITION,
        "C_exchange_target_conclusion": C_EXCHANGE_TARGET_CONCLUSION,
        "plain_meaning": PLAIN_MEANING,
        "mathematical_statement": THEOREM_TARGET_STATEMENT,
        "selected_theorem_row": TOP_OBLIGATION_ROW_ID,
        "selected_theorem_target_for_attempt": THEOREM_TARGET_ID,
        "selected_proof_target": THEOREM_TARGET_ID,
        "proof_execution": "not yet",
        "proof_execution_authorized": False,
        "proof_target_execution_authorized": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "proof_target_selected": True,
        "theorem_row_selected": True,
        "theorem_row_selected_for_execution": False,
        "theorem_discharged": False,
        "theorem_linkage_completed": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
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
        "result_review_prepared": False,
        "result_review_accepted": False,
        "attempt_preparation_packet_prepared": accepted,
        "attempt_execution_authorized_after_review_only": True,
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This packet prepares only the C_exchange definitional theorem-linkage "
            "attempt from the accepted psi-A total stress-energy conservation "
            "route. It indexes the logical shape: given T_total^{mu nu} = "
            "T_A^{mu nu} + T_psi^{mu nu}, nabla_mu T_total^{mu nu} = 0, and "
            "C_exchange^{Apsi,nu} := nabla_mu T_total^{mu nu}, therefore "
            "C_exchange^{Apsi,nu} = 0. It records proof style as definition "
            "expansion plus the accepted total-conservation route, but does not "
            "execute the proof, discharge the theorem, promote any C_k rule, "
            "embed C_k in an action, vary C_k, select a multiplier route, select "
            "a penalty route, make a direct dynamical-law claim, close EM-QFT, "
            "close QFT-GR, close GR-QM, claim empirical validation, or promote "
            "the master action. The master action remains a working-form, "
            "noncanonical organizing surface, not a promoted final law."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_cexchange_theorem_linkage_attempt_from_total_conservation_route",
            "fail to record definitional theorem-linkage attempt type",
            "fail to preserve accepted psi-A total stress-energy conservation input route",
            "fail to record C_exchange^{Apsi,nu} = 0 as target rule",
            "fail to record definition expansion plus accepted total-conservation proof style",
            "execute a proof",
            "discharge the theorem",
            "discharge any GAP-1 through GAP-8 item",
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
            "ToeFormal.Derivation.CExchangeTheoremLinkageAttemptFromTotalConservationRoute",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "scope_review_file": _ptr(scope_review_path),
            "scope_review_lean_file": _ptr(SCOPE_REVIEW_LEAN_PACKET_PATH),
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
    return payload


def write_attempt_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Prepare the C_exchange theorem-linkage attempt from total conservation."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--scope-review", type=Path, default=SCOPE_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    scope_review_path = (
        args.scope_review
        if args.scope_review.is_absolute()
        else REPO_ROOT / args.scope_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_cexchange_theorem_linkage_attempt_from_total_conservation_route(
        scope_review_path=scope_review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_attempt_packet(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "packet_result": payload["packet_result"],
                "selected_next_target": payload["selected_next_target"],
                "proof_style": payload["proof_style"],
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
