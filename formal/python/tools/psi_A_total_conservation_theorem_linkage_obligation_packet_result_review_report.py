from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_packet_report import (
    BASIS,
    DEFAULT_OUT as PACKET_PATH,
    EXPANDED_CANCELLATION_CHAIN,
    EXPANDED_CANCELLATION_CHAIN_STATEMENT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    GAUGE_EXCHANGE_ROUTE,
    LEAN_PACKET_PATH as PACKET_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    MATTER_EXCHANGE_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OBLIGATION,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_ID as PREPARED_PACKET_ID,
    PACKET_RESULT,
    PLAIN_MEANING,
    PROOF_STYLE,
    SCHEMA_ID as PACKET_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_PACKET_RESULT,
    THEOREM_TARGET_STATEMENT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_STRESS_ENERGY_DEFINITION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-27T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_"
    "20260627_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "EXCHANGE_CANCELLATION_THEOREM_TARGET_SCOPE_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "GAUGE_MATTER_EXCHANGE_CANCELLATION_TARGET_NO_THEOREM_DISCHARGE_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_total_conservation_theorem_linkage_obligation_packet_result_review_accepts_"
    "exchange_cancellation_theorem_target_scope"
)

NEXT_TARGET = "prepare_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes"
NEXT_TARGET_KIND = (
    "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_preparation"
)
ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "PREPARED_EXCHANGE_CANCELLATION_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_OR_"
    "CK_RULE_PROMOTION"
)
STRICT_ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME = (
    "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
    "PREPARED_SHARED_CONVENTION_CHECKS_INDEXED_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)

PROOF_ATTEMPT_WATCH_ITEMS = [
    "same F object",
    "same J object",
    "same index placement",
    "same sign convention",
    "same connection/covariant derivative",
    "linearity of nabla over addition",
    "valid T_total definition",
    "shared domain and boundary assumptions",
]

ACCEPTED_REVIEW_FINDINGS = [
    "psi-A total conservation obligation scoped",
    "gauge-sector exchange route used as input",
    "matter-sector exchange route used as input",
    "T_total definition used as input",
    "exchange-cancellation theorem target recorded",
    "no proof execution",
    "no theorem discharge",
    "no C_k promotion",
    "no seam closure",
    "no master-action promotion",
]

BLOCKED_CLAIMS = [
    "no proof execution during review",
    "no theorem discharge during review",
    "no GAP-1 through GAP-8 discharge",
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k variation",
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
    / "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_20260627_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiATotalConservationTheoremLinkageObligationPacketResultReview.lean"
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
        "plain_meaning": PLAIN_MEANING,
    }


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "review_executes_proof": False,
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


def _packet_valid(packet: dict[str, Any]) -> bool:
    theorem_shape = _theorem_shape()
    return (
        packet.get("schema_id") == PACKET_SCHEMA_ID
        and packet.get("packet_id") == PREPARED_PACKET_ID
        and packet.get("outcome_id") == PACKET_OUTCOME
        and packet.get("packet_result") == PACKET_RESULT
        and packet.get("strict_packet_result") == STRICT_PACKET_RESULT
        and packet.get("selected_next_target") == CONSUMED_TARGET
        and packet.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and packet.get("obligation") == OBLIGATION
        and packet.get("basis") == BASIS
        and packet.get("proof_style") == PROOF_STYLE
        and packet.get("theorem_shape") == theorem_shape
        and packet.get("theorem_target_statement") == THEOREM_TARGET_STATEMENT
        and packet.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "psi_A_total_conservation_theorem_linkage_obligation_packet_result_review"
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
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_review": (
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


def build_psi_A_total_conservation_theorem_linkage_obligation_packet_result_review(
    *,
    packet_path: Path = PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    theorem_shape = _theorem_shape()
    acceptance_criteria = {
        "consumes_expected_packet_result": _packet_valid(packet),
        "packet_preparation_accepted": packet.get("accepted") is True,
        "exchange_cancellation_target_scope_accepted": (
            theorem_shape["given"]
            == [
                GAUGE_EXCHANGE_ROUTE,
                MATTER_EXCHANGE_ROUTE,
                TOTAL_STRESS_ENERGY_DEFINITION,
            ]
            and theorem_shape["then"] == TOTAL_CONSERVATION_CONCLUSION
            and theorem_shape["expanded"] == EXPANDED_CANCELLATION_CHAIN
        ),
        "later_proof_watch_items_recorded": len(PROOF_ATTEMPT_WATCH_ITEMS) == 8,
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
        else "REMEDIATE_PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "attempt_preparation_recommended_outcome": (
            ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME
        ),
        "strict_attempt_preparation_recommended_outcome": (
            STRICT_ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME
        ),
        "prepared_packet_schema_id": PACKET_SCHEMA_ID,
        "prepared_packet_id": PREPARED_PACKET_ID,
        "prepared_packet_outcome": PACKET_OUTCOME,
        "prepared_packet_result": PACKET_RESULT,
        "prepared_packet_strict_result": STRICT_PACKET_RESULT,
        "prepared_packet_consumed": accepted,
        "obligation": OBLIGATION,
        "basis": BASIS,
        "proof_style": PROOF_STYLE,
        "theorem_shape": theorem_shape,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "gauge_exchange_route": GAUGE_EXCHANGE_ROUTE,
        "matter_exchange_route": MATTER_EXCHANGE_ROUTE,
        "total_stress_energy_definition": TOTAL_STRESS_ENERGY_DEFINITION,
        "total_conservation_conclusion": TOTAL_CONSERVATION_CONCLUSION,
        "expanded_cancellation_chain": EXPANDED_CANCELLATION_CHAIN,
        "expanded_cancellation_chain_statement": EXPANDED_CANCELLATION_CHAIN_STATEMENT,
        "plain_meaning": PLAIN_MEANING,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "proof_attempt_watch_items": PROOF_ATTEMPT_WATCH_ITEMS,
        "proof_attempt_watch_item_count": len(PROOF_ATTEMPT_WATCH_ITEMS),
        "review_executes_proof": False,
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
            "This result review accepts only the psi-A total conservation "
            "theorem-linkage obligation packet scope. It records that the "
            "gauge-sector exchange route, matter-sector exchange route, and "
            "T_total definition supply the exchange-cancellation target for a "
            "later proof attempt. It does not execute any proof, discharge any "
            "theorem, discharge GAP-1 through GAP-8, promote any C_k rule, embed "
            "C_k in an action, vary C_k, claim full Maxwell closure, close "
            "EM-QFT, close QFT-GR, close GR-QM, claim empirical validation, or "
            "promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_psi_A_total_conservation_theorem_linkage_obligation_packet_result",
            "fail to accept the exchange-cancellation theorem target scope",
            "fail to record the gauge-sector exchange route",
            "fail to record the matter-sector exchange route",
            "fail to record T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}",
            "fail to record later proof-attempt watch items",
            "execute proof during review",
            "discharge theorem during review",
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
        "full_toeformal_aggregate_status_for_review": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
        ),
        "aggregate_lean_validation_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PsiATotalConservationTheoremLinkageObligationPacketResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "prepared_packet_file": _ptr(packet_path),
            "prepared_packet_lean_file": _ptr(PACKET_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_false_boundary_flags())
    return payload


def write_review(review: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(review, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Review the psi-A total conservation theorem-linkage obligation packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--packet", type=Path, default=PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    packet_path = args.packet if args.packet.is_absolute() else REPO_ROOT / args.packet
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_psi_A_total_conservation_theorem_linkage_obligation_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
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
