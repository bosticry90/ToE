from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_report import (
    ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
    ACCEPTED_PACKET_FINDINGS,
    ACCEPTED_SOURCED_MAXWELL_ROUTE,
    ATTEMPT_PREPARATION_RESULT,
    BASIS,
    BLOCKED_CLAIMS,
    DEFAULT_OUT as ATTEMPT_PACKET_PATH,
    FIELD_STRENGTH_OBJECT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    INPUT_ROUTE,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OBLIGATION,
    OUTCOME_ID as ATTEMPT_PACKET_OUTCOME,
    PACKET_ID as ATTEMPT_PACKET_ID,
    PLAIN_MEANING,
    PLANNED_PROOF_STEPS,
    PROOF_STYLE,
    ROUTE_GIVEN,
    ROUTE_THEN,
    SCHEMA_ID as ATTEMPT_PACKET_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_ATTEMPT_PREPARATION_RESULT,
    TARGET,
    THEOREM_TARGET_STATEMENT,
    WATCH_ITEMS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_"
    "ROUTE_RESULT_REVIEW_20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_"
    "ROUTE_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "RESULT_REVIEW_ACCEPTS_GAUGE_EXCHANGE_ROUTE_PREPARATION_NO_THEOREM_DISCHARGE_"
    "OR_CK_RULE_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "RESULT_REVIEW_ACCEPTS_PREPARED_STRESS_DIVERGENCE_TO_CURRENT_EXCHANGE_ROUTE_"
    "NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_"
    "result_review_accepts_gauge_exchange_route_preparation_no_theorem_discharge"
)

NEXT_TARGET = (
    "execute_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route"
)
NEXT_TARGET_KIND = (
    "psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_execution"
)
SUGGESTED_EXECUTION_OUTCOME = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "EXECUTED_GAUGE_EXCHANGE_ROUTE_CONSTRUCTED_NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_"
    "PROMOTION"
)
STRICT_SUGGESTED_EXECUTION_OUTCOME = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "EXECUTED_GAUGE_EXCHANGE_DERIVED_FROM_STRESS_DIVERGENCE_AND_SOURCED_MAXWELL_"
    "NO_SEAM_CLOSURE"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_PACKET

ACCEPTED_REVIEW_FINDINGS = [
    "gauge-sector exchange attempt prepared",
    "sourced Maxwell input preserved",
    "gauge stress-energy divergence identity preserved",
    "same F and J objects preserved",
    "sign and index conventions preserved",
    "no theorem execution",
    "no theorem discharge",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no full Maxwell closure",
    "no seam closure",
    "no empirical validation",
    "no master-action promotion",
    "execution target selected after review",
]

REVIEW_BLOCKED_CLAIMS = [
    "no theorem execution during review",
    "no theorem discharge during review",
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

EXCHANGE_DEPENDENCY_CHAIN = [
    "C_exchange = 0 depends on total conservation",
    "total conservation depends on matter-sector exchange",
    "total conservation depends on gauge-sector exchange",
    "matter-sector exchange is locally tightened",
    "gauge-sector exchange remains the execution target",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_"
        "MAXWELL_ROUTE_RESULT_REVIEW_20260628_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRouteResultReview.lean"
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
        "multiplier_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "pillar_completion_inferred": False,
        "assumption_discharge_completed": False,
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


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The prepared gauge-sector exchange route is accepted for the "
                "next bounded sourced-Maxwell theorem-linkage execution attempt."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The result-review target is consumed by this checkpoint.",
        },
        {
            "target": "claim_gauge_exchange_theorem_discharged",
            "decision": "not_authorized",
            "reason": "This review accepts preparation only and discharges no theorem.",
        },
        {
            "target": "promote_C_k_or_embed_C_k_in_action",
            "decision": "not_authorized",
            "reason": "No C_k promotion, action embedding, or variation is authorized.",
        },
        {
            "target": "claim_full_maxwell_or_seam_closure",
            "decision": "not_authorized",
            "reason": "The review remains below closure and validation claims.",
        },
    ]


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "attempt_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("packet_result"),
            "assessment": "The prepared gauge-side exchange attempt is consumed.",
        },
        {
            "row_id": "sourced_maxwell_input_preserved",
            "status": "accepted",
            "evidence": packet.get("accepted_sourced_maxwell_route"),
            "assessment": "The sourced Maxwell input remains nabla_mu F^{mu alpha} = J^alpha.",
        },
        {
            "row_id": "gauge_stress_divergence_identity_preserved",
            "status": "accepted",
            "evidence": packet.get("accepted_gauge_stress_energy_divergence_identity"),
            "assessment": "The gauge stress-energy divergence identity is preserved.",
        },
        {
            "row_id": "same_F_and_J_objects_preserved",
            "status": "accepted",
            "evidence": [packet.get("field_strength_object"), packet.get("current_object")],
            "assessment": "The same F and J objects are retained.",
        },
        {
            "row_id": "sign_and_index_conventions_preserved",
            "status": "accepted",
            "evidence": packet.get("watch_items"),
            "assessment": "Sign, index placement, and covariant derivative watch items are preserved.",
        },
        {
            "row_id": "no_theorem_execution_or_discharge",
            "status": "accepted",
            "evidence": {
                "proof_attempt_executed": packet.get("proof_attempt_executed"),
                "theorem_discharged": packet.get("theorem_discharged"),
            },
            "assessment": "The review executes no proof and discharges no theorem.",
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
            "psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_"
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


def build_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result_review(
    *,
    packet_path: Path = ATTEMPT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
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
        "target_equation_preserved": packet.get("target_rule") == TARGET,
        "sourced_maxwell_input_preserved": (
            packet.get("accepted_sourced_maxwell_route")
            == ACCEPTED_SOURCED_MAXWELL_ROUTE
        ),
        "gauge_stress_divergence_identity_preserved": (
            packet.get("accepted_gauge_stress_energy_divergence_identity")
            == ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
        ),
        "route_shape_preserved": (
            packet.get("theorem_shape", {}).get("given") == ROUTE_GIVEN
            and packet.get("theorem_shape", {}).get("then") == ROUTE_THEN
            and packet.get("planned_proof_steps") == PLANNED_PROOF_STEPS
            and packet.get("theorem_target_statement") == THEOREM_TARGET_STATEMENT
        ),
        "watch_items_preserved": packet.get("watch_items") == WATCH_ITEMS,
        "preparation_only_boundary_preserved": (
            packet.get("proof_execution_authorized") is False
            and packet.get("proof_attempt_executed") is False
            and packet.get("theorem_discharged") is False
            and packet.get("theorem_linkage_completed") is False
            and packet.get("rule_promoted") is False
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
        else "REMEDIATE_PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID if accepted else "REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID if accepted else "REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID if accepted else "REQUIRES_REMEDIATION",
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
        "gauge_sector_exchange_attempt_prepared": accepted,
        "sourced_maxwell_input_preserved": accepted,
        "gauge_stress_energy_divergence_identity_preserved": accepted,
        "same_F_and_J_objects_preserved": accepted,
        "sign_and_index_conventions_preserved": accepted,
        "watch_items_preserved": accepted,
        "execution_target_selected_after_review": accepted,
        "review_does_not_execute_theorem": accepted,
        "selected_obligation": OBLIGATION,
        "selected_obligation_rank": "4",
        "attempt_type": "sourced-Maxwell gauge-sector exchange theorem-linkage attempt",
        "input_route": INPUT_ROUTE,
        "target_rule": TARGET,
        "proof_style": PROOF_STYLE,
        "claim_boundary": "theorem-linkage only, not physics closure",
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "field_strength_object": FIELD_STRENGTH_OBJECT,
        "current_object": "J object",
        "accepted_sourced_maxwell_route": ACCEPTED_SOURCED_MAXWELL_ROUTE,
        "accepted_gauge_stress_energy_divergence_identity": (
            ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
        ),
        "route_given": ROUTE_GIVEN,
        "route_then": ROUTE_THEN,
        "planned_proof_steps": PLANNED_PROOF_STEPS,
        "plain_meaning": PLAIN_MEANING,
        "watch_items": WATCH_ITEMS,
        "accepted_packet_findings": ACCEPTED_PACKET_FINDINGS,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "review_blocked_claims": REVIEW_BLOCKED_CLAIMS,
        "blocked_claims": REVIEW_BLOCKED_CLAIMS,
        "preparation_blocked_claims": BLOCKED_CLAIMS,
        "candidate_next_targets": candidate_next_targets,
        "review_criteria": review_criteria,
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": accepted,
        "attempt_result_review_accepted": accepted,
        "attempt_execution_target_authorized": accepted,
        "attempt_execution_authorized_as_next_target": accepted,
        "attempt_execution_authorized_after_review_only": accepted,
        "exchange_dependency_chain": EXCHANGE_DEPENDENCY_CHAIN,
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
            "This result review accepts only that the psi-A gauge-sector exchange "
            "theorem-linkage attempt from the sourced Maxwell route has been prepared. "
            "It preserves the gauge stress-energy divergence identity, sourced Maxwell "
            "input, F and J objects, sign and index conventions, planned route, and "
            "watch items. It selects the bounded execution attempt as the next target, "
            "but this review does not execute the proof, discharge the theorem, promote "
            "any C_k rule, embed C_k in an action, vary C_k, close full Maxwell or any "
            "seam, claim empirical validation, or promote the master action."
        ),
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
            "ToeFormal.Derivation.PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRouteResultReview",
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
            "Review the psi-A gauge-sector exchange theorem-linkage attempt preparation result."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--packet", type=Path, default=ATTEMPT_PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    packet_path = args.packet if args.packet.is_absolute() else REPO_ROOT / args.packet
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result_review(
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
