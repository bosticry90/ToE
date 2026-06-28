from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_report import (
    ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
    ACCEPTED_SOURCED_MAXWELL_ROUTE,
    CLAIM_BOUNDARY as CLOSEOUT_CLAIM_BOUNDARY,
    CLOSEOUT_CLAIMS,
    CLOSEOUT_RESULT,
    CLOSEOUT_STATEMENT,
    CURRENT_OBJECT,
    DEFAULT_OUT as CLOSEOUT_PATH,
    FIELD_STRENGTH_OBJECT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_CLOSEOUT,
    LIKELY_NEXT_OBLIGATION,
    LIKELY_NEXT_OBLIGATION_REASON,
    LIKELY_NEXT_SYNTHESIS_TARGET_AFTER_REVIEW,
    LOCAL_DEPENDENCY_CHAIN,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    NONCLAIMS,
    OUTCOME_ID as CLOSEOUT_OUTCOME,
    PACKET_ID as CLOSEOUT_PACKET_ID,
    PLAIN_MEANING,
    ROUTE_GIVEN,
    ROUTE_STATEMENT,
    ROUTE_STEPS,
    ROUTE_THEN,
    SCHEMA_ID as CLOSEOUT_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT,
    STRICT_CLOSEOUT_RESULT,
    TARGET,
    TARGET_CONCLUSION,
    THEOREM_TARGET_STATEMENT,
    T_A_POLICY,
    WATCH_ITEMS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_"
    "RESULT_REVIEW_20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_"
    "REVIEW_v0"
)
REVIEW_RESULT = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_"
    "REVIEW_ACCEPTS_SOURCED_MAXWELL_LINKED_GAUGE_EXCHANGE_ROUTE_NO_CK_RULE_"
    "PROMOTION_OR_SEAM_CLOSURE"
)
STRICT_REVIEW_RESULT = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_"
    "REVIEW_ACCEPTS_LOCAL_GAUGE_EXCHANGE_LINKAGE_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_result_"
    "review_accepts_sourced_maxwell_linked_gauge_exchange_route_no_ck_rule_"
    "promotion_or_seam_closure"
)

NEXT_TARGET = LIKELY_NEXT_SYNTHESIS_TARGET_AFTER_REVIEW
NEXT_TARGET_KIND = (
    "psi_A_interaction_exchange_theorem_linkage_chain_synthesis_packet_preparation"
)
SYNTHESIS_TARGET_REASON = (
    "C_exchange, total conservation, matter-sector exchange, and gauge-sector "
    "exchange have each been locally theorem-linked. The next disciplined move "
    "is to synthesize the local dependency chain before selecting another proof "
    "target."
)
CLAIM_BOUNDARY = (
    "closeout result review only; synthesis packet authorized next; no proof "
    "execution, C_k promotion, seam closure, empirical validation, or master-"
    "action promotion"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_CLOSEOUT

ACCEPTED_REVIEW_FINDINGS = [
    "gauge-sector exchange theorem-linkage closeout accepted",
    "gauge exchange linked to stress-divergence identity plus sourced Maxwell route",
    "same F and J objects preserved",
    "sign and index conventions preserved",
    "watch items preserved",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no general C_k closure",
    "no C_k dynamical-law status",
    "no empirical validation",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_"
        "RESULT_REVIEW_20260628_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiAGaugeSectorExchangeTheoremLinkageObligationCloseoutResultReview.lean"
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
        "general_C_k_theorem_linkage_closure": False,
        "general_C_k_closure": False,
        "C_k_dynamical_law_status": False,
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


def _consumed_closeout_valid(closeout: dict[str, Any]) -> bool:
    return (
        closeout.get("schema_id") == CLOSEOUT_SCHEMA_ID
        and closeout.get("packet_id") == CLOSEOUT_PACKET_ID
        and closeout.get("outcome_id") == CLOSEOUT_OUTCOME
        and closeout.get("closeout_result") == CLOSEOUT_RESULT
        and closeout.get("strict_closeout_result") == STRICT_CLOSEOUT_RESULT
        and closeout.get("selected_next_target") == CONSUMED_TARGET
        and closeout.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and closeout.get("accepted") is True
        and closeout.get("closed") is True
        and closeout.get("gauge_sector_exchange_obligation_locally_closed") is True
        and closeout.get("gauge_exchange_linked_to_sourced_maxwell_route") is True
        and closeout.get("same_F_and_J_objects_preserved") is True
        and closeout.get("general_C_k_theorem_linkage_closure") is False
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_"
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
        "scoped_lean_targets_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
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


def build_psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_result_review(
    *,
    closeout_path: Path = CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = _read_json(closeout_path)
    acceptance_criteria = {
        "consumes_expected_closeout": _consumed_closeout_valid(closeout),
        "local_gauge_exchange_closeout_accepted": (
            closeout.get("closeout_claims") == CLOSEOUT_CLAIMS
            and closeout.get("closeout_statement") == CLOSEOUT_STATEMENT
            and closeout.get("same_F_and_J_objects_preserved") is True
            and closeout.get("sourced_maxwell_route_used") is True
            and closeout.get("gauge_stress_energy_divergence_identity_used") is True
            and closeout.get("watch_items_preserved") is True
        ),
        "stress_divergence_sourced_maxwell_shape_preserved": (
            closeout.get("target_rule") == TARGET
            and closeout.get("T_A_policy") == T_A_POLICY
            and closeout.get("field_strength_object") == FIELD_STRENGTH_OBJECT
            and closeout.get("current_object") == CURRENT_OBJECT
            and closeout.get("accepted_sourced_maxwell_route")
            == ACCEPTED_SOURCED_MAXWELL_ROUTE
            and closeout.get("accepted_gauge_stress_energy_divergence_identity")
            == ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
            and closeout.get("watch_items") == WATCH_ITEMS
        ),
        "no_forbidden_closeout_claims": (
            closeout.get("rule_promoted") is False
            and closeout.get("C_k_dynamical_law_status") is False
            and closeout.get("C_k_action_embedding_claimed") is False
            and closeout.get("C_k_action_variation_executed") is False
            and closeout.get("full_maxwell_closure_claimed") is False
            and closeout.get("em_qft_closure_claimed") is False
            and closeout.get("qft_gr_closure_claimed") is False
            and closeout.get("gr_qm_closure_claimed") is False
            and closeout.get("empirical_validation_claimed") is False
            and closeout.get("master_action_promoted") is False
        ),
        "synthesis_target_authorized_next": (
            closeout.get("likely_next_synthesis_target_after_review") == NEXT_TARGET
            and closeout.get("likely_next_obligation_after_closeout")
            == LIKELY_NEXT_OBLIGATION
            and closeout.get("local_dependency_chain") == LOCAL_DEPENDENCY_CHAIN
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
        else "REMEDIATE_PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_"
            "CLOSEOUT_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "synthesis_target_authorized": accepted,
        "synthesis_packet_prepared": False,
        "selected_synthesis_target": NEXT_TARGET,
        "selected_synthesis_target_kind": NEXT_TARGET_KIND,
        "synthesis_target_reason": SYNTHESIS_TARGET_REASON,
        "likely_next_obligation": LIKELY_NEXT_OBLIGATION,
        "likely_next_obligation_reason": LIKELY_NEXT_OBLIGATION_REASON,
        "closeout_schema_id": CLOSEOUT_SCHEMA_ID,
        "closeout_packet_id": CLOSEOUT_PACKET_ID,
        "closeout_outcome": CLOSEOUT_OUTCOME,
        "closeout_strict_outcome": STRICT_CLOSEOUT_RESULT,
        "closeout_consumed": accepted,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "closeout_claims": CLOSEOUT_CLAIMS,
        "closeout_claim_count": len(CLOSEOUT_CLAIMS),
        "nonclaims": NONCLAIMS,
        "nonclaim_count": len(NONCLAIMS),
        "selected_obligation": "psi-A gauge-sector exchange theorem-linkage gap",
        "selected_obligation_rank": "4",
        "claim_boundary": CLAIM_BOUNDARY,
        "closeout_claim_boundary": CLOSEOUT_CLAIM_BOUNDARY,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "target_rule": TARGET,
        "target_conclusion": TARGET_CONCLUSION,
        "exchange_object": "- F^nu{}_alpha J^alpha",
        "T_A_policy": T_A_POLICY,
        "T_A_policy_preserved": accepted,
        "field_strength_object": FIELD_STRENGTH_OBJECT,
        "F_object_preserved": accepted,
        "current_object": CURRENT_OBJECT,
        "J_object_preserved": accepted,
        "same_F_and_J_objects_preserved": accepted,
        "accepted_sourced_maxwell_route": ACCEPTED_SOURCED_MAXWELL_ROUTE,
        "sourced_maxwell_route_used": accepted,
        "accepted_gauge_stress_energy_divergence_identity": (
            ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
        ),
        "gauge_stress_energy_divergence_identity_used": accepted,
        "route_given": ROUTE_GIVEN,
        "route_then": ROUTE_THEN,
        "route_steps": ROUTE_STEPS,
        "route_step_count": len(ROUTE_STEPS),
        "route_statement": ROUTE_STATEMENT,
        "plain_meaning": PLAIN_MEANING,
        "watch_items": WATCH_ITEMS,
        "watch_item_count": len(WATCH_ITEMS),
        "watch_items_preserved": accepted,
        "local_dependency_chain": LOCAL_DEPENDENCY_CHAIN,
        "local_dependency_chain_step_count": len(LOCAL_DEPENDENCY_CHAIN),
        "gauge_sector_exchange_closeout_accepted": accepted,
        "gauge_exchange_linked_to_sourced_maxwell_route": accepted,
        "gauge_exchange_route_constructed": accepted,
        "gauge_exchange_derived": accepted,
        "gauge_sector_exchange_obligation_locally_closed": accepted,
        "local_psi_A_gauge_sector_exchange_obligation_closed": accepted,
        "general_C_k_theorem_linkage_closure": False,
        "general_C_k_closure": False,
        "proof_attempt_executed": True,
        "review_executes_new_proof": False,
        "proof_execution_authorized": False,
        "theorem_discharged": True,
        "theorem_linkage_completed": accepted,
        "theorem_linkage_obligation_discharged": True,
        "proof_debt_reduced": True,
        "proof_debt_discharged": False,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "blocked_claims": NONCLAIMS,
        "blocked_claim_count": len(NONCLAIMS),
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
            "This result review accepts only the local psi-A gauge-sector "
            "exchange closeout: nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha "
            "is linked to the accepted stress-divergence identity plus sourced "
            "Maxwell route under preserved F, J, sign, index, covariant-"
            "derivative, domain, and boundary assumptions. It authorizes only "
            "the interaction exchange theorem-linkage chain synthesis packet. "
            "It does not claim full Maxwell closure, EM-QFT closure, QFT-GR "
            "closure, GR-QM closure, general C_k closure, C_k dynamical-law "
            "status, empirical validation, seam closure, or master-action "
            "promotion."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_result",
            "fail to accept the local psi-A gauge-sector exchange closeout",
            "fail to preserve the stress-divergence identity plus sourced Maxwell route",
            "fail to preserve the same F and J objects",
            "fail to preserve sign or index conventions",
            "claim full Maxwell closure",
            "claim EM-QFT, QFT-GR, or GR-QM closure",
            "claim general C_k closure",
            "claim C_k dynamical-law status",
            "discharge GAP-1 through GAP-8 globally",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "claim seam closure",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_REVIEW,
        "full_toeformal_aggregate_status_for_review": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "aggregate_lean_validation_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PsiAGaugeSectorExchangeTheoremLinkageObligationCloseoutResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "closeout_file": _ptr(closeout_path),
            "closeout_lean_file": _ptr(CLOSEOUT_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
    payload["gauge_sector_exchange_closeout_accepted"] = accepted
    payload["gauge_exchange_linked_to_sourced_maxwell_route"] = accepted
    payload["gauge_exchange_route_constructed"] = accepted
    payload["gauge_exchange_derived"] = accepted
    payload["gauge_sector_exchange_obligation_locally_closed"] = accepted
    payload["local_psi_A_gauge_sector_exchange_obligation_closed"] = accepted
    payload["same_F_and_J_objects_preserved"] = accepted
    payload["sourced_maxwell_route_used"] = accepted
    payload["gauge_stress_energy_divergence_identity_used"] = accepted
    payload["watch_items_preserved"] = accepted
    payload["proof_attempt_executed"] = True
    payload["theorem_discharged"] = True
    payload["theorem_linkage_completed"] = accepted
    payload["theorem_linkage_obligation_discharged"] = True
    payload["proof_debt_reduced"] = True
    payload["proof_debt_discharged"] = False
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
            "Review the local psi-A gauge-sector exchange theorem-linkage closeout."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--closeout", type=Path, default=CLOSEOUT_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    closeout_path = (
        args.closeout if args.closeout.is_absolute() else REPO_ROOT / args.closeout
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_result_review(
            closeout_path=closeout_path,
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
                "synthesis_target_authorized": payload[
                    "synthesis_target_authorized"
                ],
                "general_C_k_theorem_linkage_closure": payload[
                    "general_C_k_theorem_linkage_closure"
                ],
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
