from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_result_review_report import (
    CLOSEOUT_OUTCOME as REVIEW_CLOSEOUT_OUTCOME,
    CLOSEOUT_STATEMENT,
    DEFAULT_OUT as EXECUTION_RESULT_REVIEW_PATH,
    FIELD_EQUATION_MATCH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH as EXECUTION_RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LEAN_STATUS_WORDING_LINES_FOR_REVIEW,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as EXECUTION_RESULT_REVIEW_OUTCOME,
    PACKET_ID as EXECUTION_RESULT_REVIEW_PACKET_ID,
    REVIEW_RESULT as EXECUTION_RESULT_REVIEW_RESULT,
    SCHEMA_ID as EXECUTION_RESULT_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SOURCE_RESIDUAL_MATCH,
    STRESS_ENERGY_MATCH,
    STRICT_CLOSEOUT_OUTCOME as REVIEW_STRICT_CLOSEOUT_OUTCOME,
    STRICT_REVIEW_RESULT as EXECUTION_RESULT_REVIEW_STRICT_OUTCOME,
    TARGET_CONCLUSION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_20260630_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_v0"
CLOSEOUT_RESULT = REVIEW_CLOSEOUT_OUTCOME
STRICT_CLOSEOUT_RESULT = REVIEW_STRICT_CLOSEOUT_OUTCOME
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "phi_bridge_theorem_linkage_obligation_closed_as_standalone_componentwise_"
    "route_match_linked_C_bridge_phi_route_no_ck_rule_promotion_or_seam_"
    "closure"
)

NEXT_TARGET = "review_phi_bridge_theorem_linkage_obligation_closeout_result"
NEXT_TARGET_KIND = "phi_bridge_theorem_linkage_obligation_closeout_result_review"
SUGGESTED_REVIEW_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_"
    "STANDALONE_COMPONENTWISE_ROUTE_MATCH_LINKED_C_BRIDGE_PHI_ROUTE_NO_CK_"
    "RULE_PROMOTION_OR_SEAM_CLOSURE"
)
STRICT_SUGGESTED_REVIEW_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_"
    "LOCAL_C_BRIDGE_PHI_ZERO_ROUTE_NO_ACTION_VARIATION_OR_MASTER_ACTION_"
    "PROMOTION"
)
CLAIM_BOUNDARY = (
    "local C_bridge^phi theorem-linkage only; no phi-sector closure; no "
    "scalar/QFT closure; no QFT-GR closure; no EM-QFT closure; no seam "
    "closure; no general C_k closure; no C_k promotion; no action embedding; "
    "no variation; no empirical validation; no master-action promotion"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT = SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_CLOSEOUT = LEAN_STATUS_WORDING_FOR_REVIEW
LEAN_STATUS_WORDING_LINES_FOR_CLOSEOUT = LEAN_STATUS_WORDING_LINES_FOR_REVIEW

LOCAL_CLOSEOUT_ROUTE = [
    FIELD_EQUATION_MATCH,
    STRESS_ENERGY_MATCH,
    SOURCE_RESIDUAL_MATCH,
    "therefore: C_bridge^phi = 0",
]
LOCAL_CLOSEOUT_ROUTE_TEXT = "; ".join(LOCAL_CLOSEOUT_ROUTE)

CLOSEOUT_CLAIMS = [
    "C_bridge^phi theorem-linkage obligation locally closed",
    "componentwise master/witness route match preserved",
    "C_bridge^phi = 0 locally constructed and reviewed",
    "no phi-sector closure",
    "no scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no seam closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]

NONCLAIMS = [
    "no phi-sector closure",
    "no scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no seam closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_20260630_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiBridgeTheoremLinkageObligationCloseout.lean"
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
        "C_source_phi_route_reused": False,
        "C_bridge_phi_route_reused_from_C_source_phi": False,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "QFT_GR_route_imported": False,
        "QFT_GR_source_route_imported": False,
        "J_current_imported": False,
        "master_action_route_substituted": False,
        "new_bridge_formula_invented": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "field_equation_match_proved": False,
        "stress_energy_match_proved": False,
        "source_residual_match_proved": False,
        "C_source_phi_closure_claimed": False,
        "C_bridge_phi_closure_claimed": False,
        "phi_sector_closure_claimed": False,
        "full_scalar_qft_closure_claimed": False,
        "full_scalar_QFT_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "general_C_k_theorem_linkage_closure": False,
        "general_C_k_closure": False,
        "C_k_dynamical_law_status": False,
        "C_k_rule_promotion_authorized": False,
        "C_k_rule_promoted": False,
        "rule_promoted": False,
        "C_k_action_embedding_claimed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_authorized": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "action_embedding_claimed": False,
        "action_variation_executed": False,
        "multiplier_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_claimed": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
    }


def _theorem_target_shape() -> dict[str, Any]:
    return {
        "given": [
            FIELD_EQUATION_MATCH,
            STRESS_ENERGY_MATCH,
            SOURCE_RESIDUAL_MATCH,
        ],
        "therefore": TARGET_CONCLUSION,
        "route": LOCAL_CLOSEOUT_ROUTE,
    }


def _input_boundary_clear(review: dict[str, Any]) -> bool:
    return all(
        review.get(key) is False
        for key in _blocked_boundary_flags()
        if key in review
    )


def _consumed_review_valid(review: dict[str, Any]) -> bool:
    return (
        review.get("schema_id") == EXECUTION_RESULT_REVIEW_SCHEMA_ID
        and review.get("packet_id") == EXECUTION_RESULT_REVIEW_PACKET_ID
        and review.get("outcome_id") == EXECUTION_RESULT_REVIEW_OUTCOME
        and review.get("review_result") == EXECUTION_RESULT_REVIEW_RESULT
        and review.get("strict_review_result") == EXECUTION_RESULT_REVIEW_STRICT_OUTCOME
        and review.get("selected_next_target") == CONSUMED_TARGET
        and review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and review.get("closeout_outcome") == REVIEW_CLOSEOUT_OUTCOME
        and review.get("strict_closeout_outcome") == REVIEW_STRICT_CLOSEOUT_OUTCOME
        and review.get("accepted") is True
        and review.get("reviewed") is True
        and review.get("field_equation_match") == FIELD_EQUATION_MATCH
        and review.get("stress_energy_match") == STRESS_ENERGY_MATCH
        and review.get("source_residual_match") == SOURCE_RESIDUAL_MATCH
        and review.get("target_conclusion") == TARGET_CONCLUSION
        and review.get("C_bridge_phi_zero_derived") is True
        and review.get("C_bridge_phi_linkage_constructed") is True
        and review.get("theorem_linkage_obligation_discharged") is True
        and _input_boundary_clear(review)
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "phi_bridge_theorem_linkage_obligation_closeout",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "full_toeformal_aggregate_status_for_closeout": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
        ),
        "scoped_lean_targets_status_for_closeout": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
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


def build_phi_bridge_theorem_linkage_obligation_closeout(
    *,
    execution_result_review_path: Path = EXECUTION_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(execution_result_review_path)
    acceptance_criteria = {
        "consumed_expected_execution_result_review": _consumed_review_valid(review),
        "local_route_preserved": (
            review.get("field_equation_match") == FIELD_EQUATION_MATCH
            and review.get("stress_energy_match") == STRESS_ENERGY_MATCH
            and review.get("source_residual_match") == SOURCE_RESIDUAL_MATCH
            and review.get("target_conclusion") == TARGET_CONCLUSION
        ),
        "constructed_and_reviewed": (
            review.get("C_bridge_phi_zero_derived") is True
            and review.get("C_bridge_phi_linkage_constructed") is True
            and review.get("reviewed") is True
            and review.get("result_review_accepted") is True
        ),
        "no_new_proof_or_promotion": (
            review.get("review_executes_attempt") is False
            and review.get("proof_execution_authorized") is False
            and review.get("rule_promoted") is False
            and review.get("master_action_promoted") is False
            and review.get("seam_closure_claim") is False
        ),
        "lean_status_wording_careful": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "closed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_REQUIRES_REMEDIATION",
        "closeout_result": OUTCOME_ID
        if accepted
        else "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_REQUIRES_REMEDIATION",
        "strict_closeout_result": STRICT_CLOSEOUT_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "suggested_review_outcome": SUGGESTED_REVIEW_OUTCOME,
        "strict_suggested_review_outcome": STRICT_SUGGESTED_REVIEW_OUTCOME,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "execution_result_review_schema_id": EXECUTION_RESULT_REVIEW_SCHEMA_ID,
        "execution_result_review_packet_id": EXECUTION_RESULT_REVIEW_PACKET_ID,
        "execution_result_review_outcome": EXECUTION_RESULT_REVIEW_OUTCOME,
        "execution_result_review_strict_outcome": (
            EXECUTION_RESULT_REVIEW_STRICT_OUTCOME
        ),
        "execution_result_review_consumed": accepted,
        "selected_obligation": "C_bridge^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_bridge^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_bridge^phi",
        "claim_boundary": CLAIM_BOUNDARY,
        "main_boundary": CLAIM_BOUNDARY,
        "closeout_claims": CLOSEOUT_CLAIMS,
        "closeout_claim_count": len(CLOSEOUT_CLAIMS),
        "nonclaims": NONCLAIMS,
        "nonclaim_count": len(NONCLAIMS),
        "theorem_target_shape": _theorem_target_shape(),
        "local_closeout_route": LOCAL_CLOSEOUT_ROUTE,
        "local_closeout_route_text": LOCAL_CLOSEOUT_ROUTE_TEXT,
        "field_equation_match": FIELD_EQUATION_MATCH,
        "stress_energy_match": STRESS_ENERGY_MATCH,
        "source_residual_match": SOURCE_RESIDUAL_MATCH,
        "target_conclusion": TARGET_CONCLUSION,
        "linkage_route": LOCAL_CLOSEOUT_ROUTE,
        "route_kind": "standalone_phi_bridge_componentwise_route_match",
        "local_phi_bridge_theorem_linkage_obligation_closed": accepted,
        "phi_bridge_theorem_linkage_obligation_locally_closed": accepted,
        "phi_bridge_theorem_linkage_obligation_discharged": accepted,
        "componentwise_master_witness_route_match_preserved": accepted,
        "C_bridge_phi_zero_constructed": accepted,
        "C_bridge_phi_zero_derived": accepted,
        "C_bridge_phi_discharged": accepted,
        "C_bridge_phi_linkage_constructed": accepted,
        "constructed_and_reviewed": accepted,
        "local_theorem_linkage_reduced": accepted,
        "proof_attempt_executed": True,
        "closeout_executes_new_proof": False,
        "proof_execution_authorized": False,
        "theorem_discharged": True,
        "theorem_linkage_completed": accepted,
        "theorem_linkage_obligation_discharged": accepted,
        "proof_debt_reduced": accepted,
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
            "below phi-sector closure, scalar/QFT closure, QFT-GR closure, "
            "EM-QFT closure, seam closure, empirical confirmation, and mature "
            "physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This closeout records only that the local C_bridge^phi "
            "theorem-linkage obligation is closed by the componentwise "
            "master/witness route match: E_phi^master = E_phi^witness, "
            "T_phi^master = T_phi^witness, and C_source^phi = nabla_mu "
            "T_phi^{mu nu}; therefore C_bridge^phi = 0. It claims no "
            "phi-sector closure, no scalar/QFT closure, no QFT-GR closure, "
            "no EM-QFT closure, no seam closure, no general C_k closure, no "
            "C_k promotion, no action embedding, no variation, no empirical "
            "validation, and no master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_phi_bridge_theorem_linkage_obligation_closeout",
            "fail to close the local C_bridge^phi theorem-linkage obligation",
            "fail to preserve E_phi^master = E_phi^witness",
            "fail to preserve T_phi^master = T_phi^witness",
            "fail to preserve C_source^phi = nabla_mu T_phi^{mu nu}",
            "fail to preserve C_bridge^phi = 0",
            "claim phi-sector closure",
            "claim scalar/QFT closure",
            "claim QFT-GR closure",
            "claim EM-QFT closure",
            "claim general C_k closure",
            "promote any C_k rule",
            "embed or vary an action",
            "claim empirical validation",
            "claim seam closure",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_CLOSEOUT,
        "lean_status_wording_lines": LEAN_STATUS_WORDING_LINES_FOR_CLOSEOUT,
        "full_toeformal_aggregate_status_for_closeout": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
        ),
        "scoped_lean_targets_status_for_closeout": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
        ),
        "aggregate_lean_validation_status_for_closeout": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiBridgeTheoremLinkageObligationCloseout",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "execution_result_review_file": _ptr(execution_result_review_path),
            "execution_result_review_lean_file": _ptr(
                EXECUTION_RESULT_REVIEW_LEAN_PACKET_PATH
            ),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
    payload["proof_attempt_executed"] = True
    payload["theorem_discharged"] = True
    payload["theorem_linkage_completed"] = accepted
    payload["theorem_linkage_obligation_discharged"] = accepted
    payload["phi_bridge_theorem_linkage_obligation_discharged"] = accepted
    payload["C_bridge_phi_discharged"] = accepted
    payload["C_bridge_phi_zero_derived"] = accepted
    payload["C_bridge_phi_linkage_constructed"] = accepted
    payload["rule_promoted"] = False
    return payload


def write_closeout(closeout: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(closeout, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Close out the local standalone phi-bridge theorem-linkage obligation."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--review", type=Path, default=EXECUTION_RESULT_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = args.review if args.review.is_absolute() else REPO_ROOT / args.review
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_phi_bridge_theorem_linkage_obligation_closeout(
        execution_result_review_path=review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_closeout(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "closeout_result": payload["closeout_result"],
                "selected_next_target": payload["selected_next_target"],
                "phi_bridge_theorem_linkage_obligation_locally_closed": payload[
                    "phi_bridge_theorem_linkage_obligation_locally_closed"
                ],
                "phi_sector_closure_claimed": payload[
                    "phi_sector_closure_claimed"
                ],
                "qft_gr_closure_claimed": payload["qft_gr_closure_claimed"],
                "seam_closure_claim": payload["seam_closure_claim"],
                "rule_promoted": payload["rule_promoted"],
                "master_action_promoted": payload["master_action_promoted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if payload["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
