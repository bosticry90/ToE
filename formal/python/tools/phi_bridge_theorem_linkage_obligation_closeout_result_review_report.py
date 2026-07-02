from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_result_review_report import (
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
)
from formal.python.tools.phi_bridge_theorem_linkage_obligation_closeout_report import (
    CLAIM_BOUNDARY as CLOSEOUT_CLAIM_BOUNDARY,
    CLOSEOUT_CLAIMS,
    CLOSEOUT_RESULT,
    CLOSEOUT_STATEMENT,
    DEFAULT_OUT as CLOSEOUT_PATH,
    FIELD_EQUATION_MATCH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_CLOSEOUT,
    LEAN_STATUS_WORDING_LINES_FOR_CLOSEOUT,
    LOCAL_CLOSEOUT_ROUTE,
    LOCAL_CLOSEOUT_ROUTE_TEXT,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    NONCLAIMS,
    OUTCOME_ID as CLOSEOUT_OUTCOME,
    PACKET_ID as CLOSEOUT_PACKET_ID,
    SCHEMA_ID as CLOSEOUT_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT,
    SOURCE_RESIDUAL_MATCH,
    STRESS_ENERGY_MATCH,
    STRICT_CLOSEOUT_RESULT,
    TARGET_CONCLUSION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_20260630_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_"
    "STANDALONE_COMPONENTWISE_ROUTE_MATCH_LINKED_C_BRIDGE_PHI_ROUTE_NO_CK_"
    "RULE_PROMOTION_OR_SEAM_CLOSURE"
)
STRICT_REVIEW_RESULT = (
    "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_"
    "LOCAL_C_BRIDGE_PHI_ZERO_ROUTE_NO_ACTION_VARIATION_OR_MASTER_ACTION_"
    "PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_bridge_theorem_linkage_obligation_closeout_result_review_accepts_"
    "standalone_componentwise_route_match_linked_C_bridge_phi_route_no_ck_"
    "rule_promotion_or_seam_closure"
)

NEXT_TARGET = "select_next_ck_family_theorem_linkage_obligation_after_phi_bridge_closeout"
NEXT_TARGET_KIND = "ck_family_theorem_linkage_obligation_selector_after_phi_bridge_closeout"
LIKELY_NEXT_OBLIGATION = "C_transport^phi theorem-linkage obligation"
SELECTOR_QUESTION = (
    "Which remaining C_k theorem-linkage obligation should be attempted next "
    "after C_bridge^phi closeout?"
)
NEXT_OBLIGATION_REASON = (
    "The local phi C_k sequence is C_source^phi -> C_bridge^phi -> "
    "C_transport^phi, so C_transport^phi is the likely next theorem-linkage "
    "obligation for the selector to evaluate."
)
CLAIM_BOUNDARY = (
    "local C_bridge^phi theorem-linkage closeout review only; no phi-sector "
    "closure; no scalar/QFT closure; no QFT-GR closure; no EM-QFT closure; "
    "no seam closure; no general C_k closure; no C_k promotion; no action "
    "embedding; no variation; no empirical validation; no master-action "
    "promotion"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_CLOSEOUT
LEAN_STATUS_WORDING_LINES_FOR_REVIEW = LEAN_STATUS_WORDING_LINES_FOR_CLOSEOUT

ACCEPTED_REVIEW_FINDINGS = [
    "phi-bridge theorem-linkage obligation closeout accepted",
    "standalone componentwise route match preserved",
    "C_bridge^phi tuple definition preserved",
    "E_phi master/witness equality preserved",
    "T_phi master/witness equality preserved",
    "C_source^phi divergence-match equality preserved",
    "C_bridge^phi = 0 locally constructed, reviewed, and closed",
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
    / "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_20260630_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiBridgeTheoremLinkageObligationCloseoutResultReview.lean"
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
        "phi_sector_closure_claimed": False,
        "full_scalar_qft_closure_claimed": False,
        "full_scalar_QFT_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "general_C_k_theorem_linkage_closure": False,
        "general_C_k_closure": False,
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
        "selector_executed": False,
        "next_theorem_linkage_obligation_selected": False,
    }


def _closeout_valid(closeout: dict[str, Any]) -> bool:
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
        and closeout.get("closeout_claims") == CLOSEOUT_CLAIMS
        and closeout.get("nonclaims") == NONCLAIMS
        and closeout.get("field_equation_match") == FIELD_EQUATION_MATCH
        and closeout.get("stress_energy_match") == STRESS_ENERGY_MATCH
        and closeout.get("source_residual_match") == SOURCE_RESIDUAL_MATCH
        and closeout.get("target_conclusion") == TARGET_CONCLUSION
        and closeout.get("local_closeout_route") == LOCAL_CLOSEOUT_ROUTE
        and closeout.get("C_bridge_phi_zero_constructed") is True
        and closeout.get("C_bridge_phi_zero_derived") is True
        and closeout.get("C_bridge_phi_discharged") is True
        and closeout.get("phi_sector_closure_claimed") is False
        and closeout.get("full_scalar_qft_closure_claimed") is False
        and closeout.get("qft_gr_closure_claimed") is False
        and closeout.get("em_qft_closure_claimed") is False
        and closeout.get("general_C_k_closure") is False
        and closeout.get("seam_closure_claim") is False
        and closeout.get("rule_promoted") is False
        and closeout.get("master_action_promoted") is False
    )


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


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "phi_bridge_theorem_linkage_obligation_closeout_result_review",
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


def build_phi_bridge_theorem_linkage_obligation_closeout_result_review(
    *,
    closeout_path: Path = CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = _read_json(closeout_path)
    acceptance_criteria = {
        "consumes_expected_phi_bridge_closeout": _closeout_valid(closeout),
        "componentwise_route_match_preserved": (
            closeout.get("field_equation_match") == FIELD_EQUATION_MATCH
            and closeout.get("stress_energy_match") == STRESS_ENERGY_MATCH
            and closeout.get("source_residual_match") == SOURCE_RESIDUAL_MATCH
            and closeout.get("target_conclusion") == TARGET_CONCLUSION
            and closeout.get("local_closeout_route") == LOCAL_CLOSEOUT_ROUTE
        ),
        "local_zero_linkage_accepted": (
            closeout.get("phi_bridge_theorem_linkage_obligation_locally_closed")
            is True
            and closeout.get("C_bridge_phi_zero_constructed") is True
            and closeout.get("C_bridge_phi_zero_derived") is True
            and closeout.get("constructed_and_reviewed") is True
        ),
        "no_forbidden_closeout_claims": (
            closeout.get("phi_sector_closure_claimed") is False
            and closeout.get("full_scalar_qft_closure_claimed") is False
            and closeout.get("qft_gr_closure_claimed") is False
            and closeout.get("em_qft_closure_claimed") is False
            and closeout.get("general_C_k_closure") is False
            and closeout.get("seam_closure_claim") is False
            and closeout.get("rule_promoted") is False
            and closeout.get("action_embedding_claimed") is False
            and closeout.get("action_variation_executed") is False
            and closeout.get("empirical_validation_claimed") is False
            and closeout.get("master_action_promoted") is False
        ),
        "selector_target_authorized_next": (
            closeout.get("selected_next_target") == CONSUMED_TARGET
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
        else "REMEDIATE_PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID if accepted else "PHI_BRIDGE_CLOSEOUT_REVIEW_REMEDIATION",
        "review_result": OUTCOME_ID if accepted else "PHI_BRIDGE_CLOSEOUT_REVIEW_REMEDIATION",
        "packet_result": OUTCOME_ID if accepted else "PHI_BRIDGE_CLOSEOUT_REVIEW_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selector_question": SELECTOR_QUESTION,
        "likely_next_obligation": LIKELY_NEXT_OBLIGATION,
        "next_obligation_reason": NEXT_OBLIGATION_REASON,
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
        "selected_obligation": "C_bridge^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_bridge^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_bridge^phi",
        "claim_boundary": CLAIM_BOUNDARY,
        "main_boundary": CLAIM_BOUNDARY,
        "closeout_claim_boundary": CLOSEOUT_CLAIM_BOUNDARY,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "theorem_target_shape": _theorem_target_shape(),
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "field_equation_match": FIELD_EQUATION_MATCH,
        "stress_energy_match": STRESS_ENERGY_MATCH,
        "source_residual_match": SOURCE_RESIDUAL_MATCH,
        "target_conclusion": TARGET_CONCLUSION,
        "local_closeout_route": LOCAL_CLOSEOUT_ROUTE,
        "local_closeout_route_text": LOCAL_CLOSEOUT_ROUTE_TEXT,
        "linkage_route": LOCAL_CLOSEOUT_ROUTE,
        "route_kind": "standalone_phi_bridge_componentwise_route_match_closeout_review",
        "phi_bridge_closeout_result_review_accepted": accepted,
        "phi_bridge_theorem_linkage_obligation_closeout_accepted": accepted,
        "phi_bridge_theorem_linkage_obligation_locally_closed": accepted,
        "standalone_componentwise_route_match_preserved": accepted,
        "componentwise_master_witness_route_match_preserved": accepted,
        "exact_tuple_definition_preserved": accepted,
        "E_phi_master_witness_equality_preserved": accepted,
        "T_phi_master_witness_equality_preserved": accepted,
        "C_source_phi_divergence_match_equality_preserved": accepted,
        "C_bridge_phi_zero_locally_linked": accepted,
        "C_bridge_phi_zero_constructed": accepted,
        "C_bridge_phi_zero_derived": accepted,
        "C_bridge_phi_discharged": accepted,
        "constructed_and_reviewed": accepted,
        "review_executes_new_proof": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": True,
        "theorem_discharged": True,
        "theorem_linkage_completed": accepted,
        "theorem_linkage_obligation_discharged": True,
        "proof_debt_reduced": True,
        "proof_debt_discharged": False,
        "selector_authorized": accepted,
        "selector_executed": False,
        "next_theorem_linkage_obligation_selected": False,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
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
            "This result review accepts only the local C_bridge^phi closeout: "
            "E_phi^master = E_phi^witness, T_phi^master = T_phi^witness, and "
            "C_source^phi = nabla_mu T_phi^{mu nu}; therefore C_bridge^phi = 0. "
            "It authorizes only the next C_k-family theorem-linkage obligation "
            "selector and records C_transport^phi only as the likely next "
            "obligation. It claims no phi-sector closure, no scalar/QFT closure, "
            "no QFT-GR closure, no EM-QFT closure, no seam closure, no general "
            "C_k closure, no C_k promotion, no action embedding, no variation, "
            "no empirical validation, and no master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_phi_bridge_theorem_linkage_obligation_closeout_result",
            "fail to accept the local phi-bridge theorem-linkage closeout",
            "fail to preserve the C_bridge^phi tuple definition",
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
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_REVIEW,
        "lean_status_wording_lines": LEAN_STATUS_WORDING_LINES_FOR_REVIEW,
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
            "ToeFormal.Derivation.PhiBridgeTheoremLinkageObligationCloseoutResultReview",
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
    payload["proof_attempt_executed"] = True
    payload["theorem_discharged"] = True
    payload["theorem_linkage_completed"] = accepted
    payload["theorem_linkage_obligation_discharged"] = True
    payload["proof_debt_reduced"] = True
    payload["proof_debt_discharged"] = False
    payload["selector_authorized"] = accepted
    payload["selector_executed"] = False
    payload["next_theorem_linkage_obligation_selected"] = False
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
        description="Review the local phi-bridge theorem-linkage closeout result."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--closeout", type=Path, default=CLOSEOUT_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    closeout_path = (
        args.closeout if args.closeout.is_absolute() else REPO_ROOT / args.closeout
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_phi_bridge_theorem_linkage_obligation_closeout_result_review(
        closeout_path=closeout_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_result_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
                "selected_next_target": payload["selected_next_target"],
                "likely_next_obligation": payload["likely_next_obligation"],
                "phi_sector_closure_claimed": payload["phi_sector_closure_claimed"],
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
