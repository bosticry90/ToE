from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.A_source_theorem_linkage_obligation_closeout_report import (
    C_SOURCE_A_RESIDUAL_DEFINITION,
    CLAIM_BOUNDARY as CLOSEOUT_CLAIM_BOUNDARY,
    CLOSEOUT_CLAIMS,
    CLOSEOUT_RESULT,
    CLOSEOUT_STATEMENT,
    DEFAULT_OUT as CLOSEOUT_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_CLOSEOUT,
    LINKAGE_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    NONCLAIMS,
    OUTCOME_ID as CLOSEOUT_OUTCOME,
    PACKET_ID as CLOSEOUT_PACKET_ID,
    PLAIN_MEANING,
    SCHEMA_ID as CLOSEOUT_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT,
    SOURCE_ADMISSIBILITY_CONDITION,
    STRICT_CLOSEOUT_RESULT,
    TARGET_CONCLUSION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_"
    "STANDALONE_STRESS_CONSERVATION_LINKED_C_SOURCE_A_ROUTE_NO_CK_RULE_PROMOTION_"
    "OR_SEAM_CLOSURE"
)
STRICT_REVIEW_RESULT = (
    "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_LOCAL_"
    "C_SOURCE_A_ZERO_ROUTE_NO_SOURCED_MAXWELL_SUBSTITUTION_OR_MASTER_ACTION_"
    "PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "A_source_theorem_linkage_obligation_closeout_result_review_accepts_"
    "standalone_stress_conservation_linked_C_source_A_route_no_ck_rule_promotion_"
    "or_seam_closure"
)

NEXT_TARGET = "select_next_ck_family_theorem_linkage_obligation_after_A_source_closeout"
NEXT_TARGET_KIND = "ck_family_theorem_linkage_obligation_selector_after_A_source_closeout"
LIKELY_NEXT_OBLIGATION = "C_source^phi theorem-linkage obligation"
LIKELY_NEXT_OBLIGATION_ROW_ID = "C_source^phi"
LIKELY_SELECTOR_OUTCOME = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_A_SOURCE_CLOSEOUT_"
    "SELECTS_C_SOURCE_PHI_THEOREM_LINKAGE_GAP_NO_PROOF_EXECUTION_OR_MASTER_"
    "ACTION_PROMOTION"
)
STRICT_LIKELY_SELECTOR_OUTCOME = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_A_SOURCE_CLOSEOUT_"
    "SELECTS_PHI_SOURCE_LINKAGE_OBLIGATION_NO_GAP_DISCHARGE_OR_CK_RULE_PROMOTION"
)
NEXT_OBLIGATION_REASON = (
    "The standalone A-source theorem-linkage obligation is locally closed. The "
    "next bounded action is a selector pass over the remaining C_k-family "
    "theorem-linkage gaps, with C_source^phi retained as the likely next "
    "obligation from the prior ranked order."
)
CLAIM_BOUNDARY = (
    "A-source closeout result review only; selector authorized next; no theorem "
    "execution, seam closure, phi-sector closure, or master-action promotion"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_CLOSEOUT

ACCEPTED_REVIEW_FINDINGS = [
    "A-source theorem-linkage obligation closeout accepted",
    "C_source^{A,nu} definition preserved",
    "standalone stress-conservation route preserved",
    "C_source^{A,nu} = 0 locally linked",
    "no J current imported",
    "no psi-A sourced Maxwell substitution",
    "no sourced Maxwell closure",
    "no full Maxwell closure",
    "no A-sector closure",
    "no seam closure",
    "no C_k promotion",
    "no empirical validation",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_20260628_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ASourceTheoremLinkageObligationCloseoutResultReview.lean"
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
        "J_current_imported": False,
        "J_imported": False,
        "psi_A_sourced_route_substituted": False,
        "psi_A_sourced_Maxwell_substitution": False,
        "sourced_Maxwell_route_substituted": False,
        "sourced_maxwell_closure_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "C_source_A_closure_claimed": False,
        "A_sector_closure_claimed": False,
        "phi_sector_closure_claimed": False,
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
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "gap_1_through_gap_8_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "obligation_row_discharged": False,
        "obligation_rows_discharged": False,
        "proof_debt_discharged": False,
        "new_physics_created": False,
        "external_benchmark_intake_executed": False,
        "external_benchmark_validation_claimed": False,
    }


def _theorem_target_shape() -> dict[str, Any]:
    return {
        "given": [
            C_SOURCE_A_RESIDUAL_DEFINITION,
            SOURCE_ADMISSIBILITY_CONDITION,
        ],
        "therefore": TARGET_CONCLUSION,
        "route": LINKAGE_ROUTE,
        "plain_meaning": PLAIN_MEANING,
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
        and closeout.get("closeout_statement") == CLOSEOUT_STATEMENT
        and closeout.get("C_source_A_residual_definition")
        == C_SOURCE_A_RESIDUAL_DEFINITION
        and closeout.get("source_admissibility_condition")
        == SOURCE_ADMISSIBILITY_CONDITION
        and closeout.get("target_conclusion") == TARGET_CONCLUSION
        and closeout.get("execution_route") == LINKAGE_ROUTE
        and closeout.get("C_source_A_zero_constructed") is True
        and closeout.get("C_source_A_zero_derived") is True
        and closeout.get("theorem_linkage_completed") is True
        and closeout.get("J_current_imported") is False
        and closeout.get("psi_A_sourced_route_substituted") is False
        and closeout.get("sourced_maxwell_closure_claimed") is False
        and closeout.get("full_maxwell_closure_claimed") is False
        and closeout.get("A_sector_closure_claimed") is False
        and closeout.get("seam_closure_claim") is False
        and closeout.get("rule_promoted") is False
        and closeout.get("master_action_promoted") is False
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "A_source_theorem_linkage_obligation_closeout_result_review"
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


def build_A_source_theorem_linkage_obligation_closeout_result_review(
    *,
    closeout_path: Path = CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = _read_json(closeout_path)
    acceptance_criteria = {
        "consumes_expected_A_source_closeout": _closeout_valid(closeout),
        "standalone_A_source_route_preserved": (
            closeout.get("C_source_A_residual_definition")
            == C_SOURCE_A_RESIDUAL_DEFINITION
            and closeout.get("source_admissibility_condition")
            == SOURCE_ADMISSIBILITY_CONDITION
            and closeout.get("target_conclusion") == TARGET_CONCLUSION
            and closeout.get("execution_route") == LINKAGE_ROUTE
        ),
        "local_zero_linkage_accepted": (
            closeout.get("A_source_theorem_linkage_obligation_locally_closed")
            is True
            and closeout.get("C_source_A_zero_constructed") is True
            and closeout.get("C_source_A_zero_derived") is True
            and closeout.get("constructed_and_reviewed") is True
        ),
        "no_forbidden_closeout_claims": (
            closeout.get("J_current_imported") is False
            and closeout.get("psi_A_sourced_route_substituted") is False
            and closeout.get("sourced_maxwell_closure_claimed") is False
            and closeout.get("full_maxwell_closure_claimed") is False
            and closeout.get("A_sector_closure_claimed") is False
            and closeout.get("seam_closure_claim") is False
            and closeout.get("rule_promoted") is False
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
        else "REMEDIATE_A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "likely_next_obligation": LIKELY_NEXT_OBLIGATION,
        "likely_next_obligation_row_id": LIKELY_NEXT_OBLIGATION_ROW_ID,
        "likely_selector_outcome": LIKELY_SELECTOR_OUTCOME,
        "strict_likely_selector_outcome": STRICT_LIKELY_SELECTOR_OUTCOME,
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
        "selected_obligation": "C_source^A theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_source^A theorem-linkage gap",
        "selected_obligation_row_id": "C_source^A",
        "claim_boundary": CLAIM_BOUNDARY,
        "closeout_claim_boundary": CLOSEOUT_CLAIM_BOUNDARY,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "theorem_target_shape": _theorem_target_shape(),
        "standalone_A_stress_conservation_route": SOURCE_ADMISSIBILITY_CONDITION,
        "C_source_A_residual_definition": C_SOURCE_A_RESIDUAL_DEFINITION,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "target_conclusion": TARGET_CONCLUSION,
        "execution_route": LINKAGE_ROUTE,
        "linkage_route": LINKAGE_ROUTE,
        "route_kind": "standalone_A_stress_conservation",
        "plain_meaning": PLAIN_MEANING,
        "A_source_closeout_result_review_accepted": accepted,
        "A_source_theorem_linkage_obligation_closeout_accepted": accepted,
        "A_source_theorem_linkage_obligation_locally_closed": accepted,
        "C_source_A_definition_preserved": accepted,
        "standalone_A_stress_conservation_route_preserved": accepted,
        "standalone_A_stress_conservation_input_preserved": accepted,
        "C_source_A_zero_locally_linked": accepted,
        "C_source_A_zero_constructed": accepted,
        "C_source_A_zero_derived": accepted,
        "definition_linkage_constructed": accepted,
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
        "likely_next_obligation_from_priority_list": LIKELY_NEXT_OBLIGATION,
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
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "external_benchmark_handling": (
            "Fractional Fermi sea and lattice unitarity examples are retained "
            "only as possible future external benchmark candidates; no current "
            "A-source lane intake, validation, or authority promotion is executed."
        ),
        "non_claim_boundary": (
            "This result review accepts only that the local A-source "
            "theorem-linkage closeout is clean: C_source^{A,nu} is defined as "
            "nabla_mu T_A^{mu nu}, the standalone A-sector stress divergence is "
            "zero, and therefore C_source^{A,nu} = 0. It authorizes only the "
            "next C_k-family theorem-linkage obligation selector. It imports no "
            "J current, substitutes no psi-A sourced Maxwell route, claims no "
            "sourced or full Maxwell closure, claims no A-sector closure, "
            "claims no phi-sector closure, closes no seam, promotes no C_k "
            "rule, embeds or varies no action, claims no empirical validation, "
            "does not validate the ToE from external benchmarks, and does not "
            "promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_A_source_theorem_linkage_obligation_closeout_result",
            "fail to accept the local A-source theorem-linkage closeout",
            "fail to preserve C_source^{A,nu} := nabla_mu T_A^{mu nu}",
            "fail to preserve nabla_mu T_A^{mu nu} = 0",
            "fail to preserve C_source^{A,nu} = 0",
            "import a J current",
            "substitute the psi-A sourced Maxwell route",
            "claim sourced or full Maxwell closure",
            "claim A-sector closure",
            "claim phi-sector closure",
            "claim seam closure",
            "promote any C_k rule",
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
            "ToeFormal.Derivation.ASourceTheoremLinkageObligationCloseoutResultReview",
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
        description="Review the local A-source theorem-linkage closeout result."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--closeout", type=Path, default=CLOSEOUT_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    closeout_path = (
        args.closeout if args.closeout.is_absolute() else REPO_ROOT / args.closeout
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_A_source_theorem_linkage_obligation_closeout_result_review(
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
                "J_current_imported": payload["J_current_imported"],
                "psi_A_sourced_route_substituted": payload[
                    "psi_A_sourced_route_substituted"
                ],
                "seam_closure_claim": payload["seam_closure_claim"],
                "rule_promoted": payload["rule_promoted"],
                "master_action_promoted": payload["master_action_promoted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
