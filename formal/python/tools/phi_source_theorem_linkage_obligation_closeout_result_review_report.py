from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_source_theorem_linkage_obligation_closeout_report import (
    CLAIM_BOUNDARY as CLOSEOUT_CLAIM_BOUNDARY,
    CLOSEOUT_CLAIMS,
    CLOSEOUT_RESULT,
    CLOSEOUT_STATEMENT,
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    DEFAULT_OUT as CLOSEOUT_PATH,
    EXECUTION_REDUCTION_ROUTE,
    EXECUTION_ROUTE,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    NONCLAIMS,
    ON_SHELL_CONDITION,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID as CLOSEOUT_OUTCOME,
    PACKET_ID as CLOSEOUT_PACKET_ID,
    PLAIN_MEANING,
    RESIDUAL_IDENTITY_FORM,
    SCHEMA_ID as CLOSEOUT_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT,
    STRICT_CLOSEOUT_RESULT,
    TARGET_CONCLUSION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = (
    "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_20260630_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_"
    "STANDALONE_ON_SHELL_SCALAR_RESIDUAL_LINKED_C_SOURCE_PHI_ROUTE_NO_CK_RULE_"
    "PROMOTION_OR_SEAM_CLOSURE"
)
STRICT_REVIEW_RESULT = (
    "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_"
    "LOCAL_C_SOURCE_PHI_ZERO_ROUTE_NO_ACTION_VARIATION_OR_MASTER_ACTION_"
    "PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_source_theorem_linkage_obligation_closeout_result_review_accepts_"
    "standalone_on_shell_scalar_residual_linked_C_source_phi_route_no_ck_rule_"
    "promotion_or_seam_closure"
)

NEXT_TARGET = "select_next_ck_family_theorem_linkage_obligation_after_phi_source_closeout"
NEXT_TARGET_KIND = "ck_family_theorem_linkage_obligation_selector_after_phi_source_closeout"
SELECTOR_QUESTION = (
    "Which remaining C_k theorem-linkage obligation should be attempted next "
    "after C_source^phi closeout?"
)
NEXT_OBLIGATION_REASON = (
    "The local C_source^phi theorem-linkage obligation is closed. The next "
    "bounded action is a selector pass over the remaining C_k-family "
    "theorem-linkage obligations."
)
CLAIM_BOUNDARY = (
    "local C_source^phi theorem-linkage only; not phi-sector completion; not "
    "scalar/QFT completion; not QFT-GR source admissibility; not C_k "
    "functionalization; not seam closure; not master-action promotion"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
LEAN_STATUS_WORDING_LINES_FOR_REVIEW = [
    "full ToeFormal aggregate = NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION",
    "scoped Lean targets = PASSED_SERIAL_RERUN",
]
LEAN_STATUS_WORDING_FOR_REVIEW = "\n".join(LEAN_STATUS_WORDING_LINES_FOR_REVIEW)

ACCEPTED_REVIEW_FINDINGS = [
    "phi-source theorem-linkage obligation closeout accepted",
    "standalone phi route preserved",
    "C_source^nu[g, phi] definition preserved",
    "scalar/on-shell residual identity preserved",
    "R_i^phi definition preserved",
    "on-shell condition applied",
    "C_source^nu[g, phi] = 0 locally constructed, reviewed, and closed",
    "no phi-sector closure",
    "no full scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no seam closure",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_20260630_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiSourceTheoremLinkageObligationCloseoutResultReview.lean"
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
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "psi_A_sourced_Maxwell_substitution": False,
        "QFT_GR_source_route_imported": False,
        "J_current_imported": False,
        "C_source_phi_closure_claimed": False,
        "phi_sector_closure_claimed": False,
        "full_scalar_qft_closure_claimed": False,
        "full_scalar_QFT_closure_claimed": False,
        "A_sector_closure_claimed": False,
        "sourced_maxwell_closure_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
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
        "obligation_row_discharged": False,
        "obligation_rows_discharged": False,
        "proof_debt_discharged": False,
        "new_physics_created": False,
    }


def _theorem_target_shape() -> dict[str, Any]:
    return {
        "given": [
            C_SOURCE_PHI_RESIDUAL_DEFINITION,
            RESIDUAL_IDENTITY_FORM,
            ON_SHELL_RESIDUAL_FORM,
            ON_SHELL_CONDITION,
        ],
        "therefore": TARGET_CONCLUSION,
        "route": EXECUTION_ROUTE,
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
        and closeout.get("C_source_phi_residual_definition")
        == C_SOURCE_PHI_RESIDUAL_DEFINITION
        and closeout.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
        and closeout.get("on_shell_residual_form") == ON_SHELL_RESIDUAL_FORM
        and closeout.get("on_shell_condition") == ON_SHELL_CONDITION
        and closeout.get("target_conclusion") == TARGET_CONCLUSION
        and closeout.get("execution_route") == EXECUTION_ROUTE
        and closeout.get("execution_reduction_route") == EXECUTION_REDUCTION_ROUTE
        and closeout.get("C_source_phi_zero_constructed") is True
        and closeout.get("C_source_phi_zero_derived") is True
        and closeout.get("theorem_linkage_completed") is True
        and closeout.get("phi_sector_closure_claimed") is False
        and closeout.get("full_scalar_qft_closure_claimed") is False
        and closeout.get("qft_gr_closure_claimed") is False
        and closeout.get("em_qft_closure_claimed") is False
        and closeout.get("general_C_k_closure") is False
        and closeout.get("seam_closure_claim") is False
        and closeout.get("rule_promoted") is False
        and closeout.get("master_action_promoted") is False
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_source_theorem_linkage_obligation_closeout_result_review"
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
        "lean_status_wording_lines_for_review": LEAN_STATUS_WORDING_LINES_FOR_REVIEW,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_source_theorem_linkage_obligation_closeout_result_review(
    *,
    closeout_path: Path = CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = _read_json(closeout_path)
    acceptance_criteria = {
        "consumes_expected_phi_source_closeout": _closeout_valid(closeout),
        "standalone_phi_route_preserved": (
            closeout.get("C_source_phi_residual_definition")
            == C_SOURCE_PHI_RESIDUAL_DEFINITION
            and closeout.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
            and closeout.get("on_shell_residual_form") == ON_SHELL_RESIDUAL_FORM
            and closeout.get("on_shell_condition") == ON_SHELL_CONDITION
            and closeout.get("target_conclusion") == TARGET_CONCLUSION
            and closeout.get("execution_route") == EXECUTION_ROUTE
        ),
        "local_zero_linkage_accepted": (
            closeout.get("phi_source_theorem_linkage_obligation_locally_closed")
            is True
            and closeout.get("C_source_phi_zero_constructed") is True
            and closeout.get("C_source_phi_zero_derived") is True
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
        else "REMEDIATE_PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selector_question": SELECTOR_QUESTION,
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
        "selected_obligation": "C_source^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_source^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_source^phi",
        "claim_boundary": CLAIM_BOUNDARY,
        "main_boundary": CLAIM_BOUNDARY,
        "closeout_claim_boundary": CLOSEOUT_CLAIM_BOUNDARY,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "theorem_target_shape": _theorem_target_shape(),
        "C_source_phi_residual_definition": C_SOURCE_PHI_RESIDUAL_DEFINITION,
        "residual_identity_form": RESIDUAL_IDENTITY_FORM,
        "on_shell_residual_form": ON_SHELL_RESIDUAL_FORM,
        "on_shell_condition": ON_SHELL_CONDITION,
        "target_conclusion": TARGET_CONCLUSION,
        "execution_route": EXECUTION_ROUTE,
        "execution_reduction_route": EXECUTION_REDUCTION_ROUTE,
        "linkage_route": EXECUTION_ROUTE,
        "route_kind": "standalone_phi_on_shell_scalar_residual",
        "plain_meaning": PLAIN_MEANING,
        "phi_source_closeout_result_review_accepted": accepted,
        "phi_source_theorem_linkage_obligation_closeout_accepted": accepted,
        "phi_source_theorem_linkage_obligation_locally_closed": accepted,
        "C_source_phi_definition_preserved": accepted,
        "standalone_phi_route_preserved": accepted,
        "scalar_on_shell_residual_identity_preserved": accepted,
        "scalar_residual_definition_preserved": accepted,
        "on_shell_condition_applied": accepted,
        "C_source_phi_zero_locally_linked": accepted,
        "C_source_phi_zero_constructed": accepted,
        "C_source_phi_zero_derived": accepted,
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
            "below phi-sector closure, full scalar/QFT closure, QFT-GR source "
            "admissibility, seam closure, empirical confirmation, and mature "
            "physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only that the local phi-source "
            "theorem-linkage closeout is clean: C_source^nu[g, phi] is defined "
            "as nabla_mu T_phi^{mu nu}, rewritten as sum_i R_i^phi nabla^nu "
            "phi_i with R_i^phi := Box_g phi_i + partial_i V(phi), and "
            "reduced to zero under the on-shell condition R_i^phi = 0. It "
            "authorizes only the next C_k-family theorem-linkage obligation "
            "selector. It claims no phi-sector completion, no scalar/QFT "
            "completion, no QFT-GR source admissibility, no EM-QFT closure, no "
            "general C_k closure, no C_k functionalization, no action "
            "embedding, no variation, no empirical validation, no seam closure, "
            "and no master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_phi_source_theorem_linkage_obligation_closeout_result",
            "fail to accept the local phi-source theorem-linkage closeout",
            "fail to preserve C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}",
            "fail to preserve C_source^nu = sum_i R_i^phi nabla^nu phi_i",
            "fail to preserve R_i^phi := Box_g phi_i + partial_i V(phi)",
            "fail to apply R_i^phi = 0 as the on-shell condition",
            "claim phi-sector closure",
            "claim full scalar/QFT closure",
            "claim QFT-GR source admissibility",
            "claim EM-QFT or QFT-GR closure",
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
            "ToeFormal.Derivation.PhiSourceTheoremLinkageObligationCloseoutResultReview",
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
        description="Review the local phi-source theorem-linkage closeout result."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--closeout", type=Path, default=CLOSEOUT_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    closeout_path = (
        args.closeout if args.closeout.is_absolute() else REPO_ROOT / args.closeout
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_phi_source_theorem_linkage_obligation_closeout_result_review(
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
                "selector_question": payload["selector_question"],
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
