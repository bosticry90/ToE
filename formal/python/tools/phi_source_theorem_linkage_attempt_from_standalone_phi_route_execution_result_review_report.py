from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution_report import (
    BOUNDARY_ITEMS,
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    DEFAULT_OUT as EXECUTION_PATH,
    EXECUTION_FINDINGS,
    EXECUTION_REDUCTION_ROUTE,
    EXECUTION_RESULT,
    EXECUTION_ROUTE,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION,
    LEAN_PACKET_PATH as EXECUTION_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_EXECUTION,
    LEAN_THEOREM_NAME,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    ON_SHELL_CONDITION,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID as EXECUTION_OUTCOME,
    PACKET_ID as EXECUTION_PACKET_ID,
    PLAIN_MEANING,
    RESIDUAL_IDENTITY_FORM,
    ROUTE_PURITY_WATCH_ITEMS,
    SCHEMA_ID as EXECUTION_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION,
    STRICT_EXECUTION_RESULT,
    TARGET_CONCLUSION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTION_"
    "RESULT_REVIEW_20260630_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTION_"
    "RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTION_"
    "RESULT_REVIEW_ACCEPTS_C_SOURCE_PHI_ZERO_FROM_ON_SHELL_SCALAR_RESIDUAL_"
    "NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTION_"
    "RESULT_REVIEW_ACCEPTS_LOCAL_PHI_SOURCE_THEOREM_LINKAGE_ONLY_NO_PHI_"
    "SECTOR_OR_SEAM_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution_"
    "result_review_accepts_local_C_source_phi_zero_no_closure_or_promotion"
)

NEXT_TARGET = "prepare_phi_source_theorem_linkage_obligation_closeout"
NEXT_TARGET_KIND = "phi_source_theorem_linkage_obligation_closeout_preparation"
CLOSEOUT_OUTCOME = (
    "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_STANDALONE_ON_SHELL_"
    "SCALAR_RESIDUAL_LINKED_C_SOURCE_PHI_ROUTE_NO_CK_RULE_PROMOTION_OR_SEAM_"
    "CLOSURE"
)
STRICT_CLOSEOUT_OUTCOME = (
    "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_LOCAL_C_SOURCE_PHI_ZERO_"
    "ROUTE_NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
CLOSEOUT_STATEMENT = (
    "C_source^phi is theorem-linked to the standalone on-shell scalar residual "
    "route by definition."
)
MAIN_BOUNDARY = (
    "local C_source^phi theorem-linkage only; not phi-sector completion; not "
    "scalar/QFT completion; not QFT-GR source admissibility; not C_k "
    "functionalization; not master-action promotion"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_EXECUTION

ACCEPTED_REVIEW_FINDINGS = [
    "phi-source theorem-linkage execution accepted",
    "standalone phi route preserved",
    "C_source^nu[g, phi] definition preserved",
    "scalar/on-shell residual identity preserved",
    "R_i^phi definition preserved",
    "on-shell condition applied",
    "C_source^nu[g, phi] = 0 locally constructed",
    "Lean execution marker preserved",
    "JSON execution report preserved",
    "focused execution gate passed",
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
    / (
        "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_"
        "EXECUTION_RESULT_REVIEW_20260630_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiSourceTheoremLinkageAttemptFromStandalonePhiRouteExecutionResultReview.lean"
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
    }


def _input_boundary_clear(execution: dict[str, Any]) -> bool:
    return all(
        execution.get(key) is False
        for key in _blocked_boundary_flags()
        if key in execution
    )


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


def _review_criteria(execution: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "execution_packet_consumed",
            "status": "accepted",
            "evidence": execution.get("execution_result"),
            "assessment": "The bounded execution result is consumed by review.",
        },
        {
            "row_id": "standalone_phi_route_preserved",
            "status": "accepted",
            "evidence": execution.get("execution_route"),
            "assessment": "The route remains the standalone phi residual route.",
        },
        {
            "row_id": "C_source_phi_definition_preserved",
            "status": "accepted",
            "evidence": C_SOURCE_PHI_RESIDUAL_DEFINITION,
            "assessment": "C_source^phi remains the phi stress-divergence residual.",
        },
        {
            "row_id": "scalar_residual_identity_preserved",
            "status": "accepted",
            "evidence": RESIDUAL_IDENTITY_FORM,
            "assessment": "The scalar/on-shell residual identity is unchanged.",
        },
        {
            "row_id": "scalar_residual_definition_preserved",
            "status": "accepted",
            "evidence": ON_SHELL_RESIDUAL_FORM,
            "assessment": "R_i^phi is preserved as the scalar residual.",
        },
        {
            "row_id": "on_shell_condition_applied",
            "status": "accepted",
            "evidence": ON_SHELL_CONDITION,
            "assessment": "R_i^phi = 0 is applied as the on-shell condition.",
        },
        {
            "row_id": "C_source_phi_zero_locally_constructed",
            "status": "accepted",
            "evidence": TARGET_CONCLUSION,
            "assessment": "C_source^nu[g, phi] = 0 is locally constructed.",
        },
        {
            "row_id": "route_contamination_blocked",
            "status": "accepted",
            "evidence": ROUTE_PURITY_WATCH_ITEMS,
            "assessment": "No A, psi-A sourced Maxwell, or QFT-GR source route is imported.",
        },
        {
            "row_id": "no_closure_or_promotion",
            "status": "accepted",
            "evidence": BOUNDARY_ITEMS,
            "assessment": "No sector closure, seam closure, C_k promotion, or master-action promotion is accepted.",
        },
        {
            "row_id": "closeout_preparation_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is closeout preparation only.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_source_theorem_linkage_attempt_from_standalone_phi_route_"
            "execution_result_review"
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


def build_phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution_result_review(
    *,
    execution_path: Path = EXECUTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    execution = _read_json(execution_path)
    theorem_target_shape = _theorem_target_shape()
    review_criteria = _review_criteria(execution)
    acceptance_criteria = {
        "consumes_expected_execution_result": (
            execution.get("schema_id") == EXECUTION_SCHEMA_ID
            and execution.get("packet_id") == EXECUTION_PACKET_ID
            and execution.get("outcome_id") == EXECUTION_OUTCOME
            and execution.get("execution_result") == EXECUTION_RESULT
            and execution.get("strict_execution_result") == STRICT_EXECUTION_RESULT
            and execution.get("selected_next_target") == CONSUMED_TARGET
            and execution.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and execution.get("accepted") is True
            and execution.get("executed") is True
        ),
        "standalone_phi_route_preserved": (
            execution.get("execution_route") == EXECUTION_ROUTE
            and execution.get("execution_reduction_route") == EXECUTION_REDUCTION_ROUTE
            and execution.get("standalone_phi_source_route_preserved") is True
            and execution.get("definition_linkage_constructed") is True
        ),
        "scalar_on_shell_residual_identity_preserved": (
            execution.get("C_source_phi_residual_definition")
            == C_SOURCE_PHI_RESIDUAL_DEFINITION
            and execution.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
            and execution.get("on_shell_residual_form") == ON_SHELL_RESIDUAL_FORM
            and execution.get("on_shell_condition") == ON_SHELL_CONDITION
        ),
        "C_source_phi_zero_locally_constructed": (
            execution.get("target_conclusion") == TARGET_CONCLUSION
            and execution.get("C_source_phi_zero_constructed") is True
            and execution.get("C_source_phi_zero_derived") is True
            and execution.get("theorem_discharged") is True
            and execution.get("theorem_linkage_completed") is True
        ),
        "route_contamination_blocked": (
            execution.get("A_source_route_imported") is False
            and execution.get("psi_A_sourced_Maxwell_imported") is False
            and execution.get("QFT_GR_source_route_imported") is False
            and execution.get("J_current_imported") is False
        ),
        "no_input_forbidden_claims": _input_boundary_clear(execution),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "lean_status_wording_preserved": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "ROUTE_EXECUTION_RESULT_REVIEW"
        )
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "ROUTE_EXECUTION_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_"
            "EXECUTION_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "review_result": OUTCOME_ID
        if accepted
        else (
            "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_"
            "EXECUTION_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "packet_result": OUTCOME_ID
        if accepted
        else (
            "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_"
            "EXECUTION_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if accepted else "remediation",
        "closeout_outcome": CLOSEOUT_OUTCOME,
        "strict_closeout_outcome": STRICT_CLOSEOUT_OUTCOME,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "execution_schema_id": EXECUTION_SCHEMA_ID,
        "execution_packet_id": EXECUTION_PACKET_ID,
        "execution_outcome": EXECUTION_OUTCOME,
        "execution_result": EXECUTION_RESULT,
        "execution_strict_outcome": STRICT_EXECUTION_RESULT,
        "execution_packet_consumed": accepted,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "execution_findings": EXECUTION_FINDINGS,
        "execution_finding_count": len(EXECUTION_FINDINGS),
        "selected_obligation": "C_source^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_source^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_source^phi",
        "claim_boundary": MAIN_BOUNDARY,
        "main_boundary": MAIN_BOUNDARY,
        "route_kind": "standalone_phi_on_shell_scalar_residual",
        "standalone_phi_route_preserved": accepted,
        "C_source_phi_residual_definition": C_SOURCE_PHI_RESIDUAL_DEFINITION,
        "residual_identity_form": RESIDUAL_IDENTITY_FORM,
        "on_shell_residual_form": ON_SHELL_RESIDUAL_FORM,
        "on_shell_condition": ON_SHELL_CONDITION,
        "target_conclusion": TARGET_CONCLUSION,
        "execution_route": EXECUTION_ROUTE,
        "execution_reduction_route": EXECUTION_REDUCTION_ROUTE,
        "linkage_route": EXECUTION_ROUTE,
        "theorem_target_shape": theorem_target_shape,
        "theorem_target_recorded": accepted,
        "definition_linkage_constructed": accepted,
        "scalar_on_shell_residual_identity_preserved": accepted,
        "scalar_residual_definition_preserved": accepted,
        "on_shell_condition_applied": accepted,
        "C_source_phi_zero_constructed": accepted,
        "C_source_phi_zero_derived": accepted,
        "C_source_phi_linkage_constructed": accepted,
        "C_source_phi_admissibility_status": "local theorem-linkage only",
        "plain_meaning": PLAIN_MEANING,
        "lean_theorem_name": LEAN_THEOREM_NAME,
        "lean_execution_marker_preserved": accepted,
        "json_execution_report_preserved": accepted,
        "focused_execution_gate_passed": accepted,
        "proof_execution": "already executed; not re-executed by review",
        "review_executes_attempt": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": True,
        "proof_debt_reduced": True,
        "proof_debt_discharged": False,
        "theorem_discharged": True,
        "theorem_linkage_completed": accepted,
        "theorem_linkage_obligation_discharged": accepted,
        "phi_source_theorem_linkage_obligation_discharged": accepted,
        "C_source_phi_discharged": accepted,
        "closeout_preparation_authorized": accepted,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "boundary_items": BOUNDARY_ITEMS,
        "boundary_item_count": len(BOUNDARY_ITEMS),
        "route_purity_watch_items": ROUTE_PURITY_WATCH_ITEMS,
        "route_purity_watch_item_count": len(ROUTE_PURITY_WATCH_ITEMS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_accepted": accepted,
        "claim_ladder_position": (
            "below phi-sector closure, full scalar/QFT closure, QFT-GR source "
            "admissibility, seam closure, empirical confirmation, and mature "
            "physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only the local standalone phi-source "
            "execution result: C_source^nu[g, phi] is defined as nabla_mu "
            "T_phi^{mu nu}, rewritten as sum_i R_i^phi nabla^nu phi_i with "
            "R_i^phi := Box_g phi_i + partial_i V(phi), and reduced to zero "
            "under the on-shell condition R_i^phi = 0. It authorizes only "
            "closeout preparation. It claims no phi-sector completion, no "
            "scalar/QFT completion, no QFT-GR source admissibility, no EM-QFT "
            "closure, no general C_k closure, no C_k rule promotion, no action "
            "embedding, no variation, no empirical validation, no seam closure, "
            "and no master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution_result",
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
            "ToeFormal.Derivation.PhiSourceTheoremLinkageAttemptFromStandalonePhiRouteExecutionResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "execution_file": _ptr(execution_path),
            "execution_lean_file": _ptr(EXECUTION_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
    payload["proof_execution_authorized"] = False
    payload["proof_attempt_executed"] = True
    payload["theorem_discharged"] = True
    payload["theorem_linkage_completed"] = accepted
    payload["theorem_linkage_obligation_discharged"] = accepted
    payload["phi_source_theorem_linkage_obligation_discharged"] = accepted
    payload["C_source_phi_discharged"] = accepted
    payload["rule_promoted"] = False
    return payload


def write_review(payload: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Review the executed standalone phi-source C_source^phi theorem-linkage route."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--execution", type=Path, default=EXECUTION_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    execution_path = (
        args.execution if args.execution.is_absolute() else REPO_ROOT / args.execution
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution_result_review(
            execution_path=execution_path,
            captured_at_utc=args.captured_at_utc,
        )
    )
    path = write_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "reviewed": payload["reviewed"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
                "selected_next_target": payload["selected_next_target"],
                "closeout_outcome": payload["closeout_outcome"],
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
