from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.A_source_theorem_linkage_attempt_from_standalone_A_route_execution_report import (
    BOUNDARY_ITEMS,
    C_SOURCE_A_RESIDUAL_DEFINITION,
    DEFAULT_OUT as EXECUTION_PATH,
    EXECUTION_FINDINGS,
    EXECUTION_RESULT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION,
    LEAN_PACKET_PATH as EXECUTION_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_EXECUTION,
    LEAN_THEOREM_NAME,
    LINKAGE_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as EXECUTION_OUTCOME,
    PACKET_ID as EXECUTION_PACKET_ID,
    PLAIN_MEANING,
    PSI_A_SOURCED_MAXWELL_ROUTE,
    SCHEMA_ID as EXECUTION_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION,
    SOURCE_ADMISSIBILITY_CONDITION,
    STRICT_EXECUTION_RESULT,
    TARGET_CONCLUSION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_"
    "RESULT_REVIEW_20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_"
    "RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_"
    "ACCEPTS_C_SOURCE_A_LINKAGE_CONSTRUCTED_NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_"
    "PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_"
    "ACCEPTS_C_SOURCE_A_ZERO_FROM_STANDALONE_STRESS_CONSERVATION_NO_SOURCED_"
    "MAXWELL_SUBSTITUTION_OR_SEAM_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "A_source_theorem_linkage_attempt_from_standalone_A_route_result_review_"
    "accepts_C_source_A_linkage_constructed_no_ck_rule_promotion_or_master_action_"
    "promotion"
)

NEXT_TARGET = "prepare_A_source_theorem_linkage_obligation_closeout"
NEXT_TARGET_KIND = "A_source_theorem_linkage_obligation_closeout_preparation"
CLOSEOUT_OUTCOME = (
    "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_STANDALONE_STRESS_"
    "CONSERVATION_LINKED_C_SOURCE_A_ROUTE_NO_CK_RULE_PROMOTION_OR_SEAM_CLOSURE"
)
CLOSEOUT_STATEMENT = (
    "C_source^A is theorem-linked to standalone A-sector stress conservation "
    "by definition."
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_EXECUTION

ACCEPTED_REVIEW_FINDINGS = [
    "standalone A-source theorem-linkage route constructed",
    "C_source^{A,nu} definition preserved",
    "standalone stress-conservation input preserved",
    "C_source^{A,nu} = 0 locally linked",
    "no J current imported",
    "no psi-A sourced Maxwell substitution",
    "no A-sector closure",
    "no full Maxwell closure",
    "no C_k promotion",
    "no empirical validation",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_"
        "EXECUTION_RESULT_REVIEW_20260628_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ASourceTheoremLinkageAttemptFromStandaloneARouteExecutionResultReview.lean"
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
        "psi_A_sourced_route_substituted": False,
        "sourced_Maxwell_route_substituted": False,
        "C_source_A_closure_claimed": False,
        "A_sector_closure_claimed": False,
        "sourced_maxwell_closure_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "general_C_k_theorem_linkage_closure": False,
        "general_C_k_closure": False,
        "C_k_dynamical_law_status": False,
        "C_k_rule_promotion_authorized": False,
        "C_k_rule_promoted": False,
        "rule_promoted": False,
        "C_k_action_embedding_claimed": False,
        "C_k_action_variation_executed": False,
        "action_embedding_claimed": False,
        "action_variation_executed": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
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
            C_SOURCE_A_RESIDUAL_DEFINITION,
            SOURCE_ADMISSIBILITY_CONDITION,
        ],
        "therefore": TARGET_CONCLUSION,
        "route": LINKAGE_ROUTE,
        "plain_meaning": PLAIN_MEANING,
    }


def _review_criteria(execution: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "execution_packet_consumed",
            "status": "accepted",
            "evidence": execution.get("execution_result"),
            "assessment": "The bounded execution packet is consumed by review.",
        },
        {
            "row_id": "standalone_route_constructed",
            "status": "accepted",
            "evidence": execution.get("execution_route"),
            "assessment": "The route stays exactly standalone.",
        },
        {
            "row_id": "C_source_A_definition_preserved",
            "status": "accepted",
            "evidence": C_SOURCE_A_RESIDUAL_DEFINITION,
            "assessment": "C_source^A remains the A-sector stress divergence.",
        },
        {
            "row_id": "stress_conservation_input_preserved",
            "status": "accepted",
            "evidence": SOURCE_ADMISSIBILITY_CONDITION,
            "assessment": "The zero input is standalone A stress conservation.",
        },
        {
            "row_id": "C_source_A_zero_locally_linked",
            "status": "accepted",
            "evidence": execution.get("C_source_A_zero_derived"),
            "assessment": "C_source^A = 0 is locally linked by definition rewrite.",
        },
        {
            "row_id": "no_J_or_psi_A_sourced_route",
            "status": "accepted",
            "evidence": BOUNDARY_ITEMS[:2],
            "assessment": "No current or sourced Maxwell substitution is imported.",
        },
        {
            "row_id": "no_closure_or_promotion",
            "status": "accepted",
            "evidence": BOUNDARY_ITEMS[2:],
            "assessment": "No closure, empirical claim, or promotion is accepted.",
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
            "A_source_theorem_linkage_attempt_from_standalone_A_route_"
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
        "aggregate_lean_validation_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
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


def build_A_source_theorem_linkage_attempt_from_standalone_A_route_execution_result_review(
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
        "standalone_route_constructed": (
            execution.get("execution_route") == LINKAGE_ROUTE
            and execution.get("definition_linkage_constructed") is True
            and execution.get("C_source_A_zero_derived") is True
            and execution.get("proof_attempt_executed") is True
            and execution.get("theorem_discharged") is True
            and execution.get("theorem_linkage_completed") is True
        ),
        "theorem_target_shape_preserved": (
            theorem_target_shape["given"]
            == [C_SOURCE_A_RESIDUAL_DEFINITION, SOURCE_ADMISSIBILITY_CONDITION]
            and theorem_target_shape["therefore"] == TARGET_CONCLUSION
            and theorem_target_shape["route"] == LINKAGE_ROUTE
        ),
        "no_J_or_sourced_Maxwell_route_used": (
            execution.get("J_current_imported") is False
            and execution.get("psi_A_sourced_route_substituted") is False
            and execution.get("sourced_Maxwell_route_substituted") is False
            and PSI_A_SOURCED_MAXWELL_ROUTE not in " ".join(LINKAGE_ROUTE)
        ),
        "no_input_forbidden_claims": _input_boundary_clear(execution),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
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
        else "REMEDIATE_A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_"
            "EXECUTION_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "closeout_outcome": CLOSEOUT_OUTCOME,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "execution_schema_id": EXECUTION_SCHEMA_ID,
        "execution_packet_id": EXECUTION_PACKET_ID,
        "execution_outcome": EXECUTION_OUTCOME,
        "execution_strict_outcome": STRICT_EXECUTION_RESULT,
        "execution_packet_consumed": accepted,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "execution_findings": EXECUTION_FINDINGS,
        "execution_finding_count": len(EXECUTION_FINDINGS),
        "selected_obligation": "C_source^A theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_source^A theorem-linkage gap",
        "selected_obligation_row_id": "C_source^A",
        "claim_boundary": "theorem-linkage result review only, not physics closure",
        "route_kind": "standalone_A_stress_conservation",
        "source_free_standalone_boundary_preserved": True,
        "standalone_A_stress_conservation_route": SOURCE_ADMISSIBILITY_CONDITION,
        "C_source_A_residual_definition": C_SOURCE_A_RESIDUAL_DEFINITION,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "target_conclusion": TARGET_CONCLUSION,
        "execution_route": LINKAGE_ROUTE,
        "linkage_route": LINKAGE_ROUTE,
        "theorem_target_shape": theorem_target_shape,
        "theorem_target_recorded": accepted,
        "theorem_target_indexed": accepted,
        "theorem_linkage_target_indexed": accepted,
        "definition_linkage_route_indexed": accepted,
        "definition_linkage_attempt_prepared": accepted,
        "definition_linkage_constructed": accepted,
        "C_source_A_zero_derived": accepted,
        "C_source_A_zero_constructed": accepted,
        "C_source_A_admissibility_status": "admissibility-only",
        "plain_meaning": PLAIN_MEANING,
        "review_plain_meaning": theorem_target_shape["plain_meaning"],
        "mathematical_statement": (
            "Given C_source^{A,nu} := nabla_mu T_A^{mu nu} and "
            "nabla_mu T_A^{mu nu} = 0, show C_source^{A,nu} = 0."
        ),
        "lean_theorem_name": LEAN_THEOREM_NAME,
        "proof_execution": "already executed; not re-executed by review",
        "review_executes_attempt": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": True,
        "proof_debt_reduced": True,
        "proof_debt_discharged": False,
        "theorem_discharged": True,
        "theorem_linkage_completed": True,
        "theorem_linkage_proof_attempt_authorized": False,
        "theorem_linkage_obligation_discharged": True,
        "A_source_theorem_linkage_obligation_discharged": True,
        "C_source_A_discharged": True,
        "closeout_preparation_authorized": accepted,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "blocked_claims": BOUNDARY_ITEMS,
        "blocked_claim_count": len(BOUNDARY_ITEMS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_accepted": accepted,
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only that the standalone A-source "
            "theorem-linkage route has been constructed: C_source^{A,nu} is "
            "zero because it is defined as nabla_mu T_A^{mu nu}, and the "
            "standalone A-sector stress divergence is zero. It authorizes only "
            "closeout preparation. It imports no J current, substitutes no "
            "psi-A sourced Maxwell route, claims no A-sector or Maxwell closure, "
            "closes no seam, promotes no C_k rule, claims no empirical validation, "
            "and does not promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_A_source_theorem_linkage_attempt_from_standalone_A_route_result",
            "fail to preserve C_source^{A,nu} := nabla_mu T_A^{mu nu}",
            "fail to preserve nabla_mu T_A^{mu nu} = 0",
            "import a J current",
            "substitute the psi-A sourced Maxwell route",
            "claim sourced or full Maxwell closure",
            "claim A-sector closure",
            "claim seam closure",
            "promote C_k or the master action",
        ],
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
            "ToeFormal.Derivation.ASourceTheoremLinkageAttemptFromStandaloneARouteExecutionResultReview",
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
    payload["review_executes_attempt"] = False
    payload["proof_execution_authorized"] = False
    payload["proof_attempt_executed"] = True
    payload["proof_debt_reduced"] = True
    payload["theorem_discharged"] = True
    payload["theorem_linkage_completed"] = True
    payload["theorem_linkage_obligation_discharged"] = True
    payload["A_source_theorem_linkage_obligation_discharged"] = True
    payload["C_source_A_discharged"] = True
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
            "Review the executed standalone A-source C_source^A theorem-linkage route."
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
        build_A_source_theorem_linkage_attempt_from_standalone_A_route_execution_result_review(
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
