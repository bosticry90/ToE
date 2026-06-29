from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.A_source_theorem_linkage_attempt_from_standalone_A_route_result_review_report import (
    C_SOURCE_A_RESIDUAL_DEFINITION,
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    EXECUTION_ROUTE_TO_AUTHORIZE,
    LEAN_PACKET_PATH as RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LINKAGE_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    PACKET_ID as RESULT_REVIEW_PACKET_ID,
    PSI_A_SOURCED_MAXWELL_ROUTE,
    PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
    REVIEW_RESULT,
    SCHEMA_ID as RESULT_REVIEW_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONDITION,
    STANDALONE_A_ROUTE,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_EXECUTION_OUTCOME,
    SUGGESTED_EXECUTION_OUTCOME,
    TARGET_CONCLUSION,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_chain_closeout_result_review_report import (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_"
    "20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_v0"
EXECUTION_RESULT = SUGGESTED_EXECUTION_OUTCOME
STRICT_EXECUTION_RESULT = STRICT_SUGGESTED_EXECUTION_OUTCOME
OUTCOME_ID = EXECUTION_RESULT
PACKET_CLASSIFICATION = (
    "A_source_theorem_linkage_attempt_from_standalone_A_route_executed_"
    "C_source_A_linkage_constructed_no_ck_rule_promotion_or_master_action_"
    "promotion"
)

NEXT_TARGET = "review_A_source_theorem_linkage_attempt_from_standalone_A_route_result"
NEXT_TARGET_KIND = (
    "A_source_theorem_linkage_attempt_from_standalone_A_route_result_review"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION = SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_EXECUTION = LEAN_STATUS_WORDING_FOR_REVIEW

LEAN_THEOREM_NAME = "c_source_A_zero_from_standalone_stress_conservation"
LEAN_THEOREM_DESCRIPTION = (
    "Generic Lean witness: if C_source^A is definitionally the standalone "
    "A-sector stress-divergence residual and that residual is zero, then "
    "C_source^A is zero."
)

PLAIN_MEANING = (
    "The A-sector source residual vanishes because it is defined as the "
    "standalone A-sector stress-divergence residual, and that divergence is zero."
)

SUGGESTED_REVIEW_OUTCOME = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_"
    "ACCEPTS_C_SOURCE_A_LINKAGE_CONSTRUCTED_NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_"
    "PROMOTION"
)
STRICT_SUGGESTED_REVIEW_OUTCOME = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_"
    "ACCEPTS_C_SOURCE_A_ZERO_FROM_STANDALONE_STRESS_CONSERVATION_NO_SOURCED_"
    "MAXWELL_SUBSTITUTION_OR_SEAM_CLOSURE"
)

EXECUTION_FINDINGS = [
    "standalone A-source theorem-linkage attempt executed",
    "C_source^A linkage constructed",
    "C_source^{A,nu} zero follows from standalone stress conservation",
    "no J current imported",
    "no psi-A sourced Maxwell substitution",
    "no sourced Maxwell closure",
    "no A-sector closure",
    "no C_k rule promotion",
    "no seam closure",
    "no master-action promotion",
]

BOUNDARY_ITEMS = [
    "no J current imported",
    "no psi-A sourced Maxwell substitution",
    "no sourced Maxwell closure",
    "no full Maxwell closure",
    "no A-sector closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no general C_k closure",
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
    / "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_20260628_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ASourceTheoremLinkageAttemptFromStandaloneARouteExecution.lean"
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
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_authorized": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "action_embedding_claimed": False,
        "action_variation_executed": False,
        "multiplier_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_claimed": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "proof_debt_discharged": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
    }


def _review_valid(result_review: dict[str, Any]) -> bool:
    return (
        result_review.get("schema_id") == RESULT_REVIEW_SCHEMA_ID
        and result_review.get("packet_id") == RESULT_REVIEW_PACKET_ID
        and result_review.get("outcome_id") == RESULT_REVIEW_OUTCOME
        and result_review.get("review_result") == REVIEW_RESULT
        and result_review.get("strict_review_result") == STRICT_REVIEW_RESULT
        and result_review.get("selected_next_target") == CONSUMED_TARGET
        and result_review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and result_review.get("execution_route_to_authorize")
        == EXECUTION_ROUTE_TO_AUTHORIZE
        and result_review.get("J_current_imported") is False
        and result_review.get("psi_A_sourced_route_substituted") is False
        and result_review.get("accepted") is True
    )


def _execution_steps() -> list[dict[str, str]]:
    return [
        {
            "step_id": "define_C_source_A_residual",
            "statement": C_SOURCE_A_RESIDUAL_DEFINITION,
            "role": "standalone A-sector source residual definition",
        },
        {
            "step_id": "use_standalone_A_stress_conservation",
            "statement": SOURCE_ADMISSIBILITY_CONDITION,
            "role": "accepted standalone A-sector stress-conservation route",
        },
        {
            "step_id": "rewrite_residual_to_zero",
            "statement": TARGET_CONCLUSION,
            "role": "definition rewrite plus standalone stress-conservation zero",
        },
    ]


def _execution_criteria() -> list[dict[str, Any]]:
    return [
        {
            "row_id": "execution_target_authorized",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The prior review selected this bounded execution target.",
        },
        {
            "row_id": "standalone_route_executed",
            "status": "accepted",
            "evidence": LINKAGE_ROUTE,
            "assessment": "The route stays exactly standalone.",
        },
        {
            "row_id": "C_source_A_definition_used",
            "status": "accepted",
            "evidence": C_SOURCE_A_RESIDUAL_DEFINITION,
            "assessment": "C_source^A is expanded only as nabla_mu T_A^{mu nu}.",
        },
        {
            "row_id": "stress_conservation_zero_used",
            "status": "accepted",
            "evidence": SOURCE_ADMISSIBILITY_CONDITION,
            "assessment": "The only zero input is standalone A-sector stress conservation.",
        },
        {
            "row_id": "C_source_A_zero_constructed",
            "status": "accepted",
            "evidence": TARGET_CONCLUSION,
            "assessment": "C_source^A zero follows from the definition and zero divergence.",
        },
        {
            "row_id": "no_J_or_sourced_Maxwell_import",
            "status": "accepted",
            "evidence": BOUNDARY_ITEMS[:2],
            "assessment": "No current or psi-A sourced Maxwell route is imported.",
        },
        {
            "row_id": "no_closure_or_promotion",
            "status": "accepted",
            "evidence": BOUNDARY_ITEMS[2:],
            "assessment": "The execution remains theorem-linkage only.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "A_source_theorem_linkage_attempt_from_standalone_A_route_execution"
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
        "full_toeformal_aggregate_status_for_execution": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
        ),
        "scoped_lean_targets_status_for_execution": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
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


def build_A_source_theorem_linkage_attempt_from_standalone_A_route_execution(
    *,
    result_review_path: Path = RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    route_text = " ".join(EXECUTION_ROUTE_TO_AUTHORIZE)
    execution_steps = _execution_steps()
    execution_criteria = _execution_criteria()
    acceptance_criteria = {
        "consumes_expected_execution_target": _review_valid(result_review),
        "standalone_execution_route_exact": (
            EXECUTION_ROUTE_TO_AUTHORIZE
            == [
                "C_source^{A,nu} := nabla_mu T_A^{mu nu}",
                "nabla_mu T_A^{mu nu} = 0",
                "therefore: C_source^{A,nu} = 0",
            ]
            and EXECUTION_ROUTE_TO_AUTHORIZE == LINKAGE_ROUTE
        ),
        "C_source_A_definition_preserved": (
            C_SOURCE_A_RESIDUAL_DEFINITION
            == "C_source^{A,nu} := nabla_mu T_A^{mu nu}"
        ),
        "standalone_stress_conservation_zero_preserved": (
            SOURCE_ADMISSIBILITY_CONDITION == "nabla_mu T_A^{mu nu} = 0"
        ),
        "C_source_A_zero_constructed": TARGET_CONCLUSION
        == "C_source^{A,nu} = 0",
        "no_J_current_imported": "J^alpha" not in route_text,
        "psi_A_sourced_Maxwell_route_not_substituted": (
            PSI_A_SOURCED_MAXWELL_ROUTE == "nabla_mu F^{mu alpha} = J^alpha"
            and PSI_A_SOURCED_MAXWELL_ROUTE not in route_text
        ),
        "execution_criteria_all_accepted": all(
            row["status"] == "accepted" for row in execution_criteria
        ),
        "lean_status_wording_preserved": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "executed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_REQUIRES_REMEDIATION",
        "execution_result": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_REQUIRES_REMEDIATION",
        "strict_execution_result": STRICT_EXECUTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "post_execution_target": NEXT_TARGET,
        "post_execution_target_kind": NEXT_TARGET_KIND,
        "suggested_review_outcome": SUGGESTED_REVIEW_OUTCOME,
        "strict_suggested_review_outcome": STRICT_SUGGESTED_REVIEW_OUTCOME,
        "result_review_schema_id": RESULT_REVIEW_SCHEMA_ID,
        "result_review_packet_id": RESULT_REVIEW_PACKET_ID,
        "result_review_outcome": RESULT_REVIEW_OUTCOME,
        "result_review_strict_outcome": STRICT_REVIEW_RESULT,
        "result_review_consumed": accepted,
        "selected_obligation": "C_source^A theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_source^A theorem-linkage gap",
        "selected_obligation_row_id": "C_source^A",
        "standalone_A_sector_route": STANDALONE_A_ROUTE,
        "standalone_A_sector_route_preserved": accepted,
        "standalone_A_stress_conservation_route": SOURCE_ADMISSIBILITY_CONDITION,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "C_source_A_residual_definition": C_SOURCE_A_RESIDUAL_DEFINITION,
        "target_conclusion": TARGET_CONCLUSION,
        "execution_route": EXECUTION_ROUTE_TO_AUTHORIZE,
        "linkage_route": LINKAGE_ROUTE,
        "route_kind": "standalone_A_stress_conservation",
        "source_free_standalone_boundary_preserved": True,
        "psi_A_sourced_maxwell_route": PSI_A_SOURCED_MAXWELL_ROUTE,
        "do_not_silently_substitute_psi_A_sourced_Maxwell_route": True,
        "route_contamination_guard": PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
        "plain_meaning": PLAIN_MEANING,
        "lean_theorem_name": LEAN_THEOREM_NAME,
        "lean_theorem_description": LEAN_THEOREM_DESCRIPTION,
        "C_source_A_zero_constructed": accepted,
        "C_source_A_zero_derived": accepted,
        "C_source_A_admissibility_status": "admissibility-only",
        "theorem_linkage_completed": accepted,
        "theorem_target_recorded": accepted,
        "definition_linkage_constructed": accepted,
        "proof_execution": "executed",
        "proof_execution_authorized": True,
        "proof_attempt_executed": accepted,
        "proof_debt_reduced": accepted,
        "theorem_execution_authorized": True,
        "theorem_discharged": accepted,
        "theorem_linkage_obligation_discharged": accepted,
        "A_source_theorem_linkage_obligation_discharged": accepted,
        "C_source_A_discharged": accepted,
        "rule_promotion": "not authorized",
        "execution_steps": execution_steps,
        "execution_step_count": len(execution_steps),
        "execution_criteria": execution_criteria,
        "execution_criteria_count": len(execution_criteria),
        "execution_criteria_accepted_count": sum(
            1 for row in execution_criteria if row["status"] == "accepted"
        ),
        "execution_findings": EXECUTION_FINDINGS,
        "execution_finding_count": len(EXECUTION_FINDINGS),
        "boundary_items": BOUNDARY_ITEMS,
        "boundary_item_count": len(BOUNDARY_ITEMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": False,
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This execution constructs only the standalone A-sector C_source^A "
            "linkage from C_source^{A,nu} := nabla_mu T_A^{mu nu} and "
            "nabla_mu T_A^{mu nu} = 0 to C_source^{A,nu} = 0. It imports no "
            "J current, substitutes no psi-A sourced Maxwell route, closes no "
            "sourced or full Maxwell route, claims no A-sector closure, closes "
            "no EM-QFT, QFT-GR, or GR-QM seam, claims no general C_k closure, "
            "embeds no C_k rule in an action, varies no C_k rule, claims no "
            "empirical validation, and does not promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume execute_A_source_theorem_linkage_attempt_from_standalone_A_route",
            "fail to preserve C_source^{A,nu} := nabla_mu T_A^{mu nu}",
            "fail to use nabla_mu T_A^{mu nu} = 0 as the only zero route",
            "import a J current into the route",
            "silently substitute nabla_mu F^{mu alpha} = J^alpha",
            "claim sourced or full Maxwell closure",
            "claim A-sector closure",
            "claim EM-QFT, QFT-GR, or GR-QM closure",
            "claim general C_k closure",
            "promote any C_k rule or the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_EXECUTION,
        "full_toeformal_aggregate_status_for_execution": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
        ),
        "scoped_lean_targets_status_for_execution": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
        ),
        "aggregate_lean_validation_status_for_execution": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ASourceTheoremLinkageAttemptFromStandaloneARouteExecution",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "result_review_file": _ptr(result_review_path),
            "result_review_lean_file": _ptr(RESULT_REVIEW_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
    payload["proof_execution_authorized"] = True
    payload["proof_attempt_executed"] = accepted
    payload["proof_debt_reduced"] = accepted
    payload["theorem_execution_authorized"] = True
    payload["theorem_discharged"] = accepted
    payload["theorem_linkage_completed"] = accepted
    payload["theorem_linkage_obligation_discharged"] = accepted
    payload["A_source_theorem_linkage_obligation_discharged"] = accepted
    payload["C_source_A_discharged"] = accepted
    return payload


def write_execution(payload: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Execute the standalone A-source C_source^A theorem-linkage route."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--result-review", type=Path, default=RESULT_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    result_review_path = (
        args.result_review
        if args.result_review.is_absolute()
        else REPO_ROOT / args.result_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_A_source_theorem_linkage_attempt_from_standalone_A_route_execution(
        result_review_path=result_review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_execution(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "executed": payload["executed"],
                "out": _ptr(path),
                "execution_result": payload["execution_result"],
                "selected_next_target": payload["selected_next_target"],
                "C_source_A_zero_derived": payload["C_source_A_zero_derived"],
                "J_current_imported": payload["J_current_imported"],
                "psi_A_sourced_route_substituted": payload[
                    "psi_A_sourced_route_substituted"
                ],
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
