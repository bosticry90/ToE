from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.A_source_theorem_linkage_attempt_from_standalone_A_route_report import (
    BOUNDARY_ITEMS as ATTEMPT_BOUNDARY_ITEMS,
    C_SOURCE_A_RESIDUAL_DEFINITION,
    DEFAULT_OUT as ATTEMPT_PATH,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    LINKAGE_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as ATTEMPT_OUTCOME,
    PACKET_ID as ATTEMPT_PACKET_ID,
    PREPARED_LINKAGE_TARGET,
    PSI_A_SOURCED_MAXWELL_ROUTE,
    PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
    SCHEMA_ID as ATTEMPT_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONDITION,
    STANDALONE_A_ROUTE,
    STRICT_ATTEMPT_PREPARATION_RESULT,
    TARGET_CONCLUSION,
    WATCH_ITEMS,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_chain_closeout_result_review_report import (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_"
    "20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_"
    "ACCEPTS_C_SOURCE_A_LINKAGE_ROUTE_PREPARATION_NO_THEOREM_DISCHARGE_OR_CK_"
    "RULE_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_"
    "ACCEPTS_STANDALONE_A_STRESS_CONSERVATION_ROUTE_PREPARED_NO_SOURCED_MAXWELL_"
    "SUBSTITUTION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "A_source_theorem_linkage_attempt_from_standalone_A_route_result_review_"
    "accepts_prepared_stress_conservation_route_no_theorem_discharge"
)

NEXT_TARGET = "execute_A_source_theorem_linkage_attempt_from_standalone_A_route"
NEXT_TARGET_KIND = "A_source_theorem_linkage_attempt_from_standalone_A_route_execution"
SUGGESTED_EXECUTION_OUTCOME = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTED_C_SOURCE_A_"
    "LINKAGE_CONSTRUCTED_NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_PROMOTION"
)
STRICT_SUGGESTED_EXECUTION_OUTCOME = (
    "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTED_C_SOURCE_A_"
    "ZERO_FROM_STANDALONE_STRESS_CONSERVATION_NO_SOURCED_MAXWELL_SUBSTITUTION_"
    "OR_SEAM_CLOSURE"
)

ACCEPTED_REVIEW_FINDINGS = [
    "standalone A-source linkage attempt prepared",
    "C_source^{A,nu} definition preserved",
    "standalone stress-conservation route preserved",
    "target C_source^{A,nu} = 0 prepared",
    "no J current imported",
    "no psi-A sourced Maxwell substitution",
    "no theorem discharge",
    "no C_k promotion",
    "no A-sector closure",
    "no full Maxwell closure",
    "no empirical validation",
    "no master-action promotion",
]

BLOCKED_CLAIMS = [
    "no theorem discharge during review",
    "no C_source^A closure during review",
    "no A-sector closure",
    "no sourced Maxwell closure",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no general C_k closure",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]

EXECUTION_ROUTE_TO_AUTHORIZE = [
    C_SOURCE_A_RESIDUAL_DEFINITION,
    SOURCE_ADMISSIBILITY_CONDITION,
    "therefore: C_source^{A,nu} = 0",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_20260628_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ASourceTheoremLinkageAttemptFromStandaloneARouteResultReview.lean"
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
        "review_executes_theorem": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_execution_authorized": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "C_source_A_closure_claimed": False,
        "C_source_A_discharged": False,
        "A_source_theorem_linkage_obligation_discharged": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "J_current_imported": False,
        "psi_A_sourced_route_substituted": False,
        "sourced_Maxwell_route_substituted": False,
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
        "A_sector_closure_claimed": False,
        "sourced_maxwell_closure_claimed": False,
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
    }


def _attempt_valid(attempt: dict[str, Any]) -> bool:
    return (
        attempt.get("schema_id") == ATTEMPT_SCHEMA_ID
        and attempt.get("packet_id") == ATTEMPT_PACKET_ID
        and attempt.get("outcome_id") == ATTEMPT_OUTCOME
        and attempt.get("attempt_preparation_result") == ATTEMPT_OUTCOME
        and attempt.get("strict_attempt_preparation_result")
        == STRICT_ATTEMPT_PREPARATION_RESULT
        and attempt.get("selected_next_target") == CONSUMED_TARGET
        and attempt.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and attempt.get("C_source_A_residual_definition")
        == C_SOURCE_A_RESIDUAL_DEFINITION
        and attempt.get("source_admissibility_condition")
        == SOURCE_ADMISSIBILITY_CONDITION
        and attempt.get("target_conclusion") == TARGET_CONCLUSION
        and attempt.get("linkage_route") == LINKAGE_ROUTE
        and attempt.get("J_current_imported") is False
        and attempt.get("psi_A_sourced_route_substituted") is False
        and attempt.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "A_source_theorem_linkage_attempt_from_standalone_A_route_result_review"
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


def build_A_source_theorem_linkage_attempt_from_standalone_A_route_result_review(
    *,
    attempt_path: Path = ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    route_text = " ".join(EXECUTION_ROUTE_TO_AUTHORIZE)
    acceptance_criteria = {
        "consumes_expected_attempt_preparation": _attempt_valid(attempt),
        "C_source_A_definition_preserved": (
            C_SOURCE_A_RESIDUAL_DEFINITION
            == "C_source^{A,nu} := nabla_mu T_A^{mu nu}"
        ),
        "standalone_stress_conservation_route_preserved": (
            SOURCE_ADMISSIBILITY_CONDITION == "nabla_mu T_A^{mu nu} = 0"
        ),
        "target_C_source_A_zero_prepared": (
            TARGET_CONCLUSION == "C_source^{A,nu} = 0"
            and EXECUTION_ROUTE_TO_AUTHORIZE == LINKAGE_ROUTE
        ),
        "no_J_current_imported": "J^alpha" not in route_text,
        "psi_A_sourced_Maxwell_route_not_substituted": (
            PSI_A_SOURCED_MAXWELL_ROUTE == "nabla_mu F^{mu alpha} = J^alpha"
            and PSI_A_SOURCED_MAXWELL_ROUTE not in route_text
        ),
        "review_only_no_theorem_discharge": True,
        "blocked_claims_preserved": ATTEMPT_BOUNDARY_ITEMS[2:5]
        == [
            "no A-sector closure",
            "no sourced Maxwell closure",
            "no full Maxwell closure",
        ],
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
        else "REMEDIATE_A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "suggested_execution_outcome": SUGGESTED_EXECUTION_OUTCOME,
        "strict_suggested_execution_outcome": STRICT_SUGGESTED_EXECUTION_OUTCOME,
        "attempt_schema_id": ATTEMPT_SCHEMA_ID,
        "attempt_packet_id": ATTEMPT_PACKET_ID,
        "attempt_preparation_result": ATTEMPT_OUTCOME,
        "attempt_strict_preparation_result": STRICT_ATTEMPT_PREPARATION_RESULT,
        "attempt_preparation_consumed": accepted,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "selected_obligation": "C_source^A theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_source^A theorem-linkage gap",
        "selected_obligation_row_id": "C_source^A",
        "standalone_A_sector_route": STANDALONE_A_ROUTE,
        "standalone_A_sector_route_preserved": accepted,
        "standalone_A_stress_conservation_route": SOURCE_ADMISSIBILITY_CONDITION,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "C_source_A_residual_definition": C_SOURCE_A_RESIDUAL_DEFINITION,
        "target_conclusion": TARGET_CONCLUSION,
        "prepared_linkage_target": PREPARED_LINKAGE_TARGET,
        "execution_route_to_authorize": EXECUTION_ROUTE_TO_AUTHORIZE,
        "linkage_route": LINKAGE_ROUTE,
        "route_kind": "standalone_A_stress_conservation",
        "source_free_standalone_boundary_preserved": True,
        "J_current_imported": False,
        "psi_A_sourced_maxwell_route": PSI_A_SOURCED_MAXWELL_ROUTE,
        "psi_A_sourced_route_substituted": False,
        "sourced_Maxwell_route_substituted": False,
        "do_not_silently_substitute_psi_A_sourced_Maxwell_route": True,
        "route_contamination_guard": PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
        "watch_items": WATCH_ITEMS,
        "watch_item_count": len(WATCH_ITEMS),
        "boundary_items": BLOCKED_CLAIMS,
        "boundary_item_count": len(BLOCKED_CLAIMS),
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
            "This result review accepts only that the standalone A-sector "
            "C_source^A linkage attempt was prepared from C_source^{A,nu} := "
            "nabla_mu T_A^{mu nu} and nabla_mu T_A^{mu nu} = 0 toward the "
            "target C_source^{A,nu} = 0. It authorizes only the bounded "
            "execution target. It does not import J, does not substitute the "
            "later psi-A sourced Maxwell route nabla_mu F^{mu alpha} = J^alpha, "
            "does not discharge C_source^A, does not promote any C_k rule, "
            "does not claim A-sector closure, does not close sourced or full "
            "Maxwell, does not close EM-QFT, QFT-GR, or GR-QM, does not embed "
            "or vary C_k in an action, does not claim empirical validation, "
            "and does not promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_A_source_theorem_linkage_attempt_from_standalone_A_route_result",
            "fail to accept the prepared standalone stress-conservation route",
            "lose C_source^{A,nu} := nabla_mu T_A^{mu nu}",
            "lose target C_source^{A,nu} = 0",
            "import a J current into the route",
            "silently substitute nabla_mu F^{mu alpha} = J^alpha",
            "execute or discharge the theorem during review",
            "claim A-sector closure",
            "claim sourced or full Maxwell closure",
            "claim EM-QFT, QFT-GR, or GR-QM closure",
            "promote any C_k rule or the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
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
            "ToeFormal.Derivation.ASourceTheoremLinkageAttemptFromStandaloneARouteResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "attempt_file": _ptr(attempt_path),
            "attempt_lean_file": _ptr(ATTEMPT_LEAN_PACKET_PATH),
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
            "Review the standalone A-source C_source^A theorem-linkage attempt "
            "preparation without executing the theorem."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--attempt", type=Path, default=ATTEMPT_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    attempt_path = (
        args.attempt if args.attempt.is_absolute() else REPO_ROOT / args.attempt
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_A_source_theorem_linkage_attempt_from_standalone_A_route_result_review(
        attempt_path=attempt_path,
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
                "C_source_A_residual_definition": payload[
                    "C_source_A_residual_definition"
                ],
                "source_admissibility_condition": payload[
                    "source_admissibility_condition"
                ],
                "target_conclusion": payload["target_conclusion"],
                "J_current_imported": payload["J_current_imported"],
                "psi_A_sourced_route_substituted": payload[
                    "psi_A_sourced_route_substituted"
                ],
                "theorem_discharged": payload["theorem_discharged"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
