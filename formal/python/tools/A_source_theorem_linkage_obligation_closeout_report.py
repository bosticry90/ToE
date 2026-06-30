from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.A_source_theorem_linkage_attempt_from_standalone_A_route_execution_report import (
    BOUNDARY_ITEMS,
    C_SOURCE_A_RESIDUAL_DEFINITION,
    LINKAGE_ROUTE,
    PLAIN_MEANING,
    SOURCE_ADMISSIBILITY_CONDITION,
    TARGET_CONCLUSION,
)
from formal.python.tools.A_source_theorem_linkage_attempt_from_standalone_A_route_execution_result_review_report import (
    CLOSEOUT_OUTCOME as REVIEW_CLOSEOUT_OUTCOME,
    CLOSEOUT_STATEMENT as REVIEW_CLOSEOUT_STATEMENT,
    DEFAULT_OUT as EXECUTION_RESULT_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH as EXECUTION_RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as EXECUTION_RESULT_REVIEW_OUTCOME,
    PACKET_ID as EXECUTION_RESULT_REVIEW_PACKET_ID,
    REVIEW_RESULT as EXECUTION_RESULT_REVIEW_RESULT,
    SCHEMA_ID as EXECUTION_RESULT_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT as EXECUTION_RESULT_REVIEW_STRICT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_20260628_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_v0"
CLOSEOUT_RESULT = REVIEW_CLOSEOUT_OUTCOME
STRICT_CLOSEOUT_RESULT = (
    "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_LOCAL_C_SOURCE_A_ZERO_ROUTE_"
    "NO_SOURCED_MAXWELL_SUBSTITUTION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "A_source_theorem_linkage_obligation_closed_as_standalone_stress_"
    "conservation_linked_C_source_A_route_no_ck_rule_promotion_or_seam_closure"
)

NEXT_TARGET = "review_A_source_theorem_linkage_obligation_closeout_result"
NEXT_TARGET_KIND = "A_source_theorem_linkage_obligation_closeout_result_review"
SUGGESTED_REVIEW_OUTCOME = (
    "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_"
    "STANDALONE_STRESS_CONSERVATION_LINKED_C_SOURCE_A_ROUTE_NO_CK_RULE_PROMOTION_"
    "OR_SEAM_CLOSURE"
)
CLOSEOUT_STATEMENT = REVIEW_CLOSEOUT_STATEMENT
CLAIM_BOUNDARY = (
    "local A-source theorem-linkage closeout only, not A-sector closure or "
    "physics closure"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT = SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_CLOSEOUT = LEAN_STATUS_WORDING_FOR_REVIEW

CLOSEOUT_CLAIMS = [
    "A-source theorem-linkage obligation locally closed",
    "C_source^{A,nu} definition preserved",
    "standalone A-sector stress-conservation input preserved",
    "C_source^{A,nu} = 0 constructed and reviewed",
    "no J current imported",
    "no psi-A sourced Maxwell substitution",
    "no sourced/full Maxwell closure",
    "no A-sector closure",
    "no seam closure",
    "no C_k promotion",
    "no empirical validation",
    "no master-action promotion",
]

NONCLAIMS = [
    "no J import",
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
    / "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_20260628_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ASourceTheoremLinkageObligationCloseout.lean"
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
        and review.get("closeout_statement") == REVIEW_CLOSEOUT_STATEMENT
        and review.get("accepted") is True
        and review.get("reviewed") is True
        and review.get("C_source_A_residual_definition")
        == C_SOURCE_A_RESIDUAL_DEFINITION
        and review.get("source_admissibility_condition")
        == SOURCE_ADMISSIBILITY_CONDITION
        and review.get("target_conclusion") == TARGET_CONCLUSION
        and review.get("execution_route") == LINKAGE_ROUTE
        and review.get("C_source_A_zero_derived") is True
        and review.get("theorem_linkage_completed") is True
        and review.get("J_current_imported") is False
        and review.get("psi_A_sourced_route_substituted") is False
        and review.get("sourced_maxwell_closure_claimed") is False
        and review.get("full_maxwell_closure_claimed") is False
        and review.get("A_sector_closure_claimed") is False
        and review.get("seam_closure_claim") is False
        and review.get("rule_promoted") is False
        and review.get("master_action_promoted") is False
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "A_source_theorem_linkage_obligation_closeout",
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


def build_A_source_theorem_linkage_obligation_closeout(
    *,
    execution_result_review_path: Path = EXECUTION_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(execution_result_review_path)
    acceptance_criteria = {
        "consumed_expected_execution_result_review": _consumed_review_valid(review),
        "standalone_A_source_route_preserved": (
            review.get("C_source_A_residual_definition")
            == C_SOURCE_A_RESIDUAL_DEFINITION
            and review.get("source_admissibility_condition")
            == SOURCE_ADMISSIBILITY_CONDITION
            and review.get("target_conclusion") == TARGET_CONCLUSION
            and review.get("execution_route") == LINKAGE_ROUTE
        ),
        "constructed_and_reviewed": (
            review.get("C_source_A_zero_constructed") is True
            and review.get("C_source_A_zero_derived") is True
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
        else "REMEDIATE_A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "closed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_REQUIRES_REMEDIATION",
        "closeout_result": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_REQUIRES_REMEDIATION",
        "strict_closeout_result": STRICT_CLOSEOUT_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "suggested_review_outcome": SUGGESTED_REVIEW_OUTCOME,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "execution_result_review_schema_id": EXECUTION_RESULT_REVIEW_SCHEMA_ID,
        "execution_result_review_packet_id": EXECUTION_RESULT_REVIEW_PACKET_ID,
        "execution_result_review_outcome": EXECUTION_RESULT_REVIEW_OUTCOME,
        "execution_result_review_strict_outcome": (
            EXECUTION_RESULT_REVIEW_STRICT_OUTCOME
        ),
        "execution_result_review_consumed": accepted,
        "selected_obligation": "C_source^A theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_source^A theorem-linkage gap",
        "selected_obligation_row_id": "C_source^A",
        "claim_boundary": CLAIM_BOUNDARY,
        "closeout_claims": CLOSEOUT_CLAIMS,
        "closeout_claim_count": len(CLOSEOUT_CLAIMS),
        "nonclaims": NONCLAIMS,
        "nonclaim_count": len(NONCLAIMS),
        "theorem_target_shape": _theorem_target_shape(),
        "standalone_A_stress_conservation_route": SOURCE_ADMISSIBILITY_CONDITION,
        "C_source_A_residual_definition": C_SOURCE_A_RESIDUAL_DEFINITION,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "target_conclusion": TARGET_CONCLUSION,
        "execution_route": LINKAGE_ROUTE,
        "linkage_route": LINKAGE_ROUTE,
        "route_kind": "standalone_A_stress_conservation",
        "plain_meaning": PLAIN_MEANING,
        "local_A_source_theorem_linkage_obligation_closed": accepted,
        "A_source_theorem_linkage_obligation_locally_closed": accepted,
        "A_source_theorem_linkage_obligation_discharged": accepted,
        "C_source_A_definition_preserved": accepted,
        "standalone_A_stress_conservation_input_preserved": accepted,
        "C_source_A_zero_constructed": accepted,
        "C_source_A_zero_derived": accepted,
        "C_source_A_discharged": accepted,
        "definition_linkage_constructed": accepted,
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
        "blocked_claims": BOUNDARY_ITEMS,
        "blocked_claim_count": len(BOUNDARY_ITEMS),
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
            "This closeout records only that the local A-source theorem-linkage "
            "obligation is closed by the standalone route: C_source^{A,nu} is "
            "defined as nabla_mu T_A^{mu nu}, the standalone A-sector stress "
            "divergence is zero, and therefore C_source^{A,nu} = 0. It imports "
            "no J current, substitutes no psi-A sourced Maxwell route, claims "
            "no sourced or full Maxwell closure, claims no A-sector closure, "
            "closes no seam, closes no EM-QFT, QFT-GR, or GR-QM bridge, "
            "promotes no general C_k rule, embeds no action, varies no action, "
            "claims no empirical validation, and does not promote the master "
            "action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_A_source_theorem_linkage_obligation_closeout",
            "fail to close the local A-source theorem-linkage obligation",
            "fail to preserve C_source^{A,nu} := nabla_mu T_A^{mu nu}",
            "fail to preserve nabla_mu T_A^{mu nu} = 0",
            "fail to preserve C_source^{A,nu} = 0",
            "import a J current",
            "substitute the psi-A sourced Maxwell route",
            "claim sourced or full Maxwell closure",
            "claim A-sector closure",
            "claim seam closure",
            "promote any C_k rule",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_CLOSEOUT,
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
            "ToeFormal.Derivation.ASourceTheoremLinkageObligationCloseout",
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
    payload["A_source_theorem_linkage_obligation_discharged"] = accepted
    payload["C_source_A_discharged"] = accepted
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
        description="Close out the local standalone A-source theorem-linkage obligation."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--review", type=Path, default=EXECUTION_RESULT_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = args.review if args.review.is_absolute() else REPO_ROOT / args.review
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_A_source_theorem_linkage_obligation_closeout(
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
                "A_source_theorem_linkage_obligation_locally_closed": payload[
                    "A_source_theorem_linkage_obligation_locally_closed"
                ],
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
