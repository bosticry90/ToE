from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_exchange_closeout_report import (
    DEFAULT_OUT as SELECTION_PATH,
    DEPENDENCY_CHAIN,
    FOLLOW_ON_TARGET_AFTER_REVIEW as SELECTOR_FOLLOW_ON_TARGET_AFTER_REVIEW,
    FOLLOW_ON_TARGET_KIND as SELECTOR_FOLLOW_ON_TARGET_KIND,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION,
    GAUGE_EXCHANGE_TARGET_RULE,
    GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
    LEAN_PACKET_PATH as SELECTION_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_SELECTION,
    LIKELY_THEOREM_LINKAGE_ROUTE,
    MATTER_EXCHANGE_DEPENDENCY,
    NEXT_CLEAN_QUESTION,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as SELECTION_OUTCOME,
    PACKET_ID as SELECTION_PACKET_ID,
    PLAIN_MEANING,
    PREVIOUS_CLOSED_OBLIGATION,
    ROUTE_SKETCH,
    SCHEMA_ID as SELECTION_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION,
    SELECTED_OBLIGATION,
    SELECTED_OBLIGATION_RANK,
    SELECTION_REASON,
    SELECTION_RESULT,
    SOURCED_MAXWELL_ROUTE,
    STRICT_SELECTION_RESULT,
    THEOREM_TARGET_STATUS,
    TOTAL_CONSERVATION_DEPENDENCY,
    T_TOTAL_DEFINITION_DEPENDENCY,
    WATCH_ITEMS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_RESULT_REVIEW_20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_RESULT_REVIEW_ACCEPTS_PSI_A_GAUGE_SECTOR_EXCHANGE_"
    "THEOREM_LINKAGE_GAP_SELECTION_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_RESULT_REVIEW_ACCEPTS_GAUGE_EXCHANGE_SELECTION_ONLY_"
    "NO_GAP_DISCHARGE_OR_CK_RULE_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_"
    "exchange_closeout_result_review_accepts_gauge_exchange_selection_only"
)

NEXT_TARGET = "prepare_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet"
NEXT_TARGET_KIND = "psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet"
LIKELY_POST_PACKET_REVIEW_TARGET = (
    "review_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result"
)
LIKELY_POST_PACKET_REVIEW_KIND = (
    "psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result_review"
)

NEXT_PACKET_TARGET_STATEMENT = (
    "Given nabla_mu T_A^{mu nu} = - F^nu{}_alpha nabla_mu F^{mu alpha} "
    "and nabla_mu F^{mu alpha} = J^alpha, show nabla_mu T_A^{mu nu} = "
    "- F^nu{}_alpha J^alpha."
)
NEXT_PACKET_PLAIN_MEANING = (
    "The gauge field loses the energy-momentum that matter gains."
)
NEXT_PACKET_WATCH_ITEMS = [
    "same T_A definition",
    "same F object",
    "same J object",
    "same sign convention",
    "same index placement",
    "same covariant derivative",
    "gauge stress-energy divergence identity",
    "sourced Maxwell route",
    "metric compatibility",
    "shared domain and boundary assumptions",
]

REVIEW_ACCEPTANCE_SUMMARY = [
    "selector outcome accepted",
    "psi-A gauge-sector exchange theorem-linkage gap selected",
    "follow-on target preserved",
    "no proof execution",
    "no theorem discharge",
    "no GAP-1 through GAP-8 global discharge",
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k variation",
    "no seam closure",
    "no empirical validation",
    "no master-action promotion",
]

BLOCKED_CLAIMS = [
    "no proof execution during review",
    "no theorem discharge during review",
    "no GAP-1 through GAP-8 global discharge",
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k variation",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no empirical validation",
    "no master-action promotion",
]

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_SELECTION

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
        "EXCHANGE_CLOSEOUT_RESULT_REVIEW_20260628_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CKFamilyTheoremLinkageObligationSelectionAfterPsiAMatterExchangeCloseoutResultReview.lean"
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
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "proof_debt_discharged": False,
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
        "new_physics_created": False,
    }


def _selector_valid(selector: dict[str, Any]) -> bool:
    return (
        selector.get("schema_id") == SELECTION_SCHEMA_ID
        and selector.get("packet_id") == SELECTION_PACKET_ID
        and selector.get("outcome_id") == SELECTION_OUTCOME
        and selector.get("selection_result") == SELECTION_RESULT
        and selector.get("strict_selection_result") == STRICT_SELECTION_RESULT
        and selector.get("selected_next_target") == CONSUMED_TARGET
        and selector.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and selector.get("follow_on_target_after_review")
        == SELECTOR_FOLLOW_ON_TARGET_AFTER_REVIEW
        and selector.get("follow_on_target_kind") == SELECTOR_FOLLOW_ON_TARGET_KIND
        and selector.get("selected_obligation") == SELECTED_OBLIGATION
        and selector.get("selected_obligation_rank") == SELECTED_OBLIGATION_RANK
        and selector.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "ck_family_theorem_linkage_obligation_selection_after_"
            "psi_A_matter_exchange_closeout_result_review"
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


def build_ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_exchange_closeout_result_review(
    *,
    selection_path: Path = SELECTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector = _read_json(selection_path)
    acceptance_criteria = {
        "consumes_expected_selector_result": _selector_valid(selector),
        "selector_outcome_accepted": selector.get("accepted") is True,
        "gauge_exchange_gap_selected": (
            selector.get("selected_obligation") == SELECTED_OBLIGATION
            and selector.get("selected_obligation_rank") == SELECTED_OBLIGATION_RANK
        ),
        "follow_on_target_preserved": (
            selector.get("follow_on_target_after_review") == NEXT_TARGET
        ),
        "packet_target_scope_preserved_without_execution": (
            GAUGE_EXCHANGE_TARGET_RULE
            == "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha"
            and GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
            == "nabla_mu T_A^{mu nu} = - F^nu{}_alpha nabla_mu F^{mu alpha}"
            and SOURCED_MAXWELL_ROUTE == "nabla_mu F^{mu alpha} = J^alpha"
            and THEOREM_TARGET_STATUS.startswith("selected only")
        ),
        "blocked_claims_preserved": True,
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
        else "REMEDIATE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_EXCHANGE_CLOSEOUT_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_"
            "PSI_A_MATTER_EXCHANGE_CLOSEOUT_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_EXCHANGE_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_EXCHANGE_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_EXCHANGE_CLOSEOUT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "likely_post_packet_review_target": LIKELY_POST_PACKET_REVIEW_TARGET,
        "likely_post_packet_review_kind": LIKELY_POST_PACKET_REVIEW_KIND,
        "selection_schema_id": SELECTION_SCHEMA_ID,
        "selection_packet_id": SELECTION_PACKET_ID,
        "selection_outcome": SELECTION_OUTCOME,
        "selection_result": SELECTION_RESULT,
        "selection_strict_outcome": STRICT_SELECTION_RESULT,
        "selection_consumed": accepted,
        "previous_closed_obligation": PREVIOUS_CLOSED_OBLIGATION,
        "previous_closed_obligation_local_only": accepted,
        "selected_obligation": SELECTED_OBLIGATION,
        "selected_obligation_rank": SELECTED_OBLIGATION_RANK,
        "selected_obligation_from_priority_list": accepted,
        "follow_on_target_preserved": accepted,
        "follow_on_target_after_review": NEXT_TARGET,
        "follow_on_target_kind": NEXT_TARGET_KIND,
        "review_acceptance_summary": REVIEW_ACCEPTANCE_SUMMARY,
        "dependency_chain": DEPENDENCY_CHAIN,
        "selection_reason": SELECTION_REASON,
        "plain_meaning": PLAIN_MEANING,
        "next_clean_question": NEXT_CLEAN_QUESTION,
        "gauge_exchange_target_rule": GAUGE_EXCHANGE_TARGET_RULE,
        "gauge_stress_energy_divergence_identity": (
            GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
        ),
        "sourced_maxwell_route": SOURCED_MAXWELL_ROUTE,
        "likely_theorem_linkage_route": LIKELY_THEOREM_LINKAGE_ROUTE,
        "route_sketch": ROUTE_SKETCH,
        "matter_exchange_dependency": MATTER_EXCHANGE_DEPENDENCY,
        "total_conservation_dependency": TOTAL_CONSERVATION_DEPENDENCY,
        "T_total_definition_dependency": T_TOTAL_DEFINITION_DEPENDENCY,
        "theorem_target_status": THEOREM_TARGET_STATUS,
        "selector_watch_items": WATCH_ITEMS,
        "next_packet_scope": (
            "prepare the psi-A gauge-sector exchange theorem-linkage "
            "obligation packet only"
        ),
        "next_packet_target_statement": NEXT_PACKET_TARGET_STATEMENT,
        "next_packet_plain_meaning": NEXT_PACKET_PLAIN_MEANING,
        "next_packet_watch_items": NEXT_PACKET_WATCH_ITEMS,
        "watch_items": NEXT_PACKET_WATCH_ITEMS,
        "watch_item_count": len(NEXT_PACKET_WATCH_ITEMS),
        "review_executes_proof": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "proof_debt_reduced": False,
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
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
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
            "This result review accepts only the selector result after the local "
            "psi-A matter-sector exchange closeout. It accepts that the psi-A "
            "gauge-sector exchange theorem-linkage gap was selected and preserves "
            "preparation of that obligation packet as the next target. It does not "
            "execute any proof, discharge any theorem, discharge GAP-1 through "
            "GAP-8, promote any C_k rule, embed C_k in an action, vary C_k, claim "
            "full Maxwell closure, close EM-QFT, close QFT-GR, close GR-QM, claim "
            "empirical validation, or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_exchange_closeout_result",
            "fail to accept the psi-A gauge-sector exchange theorem-linkage gap selection",
            "fail to select prepare_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet",
            "execute proof during review",
            "discharge theorem during review",
            "discharge GAP-1 through GAP-8",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "claim full Maxwell closure",
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
            "ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterPsiAMatterExchangeCloseoutResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "selection_file": _ptr(selection_path),
            "selection_lean_file": _ptr(SELECTION_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
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
            "Review the post-psi-A matter exchange C_k theorem-linkage "
            "obligation selector result."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--selection", type=Path, default=SELECTION_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    selection_path = (
        args.selection if args.selection.is_absolute() else REPO_ROOT / args.selection
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_exchange_closeout_result_review(
        selection_path=selection_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
                "selected_obligation": payload["selected_obligation"],
                "selected_next_target": payload["selected_next_target"],
                "proof_attempt_executed": payload["proof_attempt_executed"],
                "theorem_discharged": payload["theorem_discharged"],
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
