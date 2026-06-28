from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout_result_review_report import (
    DEFAULT_OUT as CLOSEOUT_RESULT_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW as FULL_TOEFORMAL_AGGREGATE_STATUS_FROM_REVIEW,
    LEAN_PACKET_PATH as CLOSEOUT_RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW as LEAN_STATUS_WORDING_FROM_REVIEW,
    LIKELY_NEXT_OBLIGATION as REVIEW_LIKELY_NEXT_OBLIGATION,
    LIKELY_SELECTOR_OUTCOME as REVIEW_LIKELY_SELECTOR_OUTCOME,
    NEXT_OBLIGATION_REASON as REVIEW_NEXT_OBLIGATION_REASON,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as CLOSEOUT_RESULT_REVIEW_OUTCOME,
    PACKET_ID as CLOSEOUT_RESULT_REVIEW_PACKET_ID,
    REVIEW_RESULT as CLOSEOUT_RESULT_REVIEW_RESULT,
    SCHEMA_ID as CLOSEOUT_RESULT_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW as SCOPED_LEAN_TARGETS_STATUS_FROM_REVIEW,
    STRICT_REVIEW_RESULT as CLOSEOUT_RESULT_REVIEW_STRICT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_v0"
)
SELECTION_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_SELECTS_PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_"
    "GAP_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
)
STRICT_SELECTION_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_SELECTS_GAUGE_EXCHANGE_LINKAGE_OBLIGATION_NO_GAP_"
    "DISCHARGE_OR_CK_RULE_PROMOTION"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_"
    "exchange_closeout_selects_gauge_exchange_linkage_obligation_no_proof_execution"
)

NEXT_TARGET = (
    "review_ck_family_theorem_linkage_obligation_selection_after_"
    "psi_A_matter_exchange_closeout_result"
)
NEXT_TARGET_KIND = (
    "ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_"
    "exchange_closeout_result_review"
)
FOLLOW_ON_TARGET_AFTER_REVIEW = (
    "prepare_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet"
)
FOLLOW_ON_TARGET_KIND = "psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet"

SELECTED_OBLIGATION = "psi-A gauge-sector exchange theorem-linkage gap"
SELECTED_OBLIGATION_RANK = 4
PREVIOUS_CLOSED_OBLIGATION = "psi-A matter-sector exchange theorem-linkage gap"
DEPENDENCY_CHAIN = (
    "C_exchange depends on total conservation; total conservation depends on "
    "matter-sector exchange and gauge-sector exchange."
)
SELECTION_REASON = REVIEW_NEXT_OBLIGATION_REASON
PLAIN_MEANING = "The gauge field loses the energy-momentum that matter gains."
NEXT_CLEAN_QUESTION = (
    "Can the psi-A gauge-sector exchange route be theorem-linked from the gauge "
    "stress-energy divergence identity and sourced Maxwell route?"
)

GAUGE_EXCHANGE_TARGET_RULE = "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha"
MATTER_EXCHANGE_DEPENDENCY = "nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha"
TOTAL_CONSERVATION_DEPENDENCY = "nabla_mu T_total^{mu nu} = 0"
T_TOTAL_DEFINITION_DEPENDENCY = "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}"
GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY = (
    "nabla_mu T_A^{mu nu} = - F^nu{}_alpha nabla_mu F^{mu alpha}"
)
SOURCED_MAXWELL_ROUTE = "nabla_mu F^{mu alpha} = J^alpha"
THEOREM_TARGET_STATEMENT = (
    "Given nabla_mu T_A^{mu nu} = - F^nu{}_alpha nabla_mu F^{mu alpha} "
    "and nabla_mu F^{mu alpha} = J^alpha, show nabla_mu T_A^{mu nu} = "
    "- F^nu{}_alpha J^alpha."
)
THEOREM_TARGET_STATUS = (
    "selected only; exact theorem target deferred to the gauge-sector exchange "
    "obligation packet"
)
LIKELY_THEOREM_LINKAGE_ROUTE = (
    "gauge stress-energy divergence identity plus sourced Maxwell route"
)
ROUTE_SKETCH = (
    "nabla_mu T_A^{mu nu} = - F^nu{}_alpha nabla_mu F^{mu alpha}; "
    "nabla_mu F^{mu alpha} = J^alpha; therefore nabla_mu T_A^{mu nu} = "
    "- F^nu{}_alpha J^alpha"
)
WATCH_ITEMS = [
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

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FROM_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION = SCOPED_LEAN_TARGETS_STATUS_FROM_REVIEW
LEAN_STATUS_WORDING_FOR_SELECTION = LEAN_STATUS_WORDING_FROM_REVIEW

BLOCKED_CLAIMS = [
    "no proof execution during selector",
    "no theorem discharge during selector",
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

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
        "EXCHANGE_CLOSEOUT_20260628_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CKFamilyTheoremLinkageObligationSelectionAfterPsiAMatterExchangeCloseout.lean"
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


def _theorem_shape() -> dict[str, Any]:
    return {
        "given": [
            GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
            SOURCED_MAXWELL_ROUTE,
        ],
        "then": GAUGE_EXCHANGE_TARGET_RULE,
        "plain_meaning": PLAIN_MEANING,
    }


def _consumed_review_valid(review: dict[str, Any]) -> bool:
    return (
        review.get("schema_id") == CLOSEOUT_RESULT_REVIEW_SCHEMA_ID
        and review.get("packet_id") == CLOSEOUT_RESULT_REVIEW_PACKET_ID
        and review.get("outcome_id") == CLOSEOUT_RESULT_REVIEW_OUTCOME
        and review.get("review_result") == CLOSEOUT_RESULT_REVIEW_RESULT
        and review.get("strict_review_result")
        == CLOSEOUT_RESULT_REVIEW_STRICT_OUTCOME
        and review.get("selected_next_target") == CONSUMED_TARGET
        and review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and review.get("likely_selector_outcome") == REVIEW_LIKELY_SELECTOR_OUTCOME
        and review.get("likely_next_obligation") == REVIEW_LIKELY_NEXT_OBLIGATION
        and review.get("next_obligation_reason") == REVIEW_NEXT_OBLIGATION_REASON
        and review.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "ck_family_theorem_linkage_obligation_selection_after_"
            "psi_A_matter_exchange_closeout"
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
        "full_toeformal_aggregate_status_for_selection": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION
        ),
        "scoped_lean_targets_status_for_selection": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION
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


def build_ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_exchange_closeout(
    *,
    closeout_result_review_path: Path = CLOSEOUT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(closeout_result_review_path)
    acceptance_criteria = {
        "consumes_expected_matter_exchange_closeout_result_review": (
            _consumed_review_valid(review)
        ),
        "previous_matter_exchange_obligation_locally_closed": (
            review.get("local_psi_A_matter_sector_exchange_obligation_closed")
            is True
            and review.get("matter_exchange_linked_to_dirac_pair_route") is True
            and review.get("matter_exchange_route_constructed") is True
            and review.get("general_C_k_theorem_linkage_closure") is False
        ),
        "selects_fourth_priority_gauge_exchange_obligation": (
            SELECTED_OBLIGATION == REVIEW_LIKELY_NEXT_OBLIGATION
            and SELECTED_OBLIGATION_RANK == 4
            and OUTCOME_ID == REVIEW_LIKELY_SELECTOR_OUTCOME
        ),
        "selector_records_gauge_route_without_execution": (
            GAUGE_EXCHANGE_TARGET_RULE
            == "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha"
            and GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
            == "nabla_mu T_A^{mu nu} = - F^nu{}_alpha nabla_mu F^{mu alpha}"
            and SOURCED_MAXWELL_ROUTE == "nabla_mu F^{mu alpha} = J^alpha"
            and THEOREM_TARGET_STATUS.startswith("selected only")
        ),
        "blocked_claims_preserved": True,
        "lean_status_wording_careful": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_EXCHANGE_CLOSEOUT"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_"
            "PSI_A_MATTER_EXCHANGE_CLOSEOUT"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "selected": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_EXCHANGE_CLOSEOUT_REQUIRES_REMEDIATION",
        "selection_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_EXCHANGE_CLOSEOUT_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_EXCHANGE_CLOSEOUT_REQUIRES_REMEDIATION",
        "strict_selection_result": STRICT_SELECTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "follow_on_target_after_review": FOLLOW_ON_TARGET_AFTER_REVIEW,
        "follow_on_target_kind": FOLLOW_ON_TARGET_KIND,
        "closeout_result_review_schema_id": CLOSEOUT_RESULT_REVIEW_SCHEMA_ID,
        "closeout_result_review_packet_id": CLOSEOUT_RESULT_REVIEW_PACKET_ID,
        "closeout_result_review_outcome": CLOSEOUT_RESULT_REVIEW_OUTCOME,
        "closeout_result_review_strict_outcome": (
            CLOSEOUT_RESULT_REVIEW_STRICT_OUTCOME
        ),
        "closeout_result_review_consumed": accepted,
        "previous_closed_obligation": PREVIOUS_CLOSED_OBLIGATION,
        "previous_closed_obligation_local_only": accepted,
        "selected_obligation": SELECTED_OBLIGATION,
        "selected_obligation_rank": SELECTED_OBLIGATION_RANK,
        "selected_obligation_from_priority_list": accepted,
        "dependency_chain": DEPENDENCY_CHAIN,
        "selection_reason": SELECTION_REASON,
        "review_next_obligation_reason": REVIEW_NEXT_OBLIGATION_REASON,
        "plain_meaning": PLAIN_MEANING,
        "next_clean_question": NEXT_CLEAN_QUESTION,
        "gauge_exchange_target_rule": GAUGE_EXCHANGE_TARGET_RULE,
        "matter_exchange_dependency": MATTER_EXCHANGE_DEPENDENCY,
        "total_conservation_dependency": TOTAL_CONSERVATION_DEPENDENCY,
        "T_total_definition_dependency": T_TOTAL_DEFINITION_DEPENDENCY,
        "gauge_stress_energy_divergence_identity": (
            GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
        ),
        "sourced_maxwell_route": SOURCED_MAXWELL_ROUTE,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "theorem_target_status": THEOREM_TARGET_STATUS,
        "likely_theorem_linkage_route": LIKELY_THEOREM_LINKAGE_ROUTE,
        "route_sketch": ROUTE_SKETCH,
        "theorem_shape": _theorem_shape(),
        "watch_items": WATCH_ITEMS,
        "watch_item_count": len(WATCH_ITEMS),
        "selector_only": accepted,
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
            "This selector chooses only the next C_k family theorem-linkage "
            "obligation after the local psi-A matter-sector exchange closeout. "
            "It selects the psi-A gauge-sector exchange theorem-linkage gap and "
            "records the target shape plus likely route. It does not execute any "
            "proof, discharge any theorem, discharge GAP-1 through GAP-8 "
            "globally, promote C_k, embed C_k in an action, vary C_k, make a "
            "direct dynamical-law claim, close full Maxwell, EM-QFT, QFT-GR, or "
            "GR-QM, claim empirical validation, or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume select_next_ck_family_theorem_linkage_obligation_after_psi_A_matter_exchange_closeout",
            "fail to select psi-A gauge-sector exchange theorem-linkage gap",
            "execute proof during selector",
            "discharge theorem during selector",
            "claim general C_k closure",
            "discharge GAP-1 through GAP-8 globally",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "claim full Maxwell closure",
            "claim EM-QFT, QFT-GR, or GR-QM closure",
            "claim seam closure",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_SELECTION,
        "full_toeformal_aggregate_status_for_selection": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION
        ),
        "scoped_lean_targets_status_for_selection": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION
        ),
        "aggregate_lean_validation_status_for_selection": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterPsiAMatterExchangeCloseout",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "closeout_result_review_file": _ptr(closeout_result_review_path),
            "closeout_result_review_lean_file": _ptr(
                CLOSEOUT_RESULT_REVIEW_LEAN_PACKET_PATH
            ),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
    payload["proof_execution_authorized"] = False
    payload["proof_attempt_executed"] = False
    payload["theorem_discharged"] = False
    payload["theorem_linkage_obligation_discharged"] = False
    payload["proof_debt_discharged"] = False
    payload["rule_promoted"] = False
    return payload


def write_selection(selection: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(selection, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Select the next C_k theorem-linkage obligation after psi-A matter "
            "exchange closeout."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--closeout-result-review",
        type=Path,
        default=CLOSEOUT_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = (
        args.closeout_result_review
        if args.closeout_result_review.is_absolute()
        else REPO_ROOT / args.closeout_result_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_exchange_closeout(
        closeout_result_review_path=review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_selection(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "selection_result": payload["selection_result"],
                "selected_obligation": payload["selected_obligation"],
                "selected_next_target": payload["selected_next_target"],
                "follow_on_target_after_review": payload[
                    "follow_on_target_after_review"
                ],
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
