from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_interaction_exchange_theorem_linkage_chain_closeout_result_review_report import (
    DEFAULT_OUT as CLOSEOUT_RESULT_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW as FULL_TOEFORMAL_AGGREGATE_STATUS_FROM_REVIEW,
    LEAN_PACKET_PATH as CLOSEOUT_RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW as LEAN_STATUS_WORDING_FROM_REVIEW,
    LIKELY_NEXT_OBLIGATION as REVIEW_LIKELY_NEXT_OBLIGATION,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as CLOSEOUT_RESULT_REVIEW_OUTCOME,
    PACKET_ID as CLOSEOUT_RESULT_REVIEW_PACKET_ID,
    REVIEW_RESULT as CLOSEOUT_RESULT_REVIEW_RESULT,
    SCHEMA_ID as CLOSEOUT_RESULT_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW as SCOPED_LEAN_TARGETS_STATUS_FROM_REVIEW,
    STRICT_REVIEW_RESULT as CLOSEOUT_RESULT_REVIEW_STRICT_OUTCOME,
    STRICT_SUGGESTED_SELECTOR_OUTCOME as REVIEW_STRICT_SUGGESTED_SELECTOR_OUTCOME,
    SUGGESTED_SELECTOR_OUTCOME as REVIEW_SUGGESTED_SELECTOR_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_"
    "CHAIN_CLOSEOUT_20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_"
    "CHAIN_CLOSEOUT_v0"
)
SELECTION_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_CHAIN_"
    "CLOSEOUT_SELECTS_C_SOURCE_A_THEOREM_LINKAGE_GAP_NO_PROOF_EXECUTION_OR_"
    "MASTER_ACTION_PROMOTION"
)
STRICT_SELECTION_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_CHAIN_"
    "CLOSEOUT_SELECTS_A_SOURCE_LINKAGE_OBLIGATION_NO_GAP_DISCHARGE_OR_CK_RULE_"
    "PROMOTION"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_"
    "chain_closeout_selects_A_source_linkage_obligation_no_gap_discharge"
)

NEXT_TARGET = (
    "review_ck_family_theorem_linkage_obligation_selection_after_"
    "psi_A_exchange_chain_closeout_result"
)
NEXT_TARGET_KIND = (
    "ck_family_theorem_linkage_obligation_selection_after_"
    "psi_A_exchange_chain_closeout_result_review"
)
FOLLOW_ON_TARGET_AFTER_REVIEW = "prepare_A_source_theorem_linkage_obligation_packet"
FOLLOW_ON_TARGET_KIND = "A_source_theorem_linkage_obligation_packet"

SELECTED_OBLIGATION = "C_source^A theorem-linkage obligation"
SELECTED_THEOREM_LINKAGE_GAP = "C_source^A theorem-linkage gap"
SELECTED_OBLIGATION_ROW_ID = "C_source^A"
PREVIOUS_CLOSED_CHAIN = "local psi-A interaction exchange support chain"
DEPENDENCY_CHAIN = (
    "C_exchange = 0 depends on total conservation; total conservation depends "
    "on matter-sector exchange and gauge-sector exchange; matter-sector "
    "exchange depends on the Dirac-pair route; gauge-sector exchange depends "
    "on the stress-divergence identity plus sourced Maxwell route."
)
SELECTION_REASON = (
    "The local psi-A exchange support chain has been closed. The next "
    "unresolved indexed C_k-family theorem-linkage obligation is C_source^A."
)
PLAIN_MEANING = (
    "The selector now moves from the locally closed psi-A exchange chain to the "
    "A-source linkage obligation."
)
NEXT_CLEAN_QUESTION = (
    "Can the C_source^A theorem-linkage obligation be packeted with its exact "
    "source equation, assumptions, identity route, sign conventions, and "
    "boundary conditions?"
)

ROUTE_BOUNDARY = (
    "selector only; exact C_source^A theorem target, source equation, "
    "assumptions, identity route, sign conventions, and boundary conditions are "
    "deferred to the A-source theorem-linkage obligation packet"
)
AVOIDED_CLAIMS = [
    "do not execute the C_source^A proof route",
    "do not claim A-sector closure",
    "do not claim full Maxwell closure",
    "do not claim sourced Maxwell closure",
    "do not claim EM-QFT closure",
    "do not claim QFT-GR closure",
    "do not upgrade C_source^A to a dynamical law",
    "do not promote the master action",
]
BLOCKED_CLAIMS = [
    "no proof execution",
    "no theorem discharge",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no seam closure",
    "no empirical validation",
    "no master-action promotion",
]

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FROM_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION = SCOPED_LEAN_TARGETS_STATUS_FROM_REVIEW
LEAN_STATUS_WORDING_FOR_SELECTION = LEAN_STATUS_WORDING_FROM_REVIEW

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_"
        "CHAIN_CLOSEOUT_20260628_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CKFamilyTheoremLinkageObligationSelectionAfterPsiAExchangeChainCloseout.lean"
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
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "general_C_k_theorem_linkage_closure": False,
        "general_C_k_closure": False,
        "C_k_dynamical_law_status": False,
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
        "rule_promoted": False,
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
        and review.get("likely_next_obligation") == REVIEW_LIKELY_NEXT_OBLIGATION
        and review.get("suggested_selector_outcome") == REVIEW_SUGGESTED_SELECTOR_OUTCOME
        and review.get("strict_suggested_selector_outcome")
        == REVIEW_STRICT_SUGGESTED_SELECTOR_OUTCOME
        and review.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "ck_family_theorem_linkage_obligation_selection_after_"
            "psi_A_exchange_chain_closeout"
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


def build_ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_chain_closeout(
    *,
    closeout_result_review_path: Path = CLOSEOUT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(closeout_result_review_path)
    acceptance_criteria = {
        "consumes_expected_exchange_chain_closeout_result_review": (
            _consumed_review_valid(review)
        ),
        "psi_A_exchange_chain_closeout_review_accepted": (
            review.get("local_psi_A_interaction_exchange_support_chain_closed")
            is True
            and review.get("C_exchange_linkage_included") is True
            and review.get("total_conservation_linkage_included") is True
            and review.get("matter_sector_exchange_linkage_included") is True
            and review.get("gauge_sector_exchange_linkage_included") is True
        ),
        "selects_C_source_A_as_next_unresolved_indexed_obligation": (
            SELECTED_OBLIGATION == REVIEW_LIKELY_NEXT_OBLIGATION
            and OUTCOME_ID == REVIEW_SUGGESTED_SELECTOR_OUTCOME
            and STRICT_SELECTION_RESULT == REVIEW_STRICT_SUGGESTED_SELECTOR_OUTCOME
        ),
        "selector_only_without_proof_execution": (
            ROUTE_BOUNDARY.startswith("selector only")
            and FOLLOW_ON_TARGET_AFTER_REVIEW
            == "prepare_A_source_theorem_linkage_obligation_packet"
        ),
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
        else "REMEDIATE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_CHAIN_CLOSEOUT"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_"
            "PSI_A_EXCHANGE_CHAIN_CLOSEOUT"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "selected": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_CHAIN_CLOSEOUT_REQUIRES_REMEDIATION",
        "selection_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_CHAIN_CLOSEOUT_REQUIRES_REMEDIATION",
        "selector_outcome": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_CHAIN_CLOSEOUT_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_CHAIN_CLOSEOUT_REQUIRES_REMEDIATION",
        "strict_selection_result": STRICT_SELECTION_RESULT,
        "strict_selector_outcome": STRICT_SELECTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if accepted else "remediation",
        "follow_on_target_after_review": FOLLOW_ON_TARGET_AFTER_REVIEW,
        "follow_on_target_kind": FOLLOW_ON_TARGET_KIND,
        "closeout_result_review_schema_id": CLOSEOUT_RESULT_REVIEW_SCHEMA_ID,
        "closeout_result_review_packet_id": CLOSEOUT_RESULT_REVIEW_PACKET_ID,
        "closeout_result_review_outcome": CLOSEOUT_RESULT_REVIEW_OUTCOME,
        "closeout_result_review_strict_outcome": (
            CLOSEOUT_RESULT_REVIEW_STRICT_OUTCOME
        ),
        "closeout_result_review_consumed": accepted,
        "psi_A_exchange_chain_closeout_review_accepted": accepted,
        "previous_closed_chain": PREVIOUS_CLOSED_CHAIN,
        "selected_obligation": SELECTED_OBLIGATION,
        "selected_theorem_linkage_gap": SELECTED_THEOREM_LINKAGE_GAP,
        "selected_obligation_row_id": SELECTED_OBLIGATION_ROW_ID,
        "C_source_A_selected_as_next_unresolved_indexed_obligation": accepted,
        "next_theorem_linkage_obligation_selected": accepted,
        "dependency_chain": DEPENDENCY_CHAIN,
        "selection_reason": SELECTION_REASON,
        "plain_meaning": PLAIN_MEANING,
        "next_clean_question": NEXT_CLEAN_QUESTION,
        "route_boundary": ROUTE_BOUNDARY,
        "selector_only": accepted,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "gap_discharged": False,
        "rule_promoted": False,
        "avoided_claims": AVOIDED_CLAIMS,
        "blocked_claims": BLOCKED_CLAIMS,
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
            "obligation after the local psi-A exchange chain closeout. It "
            "selects C_source^A as the next unresolved indexed obligation. It "
            "does not execute the C_source^A proof route, discharge a theorem, "
            "claim A-sector closure, close full Maxwell or sourced Maxwell, "
            "close EM-QFT, QFT-GR, or GR-QM, upgrade C_source^A to a dynamical "
            "law, or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume select_next_ck_family_theorem_linkage_obligation_after_psi_A_exchange_chain_closeout",
            "fail to select C_source^A theorem-linkage obligation",
            "execute proof during selector",
            "discharge theorem during selector",
            "claim A-sector closure",
            "claim full Maxwell closure",
            "claim sourced Maxwell closure",
            "claim EM-QFT, QFT-GR, or GR-QM closure",
            "promote C_source^A to a dynamical law",
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
            "ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterPsiAExchangeChainCloseout",
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
            "Select the next C_k theorem-linkage obligation after local psi-A "
            "exchange chain closeout."
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
    payload = build_ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_chain_closeout(
        closeout_result_review_path=review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_selection(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "selector_outcome": payload["selector_outcome"],
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
