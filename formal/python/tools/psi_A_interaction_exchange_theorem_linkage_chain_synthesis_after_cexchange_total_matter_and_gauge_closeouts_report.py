from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_result_review_report import (
    DEFAULT_OUT as GAUGE_CLOSEOUT_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH as GAUGE_CLOSEOUT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LOCAL_DEPENDENCY_CHAIN,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as GAUGE_CLOSEOUT_REVIEW_OUTCOME,
    REVIEW_RESULT as GAUGE_CLOSEOUT_REVIEW_RESULT,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT as GAUGE_CLOSEOUT_REVIEW_STRICT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_AFTER_"
    "CEXCHANGE_TOTAL_MATTER_AND_GAUGE_CLOSEOUTS_20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_AFTER_"
    "CEXCHANGE_TOTAL_MATTER_AND_GAUGE_CLOSEOUTS_v0"
)
PACKET_RESULT = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_AFTER_"
    "CEXCHANGE_TOTAL_MATTER_AND_GAUGE_CLOSEOUTS_PREPARED_LOCAL_DEPENDENCY_"
    "CHAIN_SYNTHESIZED_NO_CK_RULE_PROMOTION_OR_SEAM_CLOSURE"
)
STRICT_PACKET_RESULT = (
    "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_PREPARED_"
    "CEXCHANGE_TOTAL_AND_EXCHANGE_LINKAGES_SYNTHESIZED_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = PACKET_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_"
    "cexchange_total_matter_and_gauge_closeouts_prepared_local_dependency_"
    "chain_synthesized_no_ck_rule_promotion_or_seam_closure"
)

NEXT_TARGET = (
    "review_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_"
    "cexchange_total_matter_and_gauge_closeouts_result"
)
NEXT_TARGET_KIND = (
    "psi_A_interaction_exchange_theorem_linkage_chain_synthesis_result_review"
)
LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW = (
    "prepare_psi_A_interaction_exchange_theorem_linkage_chain_closeout"
)

C_EXCHANGE_LINKAGE_DEFINITION = (
    "C_exchange^{Apsi,nu} := nabla_mu T_total^{mu nu}"
)
C_EXCHANGE_LINKAGE_INPUT = "nabla_mu T_total^{mu nu} = 0"
C_EXCHANGE_LINKAGE_CONCLUSION = "C_exchange^{Apsi,nu} = 0"
TOTAL_CONSERVATION_GAUGE_INPUT = (
    "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha"
)
TOTAL_CONSERVATION_MATTER_INPUT = (
    "nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha"
)
TOTAL_CONSERVATION_CONCLUSION = "nabla_mu T_total^{mu nu} = 0"
MATTER_SECTOR_INPUT_ROUTE = "Dirac pair + T_psi policy + J definition"
MATTER_SECTOR_CONCLUSION = (
    "nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha"
)
GAUGE_SECTOR_INPUT_ROUTE = (
    "gauge stress-divergence identity + sourced Maxwell route"
)
GAUGE_STRESS_DIVERGENCE_IDENTITY = (
    "nabla_mu T_A^{mu nu} = - F^nu{}_alpha nabla_mu F^{mu alpha}"
)
SOURCED_MAXWELL_ROUTE = "nabla_mu F^{mu alpha} = J^alpha"
GAUGE_SECTOR_CONCLUSION = (
    "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha"
)
PLAIN_MEANING = (
    "The interaction balance rule now has a locally linked support chain. "
    "Matter gains what gauge loses. The total system balances. C_exchange "
    "records that balance."
)
CLAIM_BOUNDARY = (
    "local psi-A interaction exchange theorem-linkage chain synthesis only; "
    "no new proof execution, theorem discharge, C_k rule promotion, seam "
    "closure, empirical validation, or master-action promotion"
)

SYNTHESIS_CLAIMS = [
    "local psi-A interaction exchange theorem-linkage chain synthesized",
    "C_exchange, total conservation, matter exchange, and gauge exchange linked in dependency order",
    "all linkages remain bounded and local",
    "no new proof execution in this synthesis packet",
]
NONCLAIMS = [
    "no general C_k closure",
    "no GAP-1 through GAP-8 global discharge",
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k variation",
    "no multiplier route",
    "no penalty route",
    "no direct dynamical-law claim",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no empirical validation",
    "no master-action promotion",
]

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SYNTHESIS = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_SYNTHESIS = (
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
)
LEAN_STATUS_WORDING_FOR_SYNTHESIS = LEAN_STATUS_WORDING_FOR_REVIEW

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS_AFTER_"
        "CEXCHANGE_TOTAL_MATTER_AND_GAUGE_CLOSEOUTS_20260628_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiAInteractionExchangeTheoremLinkageChainSynthesisAfterCexchangeTotalMatterAndGaugeCloseouts.lean"
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


def _linkage_chain() -> list[dict[str, Any]]:
    return [
        {
            "linkage_id": "C_exchange_linkage",
            "depends_on": "total conservation",
            "given": [
                C_EXCHANGE_LINKAGE_DEFINITION,
                C_EXCHANGE_LINKAGE_INPUT,
            ],
            "therefore": C_EXCHANGE_LINKAGE_CONCLUSION,
            "status": "locally_linked_from_total_conservation",
        },
        {
            "linkage_id": "total_conservation_linkage",
            "depends_on": "matter-sector exchange + gauge-sector exchange",
            "given": [
                TOTAL_CONSERVATION_GAUGE_INPUT,
                TOTAL_CONSERVATION_MATTER_INPUT,
            ],
            "therefore": TOTAL_CONSERVATION_CONCLUSION,
            "status": "locally_linked_from_equal_and_opposite_exchange_halves",
        },
        {
            "linkage_id": "matter_sector_exchange_linkage",
            "depends_on": "Dirac-pair route",
            "given": [MATTER_SECTOR_INPUT_ROUTE],
            "therefore": MATTER_SECTOR_CONCLUSION,
            "status": "locally_linked_from_dirac_pair_route",
        },
        {
            "linkage_id": "gauge_sector_exchange_linkage",
            "depends_on": "stress-divergence identity + sourced Maxwell route",
            "given": [
                GAUGE_STRESS_DIVERGENCE_IDENTITY,
                SOURCED_MAXWELL_ROUTE,
            ],
            "therefore": GAUGE_SECTOR_CONCLUSION,
            "status": "locally_linked_from_sourced_maxwell_route",
        },
    ]


def _blocked_boundary_flags() -> dict[str, bool]:
    return {
        "general_C_k_theorem_linkage_closure": False,
        "general_C_k_closure": False,
        "gap_1_through_gap_8_discharged": False,
        "global_gap_discharge_claimed": False,
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
        "phase2_readiness_claim": False,
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
        "rule_promoted": False,
        "obligation_row_discharged": False,
        "obligation_rows_discharged": False,
        "proof_debt_discharged": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "new_physics_created": False,
        "new_field_or_interaction_expansion_selected": False,
    }


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "psi_A_interaction_exchange_theorem_linkage_chain_synthesis_packet"
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
        "full_toeformal_aggregate_status_for_synthesis": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SYNTHESIS
        ),
        "scoped_lean_targets_status_for_synthesis": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_SYNTHESIS
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


def _consumed_review_valid(review: dict[str, Any]) -> bool:
    return (
        review.get("outcome_id") == GAUGE_CLOSEOUT_REVIEW_OUTCOME
        and review.get("review_result") == GAUGE_CLOSEOUT_REVIEW_RESULT
        and review.get("strict_review_result") == GAUGE_CLOSEOUT_REVIEW_STRICT_OUTCOME
        and review.get("selected_next_target") == CONSUMED_TARGET
        and review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and review.get("accepted") is True
        and review.get("synthesis_target_authorized") is True
        and review.get("synthesis_packet_prepared") is False
        and review.get("general_C_k_theorem_linkage_closure") is False
        and review.get("master_action_promoted") is False
    )


def build_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_cexchange_total_matter_and_gauge_closeouts(
    *,
    closeout_review_path: Path = GAUGE_CLOSEOUT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout_review = _read_json(closeout_review_path)
    acceptance_criteria = {
        "consumes_expected_gauge_closeout_result_review": _consumed_review_valid(
            closeout_review
        ),
        "local_dependency_chain_preserved": (
            closeout_review.get("local_dependency_chain") == LOCAL_DEPENDENCY_CHAIN
        ),
        "lean_status_wording_careful": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SYNTHESIS
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_SYNTHESIS == "PASSED_SERIAL_RERUN"
        ),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_INTERACTION_EXCHANGE_THEOREM_LINKAGE_CHAIN_SYNTHESIS"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID if prepared else "SYNTHESIS_PACKET_BLOCKED",
        "packet_result": PACKET_RESULT if prepared else "SYNTHESIS_PACKET_BLOCKED",
        "strict_packet_result": STRICT_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "consumed_review_outcome": GAUGE_CLOSEOUT_REVIEW_OUTCOME,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if prepared else "remediation",
        "likely_follow_on_target_after_review": LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW,
        "plain_meaning": PLAIN_MEANING,
        "claim_boundary": CLAIM_BOUNDARY,
        "synthesis_claims": SYNTHESIS_CLAIMS,
        "nonclaims": NONCLAIMS,
        "acceptance_criteria": acceptance_criteria,
        "local_dependency_chain": LOCAL_DEPENDENCY_CHAIN,
        "linkage_chain": _linkage_chain(),
        "linkage_chain_count": len(_linkage_chain()),
        "C_exchange_linkage_definition": C_EXCHANGE_LINKAGE_DEFINITION,
        "C_exchange_linkage_input": C_EXCHANGE_LINKAGE_INPUT,
        "C_exchange_linkage_conclusion": C_EXCHANGE_LINKAGE_CONCLUSION,
        "total_conservation_gauge_input": TOTAL_CONSERVATION_GAUGE_INPUT,
        "total_conservation_matter_input": TOTAL_CONSERVATION_MATTER_INPUT,
        "total_conservation_conclusion": TOTAL_CONSERVATION_CONCLUSION,
        "matter_sector_input_route": MATTER_SECTOR_INPUT_ROUTE,
        "matter_sector_conclusion": MATTER_SECTOR_CONCLUSION,
        "gauge_sector_input_route": GAUGE_SECTOR_INPUT_ROUTE,
        "gauge_stress_divergence_identity": GAUGE_STRESS_DIVERGENCE_IDENTITY,
        "sourced_maxwell_route": SOURCED_MAXWELL_ROUTE,
        "gauge_sector_conclusion": GAUGE_SECTOR_CONCLUSION,
        "local_psi_A_interaction_exchange_theorem_linkage_chain_synthesized": (
            prepared
        ),
        "C_exchange_total_matter_and_gauge_linkages_synthesized": prepared,
        "C_exchange_linkage_recorded": prepared,
        "total_conservation_linkage_recorded": prepared,
        "matter_sector_exchange_linkage_recorded": prepared,
        "gauge_sector_exchange_linkage_recorded": prepared,
        "bounded_local_linkages_only": True,
        "new_proof_execution_in_packet": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "synthesis_packet_prepared": prepared,
        "result_review_authorized": prepared,
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_SYNTHESIS,
        "full_toeformal_aggregate_status_for_synthesis": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SYNTHESIS
        ),
        "scoped_lean_targets_status_for_synthesis": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_SYNTHESIS
        ),
        "source_review_report": _ptr(GAUGE_CLOSEOUT_REVIEW_PATH),
        "source_review_evidence": _ptr(GAUGE_CLOSEOUT_REVIEW_LEAN_PACKET_PATH),
        "report_path": _ptr(DEFAULT_OUT),
        "lean_packet_path": _ptr(LEAN_PACKET_PATH),
        "qftgr_aggregate_path": _ptr(QFTGR_AGGREGATE_PATH),
        "current_target_aggregate_path": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
        "release_current_authority_aggregate_path": _ptr(
            RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
        ),
        "validation_policy": _validation_policy(),
    }
    payload.update(_blocked_boundary_flags())
    payload.update(_validation_policy())
    return payload


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Prepare the psi-A interaction exchange theorem-linkage chain "
            "synthesis packet after C_exchange, total, matter, and gauge closeouts."
        )
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=DEFAULT_OUT,
        help="Path for the generated synthesis JSON.",
    )
    args = parser.parse_args()

    payload = (
        build_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_cexchange_total_matter_and_gauge_closeouts()
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(args.out)


if __name__ == "__main__":
    main()
