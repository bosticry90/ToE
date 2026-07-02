from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_transport_theorem_linkage_obligation_closeout_report import (
    CLAIM_BOUNDARY as CLOSEOUT_CLAIM_BOUNDARY,
    CLOSEOUT_CLAIMS,
    CLOSEOUT_RESULT,
    CLOSEOUT_STATEMENT,
    COMPONENTWISE_ZERO_ROUTE,
    C_TRANSPORT_TUPLE_ZERO,
    DEFAULT_OUT as CLOSEOUT_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_CLOSEOUT,
    LEAN_STATUS_WORDING_LINES_FOR_CLOSEOUT,
    LOCAL_CLOSEOUT_ROUTE,
    LOCAL_CLOSEOUT_ROUTE_TEXT,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    NONCLAIMS,
    OUTCOME_ID as CLOSEOUT_OUTCOME,
    PACKET_ID as CLOSEOUT_PACKET_ID,
    SCHEMA_ID as CLOSEOUT_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT,
    STRICT_CLOSEOUT_RESULT,
    TARGET_CONCLUSION,
    TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT,
    TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT,
    TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-07-01T00:00:00Z"

SCHEMA_ID = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_20260701_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_"
    "STANDALONE_ACTION_TO_REGIME_TRANSPORT_MATCH_LINKED_C_TRANSPORT_PHI_ROUTE_"
    "NO_CK_RULE_PROMOTION_OR_SEAM_CLOSURE"
)
STRICT_REVIEW_RESULT = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_"
    "LOCAL_C_TRANSPORT_PHI_ZERO_ROUTE_NO_ACTION_VARIATION_OR_MASTER_ACTION_"
    "PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_transport_theorem_linkage_obligation_closeout_result_review_accepts_"
    "standalone_action_to_regime_transport_match_linked_C_transport_phi_route_"
    "no_ck_rule_promotion_or_seam_closure"
)

NEXT_TARGET = (
    "select_next_ck_family_theorem_linkage_obligation_after_phi_transport_closeout"
)
NEXT_TARGET_KIND = (
    "ck_family_theorem_linkage_obligation_selector_after_phi_transport_closeout"
)
LIKELY_SELECTOR_FOLLOW_ON_TARGET = (
    "prepare_phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_packet"
)
SELECTOR_QUESTION = (
    "Which remaining C_k theorem-linkage obligation should be attempted next "
    "after C_source^phi, C_bridge^phi, and C_transport^phi have all been "
    "locally closed?"
)
NEXT_STEP_REASON = (
    "The local phi theorem-linkage chain has closed C_source^phi, "
    "C_bridge^phi, and C_transport^phi only. The selector should decide "
    "whether to synthesize that local phi family or move to another unresolved "
    "C_k theorem-linkage obligation."
)
DISCIPLINED_NEXT_STEP = (
    "prepare_phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_packet"
)
CLAIM_BOUNDARY = (
    "local phi C_source/C_bridge/C_transport theorem-linkage only; no "
    "phi-sector closure; no scalar/QFT closure; no QFT-GR closure; no "
    "EM-QFT closure; no seam closure; no general C_k closure; no C_k "
    "promotion; no action embedding; no variation; no empirical validation; "
    "no master-action promotion"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_CLOSEOUT
LEAN_STATUS_WORDING_LINES_FOR_REVIEW = LEAN_STATUS_WORDING_LINES_FOR_CLOSEOUT

ACCEPTED_REVIEW_FINDINGS = [
    "phi-transport theorem-linkage obligation closeout accepted",
    "five-component C_transport^phi tuple preserved",
    "ACTION -> VARIATION zero component preserved",
    "VARIATION -> BRIDGE zero component preserved",
    "BRIDGE -> SOURCE zero component preserved",
    "SOURCE -> RESIDUAL zero component preserved",
    "RESIDUAL -> REGIME zero component preserved",
    "C_transport^phi = 0 locally constructed, reviewed, and closed",
    "no phi-sector closure",
    "no scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no seam closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]

COMPLETED_LOCAL_PHI_THEOREM_LINKAGE_CHAIN = [
    "C_source^phi locally linked",
    "C_bridge^phi locally linked",
    "C_transport^phi locally linked",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_"
        "20260701_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiTransportTheoremLinkageObligationCloseoutResultReview.lean"
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
        "new_transport_formula_invented": False,
        "C_source_phi_route_reused": False,
        "C_bridge_phi_route_reused": False,
        "C_bridge_phi_route_reused_as_transport": False,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "QFT_GR_route_imported": False,
        "QFT_GR_source_route_imported": False,
        "J_current_imported": False,
        "master_action_route_substituted": False,
        "transport_consistency_proved": False,
        "transport_components_proved": False,
        "transport_candidate_rule_proved": False,
        "full_route_alignment_proved": False,
        "route_chain_compatibility_proved": False,
        "source_admissibility_proved": False,
        "bridge_admissibility_proved": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "C_source_phi_closure_claimed": False,
        "C_bridge_phi_closure_claimed": False,
        "C_transport_phi_closure_claimed": False,
        "phi_sector_closure_claimed": False,
        "full_scalar_qft_closure_claimed": False,
        "full_scalar_QFT_closure_claimed": False,
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
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "selector_executed": False,
        "next_theorem_linkage_obligation_selected": False,
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
        and closeout.get("transport_constraint_form") == TRANSPORT_CONSTRAINT_FORM
        and closeout.get("transport_constraint_equation")
        == TRANSPORT_CONSTRAINT_EQUATION
        and closeout.get("transport_admissibility_constraint_form")
        == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        and closeout.get("target_conclusion") == TARGET_CONCLUSION
        and closeout.get("C_transport_tuple_zero") == C_TRANSPORT_TUPLE_ZERO
        and closeout.get("local_closeout_route") == LOCAL_CLOSEOUT_ROUTE
        and closeout.get("C_transport_phi_zero_constructed") is True
        and closeout.get("C_transport_phi_zero_derived") is True
        and closeout.get("C_transport_phi_linkage_constructed") is True
        and closeout.get("phi_sector_closure_claimed") is False
        and closeout.get("full_scalar_qft_closure_claimed") is False
        and closeout.get("qft_gr_closure_claimed") is False
        and closeout.get("em_qft_closure_claimed") is False
        and closeout.get("general_C_k_closure") is False
        and closeout.get("seam_closure_claim") is False
        and closeout.get("rule_promoted") is False
        and closeout.get("master_action_promoted") is False
    )


def _theorem_target_shape() -> dict[str, Any]:
    return {
        "given": [
            TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT,
            TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT,
            TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT,
            TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT,
            TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT,
        ],
        "therefore": [C_TRANSPORT_TUPLE_ZERO, TARGET_CONCLUSION],
        "route": LOCAL_CLOSEOUT_ROUTE,
    }


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_transport_theorem_linkage_obligation_closeout_result_review"
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


def build_phi_transport_theorem_linkage_obligation_closeout_result_review(
    *,
    closeout_path: Path = CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = _read_json(closeout_path)
    acceptance_criteria = {
        "consumes_expected_phi_transport_closeout": _closeout_valid(closeout),
        "five_component_route_preserved": (
            closeout.get("transport_action_variation_zero_component")
            == TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT
            and closeout.get("transport_variation_bridge_zero_component")
            == TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT
            and closeout.get("transport_bridge_source_zero_component")
            == TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT
            and closeout.get("transport_source_residual_zero_component")
            == TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT
            and closeout.get("transport_residual_regime_zero_component")
            == TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT
        ),
        "local_zero_linkage_accepted": (
            closeout.get("phi_transport_theorem_linkage_obligation_locally_closed")
            is True
            and closeout.get("C_transport_phi_zero_constructed") is True
            and closeout.get("C_transport_phi_zero_derived") is True
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
        else "REMEDIATE_PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_TRANSPORT_CLOSEOUT_REVIEW_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "PHI_TRANSPORT_CLOSEOUT_REVIEW_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PHI_TRANSPORT_CLOSEOUT_REVIEW_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selector_question": SELECTOR_QUESTION,
        "likely_selector_follow_on_target": LIKELY_SELECTOR_FOLLOW_ON_TARGET,
        "disciplined_next_step": DISCIPLINED_NEXT_STEP,
        "next_step_reason": NEXT_STEP_REASON,
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
        "completed_local_phi_theorem_linkage_chain": (
            COMPLETED_LOCAL_PHI_THEOREM_LINKAGE_CHAIN
        ),
        "completed_local_phi_theorem_linkage_chain_count": len(
            COMPLETED_LOCAL_PHI_THEOREM_LINKAGE_CHAIN
        ),
        "C_source_phi_locally_linked": accepted,
        "C_bridge_phi_locally_linked": accepted,
        "C_transport_phi_locally_linked": accepted,
        "selected_obligation": "C_transport^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_transport^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_transport^phi",
        "claim_boundary": CLAIM_BOUNDARY,
        "main_boundary": CLAIM_BOUNDARY,
        "closeout_claim_boundary": CLOSEOUT_CLAIM_BOUNDARY,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "theorem_target_shape": _theorem_target_shape(),
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_admissibility_constraint_form": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        "transport_action_variation_zero_component": (
            TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT
        ),
        "transport_variation_bridge_zero_component": (
            TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT
        ),
        "transport_bridge_source_zero_component": (
            TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT
        ),
        "transport_source_residual_zero_component": (
            TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT
        ),
        "transport_residual_regime_zero_component": (
            TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT
        ),
        "C_transport_tuple_zero": C_TRANSPORT_TUPLE_ZERO,
        "target_conclusion": TARGET_CONCLUSION,
        "local_closeout_route": LOCAL_CLOSEOUT_ROUTE,
        "local_closeout_route_text": LOCAL_CLOSEOUT_ROUTE_TEXT,
        "componentwise_zero_route": COMPONENTWISE_ZERO_ROUTE,
        "linkage_route": LOCAL_CLOSEOUT_ROUTE,
        "route_kind": (
            "standalone_phi_transport_action_to_regime_transport_match_closeout_review"
        ),
        "phi_transport_closeout_result_review_accepted": accepted,
        "phi_transport_theorem_linkage_obligation_closeout_accepted": accepted,
        "phi_transport_theorem_linkage_obligation_locally_closed": accepted,
        "five_component_C_transport_phi_tuple_preserved": accepted,
        "transport_action_variation_zero_component_preserved": accepted,
        "transport_variation_bridge_zero_component_preserved": accepted,
        "transport_bridge_source_zero_component_preserved": accepted,
        "transport_source_residual_zero_component_preserved": accepted,
        "transport_residual_regime_zero_component_preserved": accepted,
        "C_transport_phi_zero_locally_linked": accepted,
        "C_transport_phi_zero_constructed": accepted,
        "C_transport_phi_zero_derived": accepted,
        "C_transport_phi_discharged": accepted,
        "C_transport_phi_linkage_constructed": accepted,
        "constructed_reviewed_and_closed": accepted,
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
            "below phi-sector closure, scalar/QFT closure, QFT-GR closure, "
            "EM-QFT closure, seam closure, empirical confirmation, and mature "
            "physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only the local C_transport^phi "
            "theorem-linkage closeout: Transport_ACTION_VARIATION^phi = 0, "
            "Transport_VARIATION_BRIDGE^phi = 0, "
            "Transport_BRIDGE_SOURCE^phi = 0, "
            "Transport_SOURCE_RESIDUAL^phi = 0, and "
            "Transport_RESIDUAL_REGIME^phi = 0; therefore "
            "C_transport^phi = (0, 0, 0, 0, 0) and C_transport^phi = 0. "
            "It authorizes only the next C_k-family theorem-linkage obligation "
            "selector. It claims no phi-sector closure, no scalar/QFT closure, "
            "no QFT-GR closure, no EM-QFT closure, no seam closure, no general "
            "C_k closure, no C_k promotion, no action embedding, no variation, "
            "no empirical validation, and no master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_phi_transport_theorem_linkage_obligation_closeout_result",
            "fail to accept the local phi-transport theorem-linkage closeout",
            "fail to preserve the five-component C_transport^phi tuple",
            "fail to preserve Transport_ACTION_VARIATION^phi = 0",
            "fail to preserve Transport_VARIATION_BRIDGE^phi = 0",
            "fail to preserve Transport_BRIDGE_SOURCE^phi = 0",
            "fail to preserve Transport_SOURCE_RESIDUAL^phi = 0",
            "fail to preserve Transport_RESIDUAL_REGIME^phi = 0",
            "fail to preserve C_transport^phi = 0",
            "claim phi-sector closure",
            "claim scalar/QFT closure",
            "claim QFT-GR closure",
            "claim EM-QFT closure",
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
            "ToeFormal.Derivation.PhiTransportTheoremLinkageObligationCloseoutResultReview",
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
        description="Review the local phi-transport theorem-linkage closeout result."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--closeout", type=Path, default=CLOSEOUT_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    closeout_path = (
        args.closeout if args.closeout.is_absolute() else REPO_ROOT / args.closeout
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_phi_transport_theorem_linkage_obligation_closeout_result_review(
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
                "likely_selector_follow_on_target": payload[
                    "likely_selector_follow_on_target"
                ],
                "phi_sector_closure_claimed": payload["phi_sector_closure_claimed"],
                "qft_gr_closure_claimed": payload["qft_gr_closure_claimed"],
                "seam_closure_claim": payload["seam_closure_claim"],
                "rule_promoted": payload["rule_promoted"],
                "master_action_promoted": payload["master_action_promoted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if payload["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
