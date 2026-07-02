from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_report import (
    BOUNDARY_ITEMS as ATTEMPT_BOUNDARY_ITEMS,
    COMPONENTWISE_ZERO_ROUTE,
    C_TRANSPORT_TUPLE_ZERO,
    DEFAULT_OUT as ATTEMPT_PATH,
    KNOWN_PHI_TRANSPORT_CHAIN_FORM,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LEAN_STATUS_WORDING_LINES_FOR_PACKET,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as ATTEMPT_OUTCOME,
    PACKET_ID as ATTEMPT_PACKET_ID,
    PLAIN_MEANING as ATTEMPT_PLAIN_MEANING,
    PREPARED_LINKAGE_TARGET,
    SCHEMA_ID as ATTEMPT_SCHEMA_ID,
    STANDALONE_PHI_TRANSPORT_ROUTE,
    STRICT_ATTEMPT_PREPARATION_RESULT,
    TARGET_CONCLUSION,
    TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT,
    TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT,
    TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-07-01T00:00:00Z"

SCHEMA_ID = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "RESULT_REVIEW_20260701_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "RESULT_REVIEW_ACCEPTS_COMPONENTWISE_TRANSPORT_ZERO_ROUTE_PREPARATION_NO_"
    "THEOREM_DISCHARGE_OR_CK_RULE_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "RESULT_REVIEW_ACCEPTS_ACTION_TO_REGIME_TRANSPORT_MATCH_TARGET_PREPARED_NO_"
    "ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_"
    "result_review_accepts_prepared_componentwise_transport_zero_route_no_theorem_"
    "discharge"
)

NEXT_TARGET = (
    "execute_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route"
)
NEXT_TARGET_KIND = (
    "phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_"
    "execution"
)
SUGGESTED_EXECUTION_OUTCOME = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "EXECUTED_COMPONENTWISE_TRANSPORT_ZERO_LINKAGE_CONSTRUCTED_NO_CK_RULE_"
    "PROMOTION_OR_MASTER_ACTION_PROMOTION"
)
STRICT_SUGGESTED_EXECUTION_OUTCOME = (
    "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "EXECUTED_C_TRANSPORT_PHI_ZERO_FROM_ACTION_TO_REGIME_TRANSPORT_MATCH_NO_"
    "PHI_SECTOR_OR_SEAM_CLOSURE"
)

EXECUTION_ROUTE_TO_AUTHORIZE = COMPONENTWISE_ZERO_ROUTE
PLAIN_MEANING = (
    "The execution target may construct C_transport^phi = 0 only by the "
    "prepared five-component transport zero route, with no promotion of that "
    "route match to action variation or master-action status."
)

ACCEPTED_REVIEW_FINDINGS = [
    "phi-transport theorem-linkage attempt preparation accepted",
    "five-component C_transport^phi tuple preserved",
    "ACTION -> VARIATION zero target preserved",
    "VARIATION -> BRIDGE zero target preserved",
    "BRIDGE -> SOURCE zero target preserved",
    "SOURCE -> RESIDUAL zero target preserved",
    "RESIDUAL -> REGIME zero target preserved",
    "componentwise zero route prepared",
    "target C_transport^phi = 0 prepared",
    "no proof execution",
    "no theorem discharge",
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

BLOCKED_CLAIMS = [
    "no proof execution during review",
    "no theorem discharge during review",
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

ROUTE_PURITY_WATCH_ITEMS = [
    "no C_source^phi substitution",
    "no C_bridge^phi substitution",
    "no A-sector route import",
    "no psi-A route import",
    "no QFT-GR route import",
    "no master-action promotion from transport match",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_"
    "RESULT_REVIEW_20260701_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiTransportTheoremLinkageAttemptFromStandalonePhiTransportRouteResultReview.lean"
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
        "C_transport_phi_discharged": False,
        "C_transport_phi_zero_derived": False,
        "C_transport_phi_theorem_linkage_gap_discharged": False,
        "C_transport_phi_theorem_linkage_obligation_discharged": False,
        "C_transport_phi_proof_executed": False,
        "C_transport_phi_closure_claimed": False,
        "transport_consistency_proved": False,
        "transport_components_proved": False,
        "transport_candidate_rule_proved": False,
        "full_route_alignment_proved": False,
        "route_chain_compatibility_proved": False,
        "source_admissibility_proved": False,
        "bridge_admissibility_proved": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
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
        "master_action_route_substituted": False,
        "J_current_imported": False,
        "C_source_phi_closure_claimed": False,
        "C_bridge_phi_closure_claimed": False,
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


def _attempt_valid(attempt: dict[str, Any]) -> bool:
    component_forms = [row["component_form"] for row in TRANSPORT_COMPONENTS]
    return (
        attempt.get("schema_id") == ATTEMPT_SCHEMA_ID
        and attempt.get("packet_id") == ATTEMPT_PACKET_ID
        and attempt.get("outcome_id") == ATTEMPT_OUTCOME
        and attempt.get("attempt_preparation_result") == ATTEMPT_OUTCOME
        and attempt.get("strict_attempt_preparation_result")
        == STRICT_ATTEMPT_PREPARATION_RESULT
        and attempt.get("selected_next_target") == CONSUMED_TARGET
        and attempt.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and attempt.get("standalone_phi_transport_route")
        == STANDALONE_PHI_TRANSPORT_ROUTE
        and attempt.get("transport_constraint_form") == TRANSPORT_CONSTRAINT_FORM
        and attempt.get("transport_constraint_equation") == TRANSPORT_CONSTRAINT_EQUATION
        and attempt.get("transport_admissibility_constraint_form")
        == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        and attempt.get("transport_component_count") == len(TRANSPORT_COMPONENTS)
        and attempt.get("transport_component_forms") == component_forms
        and attempt.get("componentwise_zero_route") == COMPONENTWISE_ZERO_ROUTE
        and attempt.get("target_conclusion") == TARGET_CONCLUSION
        and attempt.get("proof_attempt_executed") is False
        and attempt.get("theorem_discharged") is False
        and attempt.get("C_transport_phi_discharged") is False
        and attempt.get("master_action_promoted") is False
        and attempt.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_"
            "route_result_review"
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
            "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
        ),
        "scoped_lean_targets_status_for_review": "PASSED_SERIAL_RERUN",
        "lean_status_wording_lines_for_review": LEAN_STATUS_WORDING_LINES_FOR_PACKET,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_result_review(
    *,
    attempt_path: Path = ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    route_text = " ".join(EXECUTION_ROUTE_TO_AUTHORIZE)
    acceptance_criteria = {
        "consumes_expected_attempt_preparation": _attempt_valid(attempt),
        "C_transport_phi_tuple_preserved": (
            TRANSPORT_CONSTRAINT_FORM
            == "C_transport^phi := (Transport_ACTION_VARIATION^phi, "
            "Transport_VARIATION_BRIDGE^phi, Transport_BRIDGE_SOURCE^phi, "
            "Transport_SOURCE_RESIDUAL^phi, Transport_RESIDUAL_REGIME^phi)"
            and TRANSPORT_CONSTRAINT_EQUATION == "C_transport^phi = 0"
        ),
        "componentwise_route_preserved": (
            TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT
            == "Transport_ACTION_VARIATION^phi = 0"
            and TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT
            == "Transport_VARIATION_BRIDGE^phi = 0"
            and TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT
            == "Transport_BRIDGE_SOURCE^phi = 0"
            and TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT
            == "Transport_SOURCE_RESIDUAL^phi = 0"
            and TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT
            == "Transport_RESIDUAL_REGIME^phi = 0"
            and C_TRANSPORT_TUPLE_ZERO == "C_transport^phi = (0, 0, 0, 0, 0)"
            and TARGET_CONCLUSION == "C_transport^phi = 0"
        ),
        "route_contamination_blocked": (
            "C_source^phi =" not in route_text
            and "C_bridge^phi =" not in route_text
            and "J^alpha" not in route_text
            and "F^{mu" not in route_text
            and "QFT-GR" not in route_text
        ),
        "review_only_no_proof_execution": True,
        "review_only_no_theorem_discharge": True,
        "blocked_claims_preserved": ATTEMPT_BOUNDARY_ITEMS
        == [
            "no proof execution during preparation",
            "no theorem discharge",
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
        ],
        "lean_status_wording_preserved": (
            LEAN_STATUS_WORDING_LINES_FOR_PACKET
            == [
                "full ToeFormal aggregate = NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION",
                "scoped Lean targets = PASSED_SERIAL_RERUN",
            ]
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_"
            "PHI_TRANSPORT_ROUTE_RESULT_REVIEW"
        )
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_"
            "PHI_TRANSPORT_ROUTE_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "TRANSPORT_ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "review_result": OUTCOME_ID
        if accepted
        else (
            "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "TRANSPORT_ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "packet_result": OUTCOME_ID
        if accepted
        else (
            "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "TRANSPORT_ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if accepted else "remediation",
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
        "route_purity_watch_items": ROUTE_PURITY_WATCH_ITEMS,
        "route_purity_watch_item_count": len(ROUTE_PURITY_WATCH_ITEMS),
        "selected_obligation": "C_transport^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_transport^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_transport^phi",
        "standalone_phi_transport_route": STANDALONE_PHI_TRANSPORT_ROUTE,
        "standalone_phi_transport_route_preserved": accepted,
        "exact_five_component_transport_tuple_preserved": accepted,
        "target_C_transport_phi_zero_preserved": accepted,
        "componentwise_zero_target_prepared": accepted,
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_admissibility_constraint_form": (
            TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "transport_component_count": len(TRANSPORT_COMPONENTS),
        "transport_component_forms": [
            row["component_form"] for row in TRANSPORT_COMPONENTS
        ],
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
        "transport_action_variation_zero_target_preserved": accepted,
        "transport_variation_bridge_zero_target_preserved": accepted,
        "transport_bridge_source_zero_target_preserved": accepted,
        "transport_source_residual_zero_target_preserved": accepted,
        "transport_residual_regime_zero_target_preserved": accepted,
        "componentwise_zero_route": COMPONENTWISE_ZERO_ROUTE,
        "componentwise_zero_route_count": len(COMPONENTWISE_ZERO_ROUTE),
        "execution_route_to_authorize": EXECUTION_ROUTE_TO_AUTHORIZE,
        "execution_route_to_authorize_count": len(EXECUTION_ROUTE_TO_AUTHORIZE),
        "C_transport_tuple_zero": C_TRANSPORT_TUPLE_ZERO,
        "target_conclusion": TARGET_CONCLUSION,
        "prepared_linkage_target": PREPARED_LINKAGE_TARGET,
        "plain_meaning": PLAIN_MEANING,
        "attempt_plain_meaning": ATTEMPT_PLAIN_MEANING,
        "route_kind": "standalone_phi_transport_componentwise_zero_preparation",
        "known_phi_transport_chain_form": KNOWN_PHI_TRANSPORT_CHAIN_FORM,
        "componentwise_zero_route_prepared": accepted,
        "action_to_regime_transport_match_target_prepared": accepted,
        "action_to_regime_transport_match_promoted_to_master_action": False,
        "same_standalone_phi_transport_registry_tuple": True,
        "same_component_order": True,
        "route_contamination_guard": (
            "review only the prepared componentwise standalone phi transport route; "
            "do not substitute C_source^phi, C_bridge^phi, A-sector, psi-A, "
            "QFT-GR, or master-action routes and do not treat action-to-regime "
            "transport match as action variation or master-action promotion"
        ),
        "boundary_items": BLOCKED_CLAIMS,
        "boundary_item_count": len(BLOCKED_CLAIMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "claim_ladder_position": (
            "below proof execution, theorem discharge, phi-sector closure, "
            "scalar/QFT closure, seam closure, empirical prediction, empirical "
            "confirmation, and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only that the standalone phi-transport "
            "C_transport^phi componentwise zero route was prepared. It preserves "
            "C_transport^phi := (Transport_ACTION_VARIATION^phi, "
            "Transport_VARIATION_BRIDGE^phi, Transport_BRIDGE_SOURCE^phi, "
            "Transport_SOURCE_RESIDUAL^phi, Transport_RESIDUAL_REGIME^phi), "
            "the five zero transport targets, and the prepared targets "
            "C_transport^phi = (0, 0, 0, 0, 0) and C_transport^phi = 0. It "
            "authorizes only the bounded execution target. It does not execute "
            "a proof, discharge C_transport^phi, claim phi-sector closure, "
            "claim scalar/QFT closure, close EM-QFT or QFT-GR, claim general "
            "C_k closure, embed or vary an action, claim empirical validation, "
            "or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_result",
            "fail to accept the prepared componentwise transport zero route",
            "lose C_transport^phi tuple definition",
            "lose ACTION -> VARIATION zero target",
            "lose VARIATION -> BRIDGE zero target",
            "lose BRIDGE -> SOURCE zero target",
            "lose SOURCE -> RESIDUAL zero target",
            "lose RESIDUAL -> REGIME zero target",
            "silently substitute C_source^phi, C_bridge^phi, A-sector, psi-A, QFT-GR, or master-action routes",
            "execute or discharge the theorem during review",
            "claim phi-sector closure",
            "claim scalar/QFT closure",
            "claim EM-QFT or QFT-GR closure",
            "claim general C_k closure",
            "embed or vary an action",
            "treat action-to-regime transport match as master-action promotion",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_PACKET,
        "lean_status_wording_lines": LEAN_STATUS_WORDING_LINES_FOR_PACKET,
        "full_toeformal_aggregate_status_for_review": (
            "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
        ),
        "scoped_lean_targets_status_for_review": "PASSED_SERIAL_RERUN",
        "aggregate_lean_validation_status_for_review": "PASSED_SERIAL_RERUN",
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiTransportTheoremLinkageAttemptFromStandalonePhiTransportRouteResultReview",
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
            "Review the prepared standalone phi-transport C_transport^phi "
            "componentwise zero route without executing or discharging it."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--attempt", type=Path, default=ATTEMPT_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    attempt_path = args.attempt if args.attempt.is_absolute() else REPO_ROOT / args.attempt
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    review = (
        build_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_result_review(
            attempt_path=attempt_path,
            captured_at_utc=args.captured_at_utc,
        )
    )
    path = write_review(review, out)
    print(
        json.dumps(
            {
                "accepted": review["accepted"],
                "out": _ptr(path),
                "review_result": review["review_result"],
                "selected_next_target": review["selected_next_target"],
                "suggested_execution_outcome": review[
                    "suggested_execution_outcome"
                ],
                "proof_attempt_executed": review["proof_attempt_executed"],
                "theorem_discharged": review["theorem_discharged"],
                "master_action_promoted": review["master_action_promoted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if review["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
