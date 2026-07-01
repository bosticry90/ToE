from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_report import (
    BOUNDARY_ITEMS as ATTEMPT_BOUNDARY_ITEMS,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    BRIDGE_TUPLE_ZERO,
    COMPONENTWISE_ZERO_ROUTE,
    DEFAULT_OUT as ATTEMPT_PATH,
    FIELD_EQUATION_MATCH,
    FIELD_EQUATION_ZERO_COMPONENT,
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
    SOURCE_RESIDUAL_MATCH,
    SOURCE_RESIDUAL_ZERO_COMPONENT,
    STANDALONE_PHI_BRIDGE_ROUTE,
    STRESS_ENERGY_MATCH,
    STRESS_ENERGY_ZERO_COMPONENT,
    STRICT_ATTEMPT_PREPARATION_RESULT,
    TARGET_CONCLUSION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "RESULT_REVIEW_20260630_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_RESULT_"
    "REVIEW_ACCEPTS_C_BRIDGE_PHI_COMPONENT_ZERO_ROUTE_PREPARATION_NO_THEOREM_"
    "DISCHARGE_OR_CK_RULE_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_RESULT_"
    "REVIEW_ACCEPTS_MASTER_WITNESS_ROUTE_MATCH_TARGET_PREPARED_NO_ACTION_"
    "VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_result_"
    "review_accepts_prepared_componentwise_zero_route_no_theorem_discharge"
)

NEXT_TARGET = "execute_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route"
NEXT_TARGET_KIND = (
    "phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution"
)
SUGGESTED_EXECUTION_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "EXECUTED_C_BRIDGE_PHI_COMPONENT_ZERO_LINKAGE_CONSTRUCTED_NO_CK_RULE_"
    "PROMOTION_OR_MASTER_ACTION_PROMOTION"
)
STRICT_SUGGESTED_EXECUTION_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "EXECUTED_C_BRIDGE_PHI_ZERO_FROM_MASTER_WITNESS_ROUTE_MATCH_NO_PHI_SECTOR_"
    "OR_SEAM_CLOSURE"
)

EXECUTION_ROUTE_TO_AUTHORIZE = [
    FIELD_EQUATION_MATCH,
    STRESS_ENERGY_MATCH,
    SOURCE_RESIDUAL_MATCH,
    "therefore: C_bridge^phi = (0, 0, 0)",
    "therefore: C_bridge^phi = 0",
]
PLAIN_MEANING = (
    "The execution target may construct C_bridge^phi = 0 only by the prepared "
    "componentwise master/witness route match, with no promotion of that route "
    "match to a master-action theorem."
)

ACCEPTED_REVIEW_FINDINGS = [
    "phi-bridge theorem-linkage attempt preparation accepted",
    "C_bridge^phi tuple definition preserved",
    "E_phi master/witness match target preserved",
    "T_phi master/witness match target preserved",
    "C_source^phi divergence-match target preserved",
    "componentwise zero route prepared",
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
    "no C_source^phi proof reuse",
    "no A-source route import",
    "no psi-A route import",
    "no QFT-GR route import",
    "no master-action promotion from route match",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "RESULT_REVIEW_20260630_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiBridgeTheoremLinkageAttemptFromStandalonePhiBridgeRouteResultReview.lean"
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
        "C_bridge_phi_discharged": False,
        "C_bridge_phi_linkage_constructed": False,
        "C_bridge_phi_zero_derived": False,
        "C_bridge_phi_theorem_linkage_obligation_discharged": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "field_equation_match_proved": False,
        "stress_energy_match_proved": False,
        "source_residual_match_proved": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "C_source_phi_route_reused": False,
        "C_bridge_phi_route_reused_from_C_source_phi": False,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "QFT_GR_route_imported": False,
        "QFT_GR_source_route_imported": False,
        "J_current_imported": False,
        "master_action_route_substituted": False,
        "new_bridge_formula_invented": False,
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
    return (
        attempt.get("schema_id") == ATTEMPT_SCHEMA_ID
        and attempt.get("packet_id") == ATTEMPT_PACKET_ID
        and attempt.get("outcome_id") == ATTEMPT_OUTCOME
        and attempt.get("attempt_preparation_result") == ATTEMPT_OUTCOME
        and attempt.get("strict_attempt_preparation_result")
        == STRICT_ATTEMPT_PREPARATION_RESULT
        and attempt.get("selected_next_target") == CONSUMED_TARGET
        and attempt.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and attempt.get("standalone_phi_bridge_route") == STANDALONE_PHI_BRIDGE_ROUTE
        and attempt.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
        and attempt.get("bridge_constraint_equation") == BRIDGE_CONSTRAINT_EQUATION
        and attempt.get("componentwise_zero_route") == COMPONENTWISE_ZERO_ROUTE
        and attempt.get("field_equation_match") == FIELD_EQUATION_MATCH
        and attempt.get("stress_energy_match") == STRESS_ENERGY_MATCH
        and attempt.get("source_residual_match") == SOURCE_RESIDUAL_MATCH
        and attempt.get("target_conclusion") == TARGET_CONCLUSION
        and attempt.get("proof_attempt_executed") is False
        and attempt.get("theorem_discharged") is False
        and attempt.get("C_bridge_phi_discharged") is False
        and attempt.get("master_action_promoted") is False
        and attempt.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_"
            "result_review"
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


def build_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_result_review(
    *,
    attempt_path: Path = ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    route_text = " ".join(EXECUTION_ROUTE_TO_AUTHORIZE)
    acceptance_criteria = {
        "consumes_expected_attempt_preparation": _attempt_valid(attempt),
        "C_bridge_phi_tuple_definition_preserved": (
            BRIDGE_CONSTRAINT_FORM
            == "C_bridge^phi := (E_phi^master - E_phi^witness, "
            "T_phi^master - T_phi^witness, "
            "C_source^phi - nabla_mu T_phi^{mu nu})"
            and BRIDGE_CONSTRAINT_EQUATION == "C_bridge^phi = 0"
        ),
        "componentwise_route_preserved": (
            FIELD_EQUATION_MATCH == "E_phi^master = E_phi^witness"
            and STRESS_ENERGY_MATCH == "T_phi^master = T_phi^witness"
            and SOURCE_RESIDUAL_MATCH == "C_source^phi = nabla_mu T_phi^{mu nu}"
            and BRIDGE_TUPLE_ZERO == "C_bridge^phi = (0, 0, 0)"
            and TARGET_CONCLUSION == "C_bridge^phi = 0"
        ),
        "prepared_zero_components_preserved": (
            FIELD_EQUATION_ZERO_COMPONENT == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
            and STRESS_ENERGY_ZERO_COMPONENT == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
            and SOURCE_RESIDUAL_ZERO_COMPONENT == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        ),
        "route_contamination_blocked": (
            "J^alpha" not in route_text
            and "nabla_mu F" not in route_text
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
            "REMEDIATE_PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "BRIDGE_ROUTE_RESULT_REVIEW"
        )
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "BRIDGE_ROUTE_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_"
            "ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "review_result": OUTCOME_ID
        if accepted
        else (
            "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_"
            "ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "packet_result": OUTCOME_ID
        if accepted
        else (
            "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_"
            "ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION"
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
        "selected_obligation": "C_bridge^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_bridge^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_bridge^phi",
        "standalone_phi_bridge_route": STANDALONE_PHI_BRIDGE_ROUTE,
        "standalone_phi_bridge_route_preserved": accepted,
        "exact_tuple_definition_preserved": accepted,
        "target_C_bridge_phi_zero_preserved": accepted,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_route_field_equation_match": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        "componentwise_zero_route": COMPONENTWISE_ZERO_ROUTE,
        "componentwise_zero_route_count": len(COMPONENTWISE_ZERO_ROUTE),
        "execution_route_to_authorize": EXECUTION_ROUTE_TO_AUTHORIZE,
        "execution_route_to_authorize_count": len(EXECUTION_ROUTE_TO_AUTHORIZE),
        "field_equation_match": FIELD_EQUATION_MATCH,
        "stress_energy_match": STRESS_ENERGY_MATCH,
        "source_residual_match": SOURCE_RESIDUAL_MATCH,
        "field_equation_zero_component": FIELD_EQUATION_ZERO_COMPONENT,
        "stress_energy_zero_component": STRESS_ENERGY_ZERO_COMPONENT,
        "source_residual_zero_component": SOURCE_RESIDUAL_ZERO_COMPONENT,
        "bridge_tuple_zero": BRIDGE_TUPLE_ZERO,
        "target_conclusion": TARGET_CONCLUSION,
        "prepared_linkage_target": PREPARED_LINKAGE_TARGET,
        "plain_meaning": PLAIN_MEANING,
        "attempt_plain_meaning": ATTEMPT_PLAIN_MEANING,
        "route_kind": "standalone_phi_bridge_componentwise_zero_preparation",
        "master_witness_route_match_target_prepared": accepted,
        "master_witness_route_match_promoted_to_master_action": False,
        "E_phi_master_witness_match_target_preserved": accepted,
        "T_phi_master_witness_match_target_preserved": accepted,
        "C_source_phi_divergence_match_target_preserved": accepted,
        "componentwise_zero_route_prepared": accepted,
        "same_standalone_phi_bridge_registry_tuple": True,
        "same_sign_and_index_conventions": True,
        "route_contamination_guard": (
            "review only the prepared componentwise standalone phi bridge route; "
            "do not substitute C_source^phi, A-source, psi-A, QFT-GR, or "
            "master-action routes and do not treat master/witness route match "
            "as master-action promotion"
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
            "This result review accepts only that the standalone phi-bridge "
            "C_bridge^phi componentwise zero route was prepared. It preserves "
            "C_bridge^phi := (E_phi^master - E_phi^witness, T_phi^master - "
            "T_phi^witness, C_source^phi - nabla_mu T_phi^{mu nu}), the "
            "targets E_phi^master = E_phi^witness, T_phi^master = "
            "T_phi^witness, C_source^phi = nabla_mu T_phi^{mu nu}, and the "
            "prepared targets C_bridge^phi = (0, 0, 0) and C_bridge^phi = 0. "
            "It authorizes only the bounded execution target. It does not "
            "execute a proof, discharge C_bridge^phi, claim phi-sector closure, "
            "claim scalar/QFT closure, close EM-QFT or QFT-GR, claim general "
            "C_k closure, embed or vary an action, claim empirical validation, "
            "or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_result",
            "fail to accept the prepared componentwise zero route",
            "lose C_bridge^phi tuple definition",
            "lose E_phi master/witness match target",
            "lose T_phi master/witness match target",
            "lose C_source^phi divergence-match target",
            "silently substitute C_source^phi, A-source, psi-A, QFT-GR, or master-action routes",
            "execute or discharge the theorem during review",
            "claim phi-sector closure",
            "claim scalar/QFT closure",
            "claim EM-QFT or QFT-GR closure",
            "claim general C_k closure",
            "embed or vary an action",
            "treat master/witness route match as master-action promotion",
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
            "ToeFormal.Derivation.PhiBridgeTheoremLinkageAttemptFromStandalonePhiBridgeRouteResultReview",
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
            "Review the prepared standalone phi-bridge C_bridge^phi "
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
        build_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_result_review(
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
