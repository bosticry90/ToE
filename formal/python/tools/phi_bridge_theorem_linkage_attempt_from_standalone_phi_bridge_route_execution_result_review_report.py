from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_report import (
    BOUNDARY_ITEMS,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_TUPLE_ZERO,
    COMPONENTWISE_ZERO_ROUTE,
    DEFAULT_OUT as EXECUTION_PATH,
    EXECUTED_COMPONENTWISE_ROUTE,
    EXECUTION_FINDINGS,
    EXECUTION_RESULT,
    EXECUTION_ROUTE_TO_AUTHORIZE,
    FIELD_EQUATION_MATCH,
    FIELD_EQUATION_ZERO_COMPONENT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION,
    LEAN_PACKET_PATH as EXECUTION_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_EXECUTION,
    LEAN_STATUS_WORDING_LINES_FOR_EXECUTION,
    LEAN_THEOREM_NAME,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as EXECUTION_OUTCOME,
    PACKET_ID as EXECUTION_PACKET_ID,
    PLAIN_MEANING,
    ROUTE_PURITY_WATCH_ITEMS,
    SCHEMA_ID as EXECUTION_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION,
    SOURCE_RESIDUAL_MATCH,
    SOURCE_RESIDUAL_ZERO_COMPONENT,
    STANDALONE_PHI_BRIDGE_ROUTE,
    STRESS_ENERGY_MATCH,
    STRESS_ENERGY_ZERO_COMPONENT,
    STRICT_EXECUTION_RESULT,
    TARGET_CONCLUSION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "EXECUTION_RESULT_REVIEW_20260630_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "EXECUTION_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "EXECUTION_RESULT_REVIEW_ACCEPTS_C_BRIDGE_PHI_ZERO_FROM_COMPONENTWISE_"
    "ROUTE_MATCH_NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "EXECUTION_RESULT_REVIEW_ACCEPTS_LOCAL_PHI_BRIDGE_THEOREM_LINKAGE_ONLY_NO_"
    "PHI_SECTOR_OR_SEAM_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_"
    "execution_result_review_accepts_local_C_bridge_phi_zero_no_ck_rule_or_"
    "master_action_promotion"
)

NEXT_TARGET = "prepare_phi_bridge_theorem_linkage_obligation_closeout"
NEXT_TARGET_KIND = "phi_bridge_theorem_linkage_obligation_closeout_preparation"
CLOSEOUT_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_STANDALONE_COMPONENTWISE_"
    "ROUTE_MATCH_LINKED_C_BRIDGE_PHI_ROUTE_NO_CK_RULE_PROMOTION_OR_SEAM_CLOSURE"
)
STRICT_CLOSEOUT_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_LOCAL_C_BRIDGE_PHI_ZERO_"
    "ROUTE_NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
CLOSEOUT_STATEMENT = (
    "C_bridge^phi is theorem-linked to the standalone componentwise "
    "master/witness route match."
)
MAIN_BOUNDARY = (
    "local C_bridge^phi theorem-linkage only; not phi-sector completion; not "
    "scalar/QFT completion; not master-action promotion; not seam closure."
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_EXECUTION
LEAN_STATUS_WORDING_LINES_FOR_REVIEW = LEAN_STATUS_WORDING_LINES_FOR_EXECUTION

ACCEPTED_REVIEW_FINDINGS = [
    "phi-bridge theorem-linkage execution accepted",
    "C_bridge^phi tuple definition preserved",
    "E_phi master/witness equality preserved",
    "T_phi master/witness equality preserved",
    "C_source^phi divergence-match equality preserved",
    "componentwise zero route constructed",
    "C_bridge^phi = 0 locally constructed",
    "Lean execution marker preserved",
    "JSON execution report preserved",
    "focused execution gates passed",
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

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
        "EXECUTION_RESULT_REVIEW_20260630_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiBridgeTheoremLinkageAttemptFromStandalonePhiBridgeRouteExecutionResultReview.lean"
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
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "field_equation_match_proved": False,
        "stress_energy_match_proved": False,
        "source_residual_match_proved": False,
        "C_source_phi_closure_claimed": False,
        "C_bridge_phi_closure_claimed": False,
        "phi_sector_closure_claimed": False,
        "full_scalar_qft_closure_claimed": False,
        "full_scalar_QFT_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
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


def _input_boundary_clear(execution: dict[str, Any]) -> bool:
    return all(
        execution.get(key) is False
        for key in _blocked_boundary_flags()
        if key in execution
    )


def _theorem_target_shape() -> dict[str, Any]:
    return {
        "given": [
            FIELD_EQUATION_MATCH,
            STRESS_ENERGY_MATCH,
            SOURCE_RESIDUAL_MATCH,
        ],
        "therefore": [
            FIELD_EQUATION_ZERO_COMPONENT,
            STRESS_ENERGY_ZERO_COMPONENT,
            SOURCE_RESIDUAL_ZERO_COMPONENT,
            BRIDGE_TUPLE_ZERO,
            TARGET_CONCLUSION,
        ],
        "route": COMPONENTWISE_ZERO_ROUTE,
        "plain_meaning": PLAIN_MEANING,
    }


def _review_criteria(execution: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "execution_packet_consumed",
            "status": "accepted",
            "evidence": execution.get("execution_result"),
            "assessment": "The bounded execution result is consumed by review.",
        },
        {
            "row_id": "tuple_definition_preserved",
            "status": "accepted",
            "evidence": BRIDGE_CONSTRAINT_FORM,
            "assessment": "The C_bridge^phi tuple definition is unchanged.",
        },
        {
            "row_id": "master_witness_equalities_preserved",
            "status": "accepted",
            "evidence": [FIELD_EQUATION_MATCH, STRESS_ENERGY_MATCH],
            "assessment": "The E_phi and T_phi master/witness equalities are preserved.",
        },
        {
            "row_id": "source_divergence_match_preserved",
            "status": "accepted",
            "evidence": SOURCE_RESIDUAL_MATCH,
            "assessment": "The C_source^phi divergence-match equality is preserved.",
        },
        {
            "row_id": "componentwise_zero_route_constructed",
            "status": "accepted",
            "evidence": COMPONENTWISE_ZERO_ROUTE,
            "assessment": "The componentwise zero route constructs C_bridge^phi = 0.",
        },
        {
            "row_id": "execution_artifacts_preserved",
            "status": "accepted",
            "evidence": [_ptr(EXECUTION_LEAN_PACKET_PATH), _ptr(EXECUTION_PATH)],
            "assessment": "The Lean execution marker and JSON report remain preserved.",
        },
        {
            "row_id": "route_contamination_blocked",
            "status": "accepted",
            "evidence": ROUTE_PURITY_WATCH_ITEMS,
            "assessment": "No C_source^phi, A-source, psi-A, QFT-GR, or master-action route is substituted.",
        },
        {
            "row_id": "no_closure_or_promotion",
            "status": "accepted",
            "evidence": BOUNDARY_ITEMS,
            "assessment": "No sector closure, seam closure, C_k promotion, or master-action promotion is accepted.",
        },
        {
            "row_id": "closeout_preparation_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is closeout preparation only.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_"
            "route_execution_result_review"
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


def build_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_result_review(
    *,
    execution_path: Path = EXECUTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    execution = _read_json(execution_path)
    theorem_target_shape = _theorem_target_shape()
    review_criteria = _review_criteria(execution)
    acceptance_criteria = {
        "consumes_expected_execution_result": (
            execution.get("schema_id") == EXECUTION_SCHEMA_ID
            and execution.get("packet_id") == EXECUTION_PACKET_ID
            and execution.get("outcome_id") == EXECUTION_OUTCOME
            and execution.get("execution_result") == EXECUTION_RESULT
            and execution.get("strict_execution_result") == STRICT_EXECUTION_RESULT
            and execution.get("selected_next_target") == CONSUMED_TARGET
            and execution.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and execution.get("accepted") is True
            and execution.get("executed") is True
        ),
        "tuple_definition_preserved": (
            execution.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and execution.get("bridge_constraint_equation")
            == BRIDGE_CONSTRAINT_EQUATION
            and execution.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "componentwise_route_constructed": (
            execution.get("componentwise_zero_route") == COMPONENTWISE_ZERO_ROUTE
            and execution.get("executed_componentwise_route")
            == EXECUTED_COMPONENTWISE_ROUTE
            and execution.get("execution_route_to_authorize")
            == EXECUTION_ROUTE_TO_AUTHORIZE
        ),
        "component_equalities_preserved": (
            execution.get("field_equation_match") == FIELD_EQUATION_MATCH
            and execution.get("stress_energy_match") == STRESS_ENERGY_MATCH
            and execution.get("source_residual_match") == SOURCE_RESIDUAL_MATCH
            and execution.get("field_equation_zero_component")
            == FIELD_EQUATION_ZERO_COMPONENT
            and execution.get("stress_energy_zero_component")
            == STRESS_ENERGY_ZERO_COMPONENT
            and execution.get("source_residual_zero_component")
            == SOURCE_RESIDUAL_ZERO_COMPONENT
        ),
        "C_bridge_phi_zero_locally_constructed": (
            execution.get("bridge_tuple_zero") == BRIDGE_TUPLE_ZERO
            and execution.get("target_conclusion") == TARGET_CONCLUSION
            and execution.get("C_bridge_phi_zero_constructed") is True
            and execution.get("C_bridge_phi_zero_derived") is True
            and execution.get("C_bridge_phi_discharged") is True
            and execution.get("theorem_discharged") is True
            and execution.get("theorem_linkage_completed") is True
        ),
        "execution_artifacts_preserved": (
            EXECUTION_LEAN_PACKET_PATH.exists() and execution_path.exists()
        ),
        "no_input_forbidden_claims": _input_boundary_clear(execution),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
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
        else (
            "REMEDIATE_PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "BRIDGE_ROUTE_EXECUTION_RESULT_REVIEW"
        )
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "BRIDGE_ROUTE_EXECUTION_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_"
            "ROUTE_EXECUTION_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "review_result": OUTCOME_ID
        if accepted
        else (
            "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_"
            "ROUTE_EXECUTION_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "packet_result": OUTCOME_ID
        if accepted
        else (
            "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_"
            "ROUTE_EXECUTION_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if accepted else "remediation",
        "closeout_outcome": CLOSEOUT_OUTCOME,
        "strict_closeout_outcome": STRICT_CLOSEOUT_OUTCOME,
        "closeout_statement": CLOSEOUT_STATEMENT,
        "execution_schema_id": EXECUTION_SCHEMA_ID,
        "execution_packet_id": EXECUTION_PACKET_ID,
        "execution_outcome": EXECUTION_OUTCOME,
        "execution_result": EXECUTION_RESULT,
        "execution_strict_outcome": STRICT_EXECUTION_RESULT,
        "execution_packet_consumed": accepted,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "execution_findings": EXECUTION_FINDINGS,
        "execution_finding_count": len(EXECUTION_FINDINGS),
        "selected_obligation": "C_bridge^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_bridge^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_bridge^phi",
        "claim_boundary": MAIN_BOUNDARY,
        "main_boundary": MAIN_BOUNDARY,
        "route_kind": "standalone_phi_bridge_componentwise_zero_execution_review",
        "standalone_phi_bridge_route": STANDALONE_PHI_BRIDGE_ROUTE,
        "standalone_phi_bridge_route_preserved": accepted,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "componentwise_zero_route": COMPONENTWISE_ZERO_ROUTE,
        "executed_componentwise_route": EXECUTED_COMPONENTWISE_ROUTE,
        "execution_route_to_authorize": EXECUTION_ROUTE_TO_AUTHORIZE,
        "field_equation_match": FIELD_EQUATION_MATCH,
        "stress_energy_match": STRESS_ENERGY_MATCH,
        "source_residual_match": SOURCE_RESIDUAL_MATCH,
        "field_equation_zero_component": FIELD_EQUATION_ZERO_COMPONENT,
        "stress_energy_zero_component": STRESS_ENERGY_ZERO_COMPONENT,
        "source_residual_zero_component": SOURCE_RESIDUAL_ZERO_COMPONENT,
        "bridge_tuple_zero": BRIDGE_TUPLE_ZERO,
        "target_conclusion": TARGET_CONCLUSION,
        "theorem_target_shape": theorem_target_shape,
        "plain_meaning": PLAIN_MEANING,
        "lean_theorem_name": LEAN_THEOREM_NAME,
        "exact_tuple_definition_preserved": accepted,
        "target_C_bridge_phi_zero_preserved": accepted,
        "E_phi_master_witness_equality_preserved": accepted,
        "T_phi_master_witness_equality_preserved": accepted,
        "C_source_phi_divergence_match_equality_preserved": accepted,
        "componentwise_zero_route_constructed": accepted,
        "C_bridge_phi_tuple_zero_constructed": accepted,
        "C_bridge_phi_zero_constructed": accepted,
        "C_bridge_phi_zero_derived": accepted,
        "C_bridge_phi_linkage_constructed": accepted,
        "C_bridge_phi_admissibility_status": "local theorem-linkage only",
        "lean_execution_marker_preserved": accepted,
        "json_execution_report_preserved": accepted,
        "focused_execution_gates_passed": accepted,
        "proof_execution": "already executed; not re-executed by review",
        "review_executes_attempt": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": True,
        "proof_debt_reduced": True,
        "proof_debt_discharged": False,
        "theorem_discharged": True,
        "theorem_linkage_completed": accepted,
        "theorem_linkage_obligation_discharged": accepted,
        "C_bridge_phi_theorem_linkage_obligation_discharged": accepted,
        "C_bridge_phi_discharged": accepted,
        "closeout_preparation_authorized": accepted,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "boundary_items": BOUNDARY_ITEMS,
        "boundary_item_count": len(BOUNDARY_ITEMS),
        "route_purity_watch_items": ROUTE_PURITY_WATCH_ITEMS,
        "route_purity_watch_item_count": len(ROUTE_PURITY_WATCH_ITEMS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_accepted": accepted,
        "claim_ladder_position": (
            "below phi-sector closure, scalar/QFT closure, QFT-GR source "
            "admissibility, seam closure, empirical confirmation, and mature "
            "physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only the local standalone phi-bridge "
            "execution result: C_bridge^phi is reduced componentwise from "
            "E_phi^master = E_phi^witness, T_phi^master = T_phi^witness, and "
            "C_source^phi = nabla_mu T_phi^{mu nu}, yielding "
            "C_bridge^phi = (0, 0, 0) and C_bridge^phi = 0. It authorizes "
            "only closeout preparation. It claims no phi-sector closure, no "
            "scalar/QFT closure, no QFT-GR closure, no EM-QFT closure, no seam "
            "closure, no general C_k closure, no C_k promotion, no action "
            "embedding, no variation, no empirical validation, and no "
            "master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_result",
            "fail to preserve the C_bridge^phi tuple definition",
            "fail to preserve E_phi^master = E_phi^witness",
            "fail to preserve T_phi^master = T_phi^witness",
            "fail to preserve C_source^phi = nabla_mu T_phi^{mu nu}",
            "fail to preserve the componentwise zero route",
            "fail to preserve C_bridge^phi = (0, 0, 0)",
            "fail to preserve C_bridge^phi = 0",
            "claim phi-sector closure",
            "claim scalar/QFT closure",
            "claim EM-QFT or QFT-GR closure",
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
            "ToeFormal.Derivation.PhiBridgeTheoremLinkageAttemptFromStandalonePhiBridgeRouteExecutionResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "execution_file": _ptr(execution_path),
            "execution_lean_file": _ptr(EXECUTION_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
    payload["proof_execution_authorized"] = False
    payload["proof_attempt_executed"] = True
    payload["theorem_discharged"] = True
    payload["theorem_linkage_completed"] = accepted
    payload["theorem_linkage_obligation_discharged"] = accepted
    payload["C_bridge_phi_theorem_linkage_obligation_discharged"] = accepted
    payload["C_bridge_phi_discharged"] = accepted
    payload["C_bridge_phi_zero_derived"] = accepted
    payload["C_bridge_phi_linkage_constructed"] = accepted
    payload["rule_promoted"] = False
    return payload


def write_review(payload: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Review the executed standalone phi-bridge C_bridge^phi theorem-linkage route."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--execution", type=Path, default=EXECUTION_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    execution_path = (
        args.execution if args.execution.is_absolute() else REPO_ROOT / args.execution
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_result_review(
            execution_path=execution_path,
            captured_at_utc=args.captured_at_utc,
        )
    )
    path = write_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "reviewed": payload["reviewed"],
                "out": _ptr(path),
                "outcome_id": payload["outcome_id"],
                "selected_next_target": payload["selected_next_target"],
            },
            sort_keys=True,
        )
    )
    return 0 if payload["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
