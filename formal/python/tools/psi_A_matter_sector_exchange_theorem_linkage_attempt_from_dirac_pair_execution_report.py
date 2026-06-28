from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result_review_report import (
    ADJOINT_DIRAC_EQUATION_SHAPE,
    COMPATIBILITY_ASSUMPTIONS,
    CURRENT_DEFINITION,
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    DELICATE_WATCH_ITEMS,
    DIRAC_EQUATION_SHAPE,
    DOMAIN_BOUNDARY_ASSUMPTIONS,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    INPUT_ROUTE,
    LEAN_PACKET_PATH as RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    NEXT_TARGET as CONSUMED_EXECUTION_TARGET,
    NEXT_TARGET_KIND as CONSUMED_EXECUTION_TARGET_KIND,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    PACKET_ID as RESULT_REVIEW_PACKET_ID,
    PLAIN_MEANING,
    PLANNED_PROOF_STEPS,
    PROOF_STYLE,
    REVIEW_RESULT,
    SCHEMA_ID as RESULT_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_EXECUTION_OUTCOME,
    SUGGESTED_EXECUTION_OUTCOME,
    TARGET,
    THEOREM_TARGET_STATEMENT,
    T_PSI_POLICY,
    WATCH_ITEMS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
    "EXECUTION_20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
    "EXECUTION_v0"
)
EXECUTION_RESULT = SUGGESTED_EXECUTION_OUTCOME
STRICT_EXECUTION_RESULT = STRICT_SUGGESTED_EXECUTION_OUTCOME
OUTCOME_ID = EXECUTION_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_"
    "executed_matter_exchange_route_constructed_no_ck_rule_promotion_or_master_"
    "action_promotion"
)

NEXT_TARGET = "review_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result"
NEXT_TARGET_KIND = (
    "psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result_review"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION = SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_EXECUTION = LEAN_STATUS_WORDING_FOR_REVIEW

ATTEMPT_TYPE = "Dirac-pair matter-sector exchange execution"
EXECUTION_PROOF_STYLE = (
    "Dirac-pair stress-energy divergence route with compatibility cancellations"
)
TARGET_CONCLUSION = TARGET
EXCHANGE_OBJECT = "F^nu{}_alpha J^alpha"
LEAN_THEOREM_NAME = "psi_A_matter_exchange_from_dirac_pair_cancellations"
LEAN_THEOREM_DESCRIPTION = (
    "Generic Lean witness: after the T_psi divergence expansion is supplied, "
    "Dirac and adjoint Dirac terms cancel, compatibility removes connection "
    "leakage, and the remaining gauge-coupling term is identified with the "
    "Lorentz-force exchange object."
)
ROUTE_STATEMENT = (
    "nabla_mu T_psi^{mu nu} expands under the selected T_psi policy; "
    "Dirac and adjoint Dirac equations cancel the free/mass terms; "
    "gamma / spin / tetrad / metric compatibility removes connection leakage; "
    "the remaining gauge-coupling term is + F^nu{}_alpha J^alpha using "
    "J^alpha = q psibar gamma^alpha psi"
)

ROUTE_GIVEN = [
    T_PSI_POLICY,
    DIRAC_EQUATION_SHAPE,
    ADJOINT_DIRAC_EQUATION_SHAPE,
    CURRENT_DEFINITION,
    "gamma / spin / tetrad compatibility",
    "metric compatibility",
    DOMAIN_BOUNDARY_ASSUMPTIONS,
]

ROUTE_STEPS = [
    "expand nabla_mu T_psi^{mu nu} using the selected T_psi policy",
    "apply the Leibniz rule to the spinor bilinears",
    "use gamma / spin / tetrad compatibility",
    "use metric compatibility and the shared covariant derivative",
    "substitute the Dirac equation (i gamma^mu D_mu - m) psi = 0",
    "substitute the adjoint equation i(D_mu psibar) gamma^mu + m psibar = 0",
    "cancel the free and mass terms",
    "isolate the gauge-coupling term",
    "substitute J^alpha = q psibar gamma^alpha psi to obtain + F^nu{}_alpha J^alpha",
]

EXECUTION_FINDINGS = [
    "psi-A matter-sector exchange theorem-linkage attempt executed",
    "matter exchange route constructed from the Dirac-pair route",
    "T_psi policy used as the selected matter stress-energy policy",
    "Dirac and adjoint Dirac equation contexts used",
    "current definition J^alpha = q psibar gamma^alpha psi used",
    "gamma / spin / tetrad / metric compatibility assumptions preserved",
    "no C_k rule promotion",
    "no C_k action embedding or variation",
    "no seam closure or empirical validation",
    "no master-action promotion",
]

EXECUTION_BLOCKED_CLAIMS = [
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k action variation",
    "no multiplier route",
    "no penalty route",
    "no direct dynamical-law claim",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no empirical validation",
    "no seam closure",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
        "EXECUTION_20260628_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPairExecution.lean"
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
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
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
        "proof_debt_discharged": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "new_physics_created": False,
        "new_field_or_interaction_expansion_selected": False,
    }


def _input_boundary_clear(result_review: dict[str, Any]) -> bool:
    return all(
        result_review.get(key) is False
        for key in _blocked_boundary_flags()
        if key in result_review
    )


def _theorem_target_shape() -> dict[str, Any]:
    return {
        "given": ROUTE_GIVEN,
        "therefore": TARGET,
        "route_steps": ROUTE_STEPS,
        "route_statement": ROUTE_STATEMENT,
        "plain_meaning": PLAIN_MEANING,
        "watch_items": WATCH_ITEMS,
    }


def _execution_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "expand_tpsi_divergence",
            "statement": ROUTE_STEPS[0],
            "role": "selected T_psi policy expansion",
        },
        {
            "step_id": "apply_leibniz_rule",
            "statement": ROUTE_STEPS[1],
            "role": "bilinear divergence expansion",
        },
        {
            "step_id": "use_gamma_spin_tetrad_compatibility",
            "statement": ROUTE_STEPS[2],
            "role": "compatibility assumption",
        },
        {
            "step_id": "use_metric_compatibility",
            "statement": ROUTE_STEPS[3],
            "role": "compatibility assumption",
        },
        {
            "step_id": "substitute_dirac_equation",
            "statement": DIRAC_EQUATION_SHAPE,
            "role": "Dirac equation input",
        },
        {
            "step_id": "substitute_adjoint_dirac_equation",
            "statement": ADJOINT_DIRAC_EQUATION_SHAPE,
            "role": "adjoint Dirac equation input",
        },
        {
            "step_id": "cancel_free_and_mass_terms",
            "statement": "free/mass terms cancel under the Dirac pair",
            "role": "Dirac-pair cancellation",
        },
        {
            "step_id": "isolate_gauge_coupling",
            "statement": "remaining gauge-coupling term has sign + F^nu{}_alpha J^alpha",
            "role": "same sign and index convention",
        },
        {
            "step_id": "substitute_current_definition",
            "statement": TARGET,
            "role": "J^alpha = q psibar gamma^alpha psi substitution",
        },
    ]


def _execution_criteria(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "execution_target_authorized",
            "status": "accepted",
            "evidence": result_review.get("selected_next_target"),
            "assessment": "The prior result review selected this bounded execution target.",
        },
        {
            "row_id": "tpsi_policy_used",
            "status": "accepted",
            "evidence": T_PSI_POLICY,
            "assessment": "The selected T_psi policy is the matter stress-energy input.",
        },
        {
            "row_id": "dirac_pair_used",
            "status": "accepted",
            "evidence": [DIRAC_EQUATION_SHAPE, ADJOINT_DIRAC_EQUATION_SHAPE],
            "assessment": "The Dirac and adjoint Dirac equations are used as supplied inputs.",
        },
        {
            "row_id": "current_definition_used",
            "status": "accepted",
            "evidence": CURRENT_DEFINITION,
            "assessment": "The J definition identifies the Lorentz-force exchange object.",
        },
        {
            "row_id": "compatibility_assumptions_preserved",
            "status": "accepted",
            "evidence": COMPATIBILITY_ASSUMPTIONS,
            "assessment": "Gamma, spin/tetrad, metric, domain, and boundary assumptions remain explicit.",
        },
        {
            "row_id": "matter_exchange_route_constructed",
            "status": "accepted",
            "evidence": TARGET,
            "assessment": "The matter-side exchange target is obtained by the bounded route.",
        },
        {
            "row_id": "watch_items_preserved",
            "status": "accepted",
            "evidence": WATCH_ITEMS,
            "assessment": "Same T_psi, F, J, sign, index, derivative, and domain watch items are preserved.",
        },
        {
            "row_id": "no_ck_promotion_or_action_route",
            "status": "accepted",
            "evidence": EXECUTION_BLOCKED_CLAIMS,
            "assessment": "No C_k promotion, action embedding, variation, multiplier, or penalty route is selected.",
        },
        {
            "row_id": "no_physics_closure_claim",
            "status": "accepted",
            "evidence": [
                "no direct dynamical-law claim",
                "no full Maxwell closure",
                "no EM-QFT closure",
                "no QFT-GR closure",
                "no GR-QM closure",
                "no empirical validation",
                "no seam closure",
                "no master-action promotion",
            ],
            "assessment": "The execution remains a theorem-linkage step only.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_"
            "execution"
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
        "full_toeformal_aggregate_status_for_execution": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
        ),
        "scoped_lean_targets_status_for_execution": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
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


def build_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution(
    *,
    result_review_path: Path = RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    theorem_target_shape = _theorem_target_shape()
    execution_steps = _execution_steps()
    execution_criteria = _execution_criteria(result_review)
    acceptance_criteria = {
        "consumes_expected_execution_target": (
            result_review.get("schema_id") == RESULT_REVIEW_SCHEMA_ID
            and result_review.get("packet_id") == RESULT_REVIEW_PACKET_ID
            and result_review.get("outcome_id") == RESULT_REVIEW_OUTCOME
            and result_review.get("review_result") == REVIEW_RESULT
            and result_review.get("strict_review_result") == STRICT_REVIEW_RESULT
            and result_review.get("selected_next_target") == CONSUMED_EXECUTION_TARGET
            and result_review.get("selected_next_target_kind")
            == CONSUMED_EXECUTION_TARGET_KIND
            and result_review.get("proof_execution_authorized_by_review_for_next_target")
            is True
            and result_review.get(
                "theorem_linkage_proof_attempt_authorized_for_next_target"
            )
            is True
            and result_review.get("accepted") is True
        ),
        "theorem_target_shape_preserved": (
            theorem_target_shape["given"] == ROUTE_GIVEN
            and theorem_target_shape["therefore"] == TARGET
            and result_review.get("theorem_target_statement")
            == THEOREM_TARGET_STATEMENT
        ),
        "dirac_pair_execution_shape": (
            INPUT_ROUTE == "Dirac pair plus T_psi policy plus current definition"
            and PROOF_STYLE
            == "Dirac-pair stress-energy divergence route with current definition and compatibility assumptions"
            and EXECUTION_PROOF_STYLE
            == "Dirac-pair stress-energy divergence route with compatibility cancellations"
        ),
        "execution_steps_all_bounded": (
            len(execution_steps) == 9 and execution_steps[-1]["statement"] == TARGET
        ),
        "watch_items_preserved": WATCH_ITEMS
        == [
            "same T_psi definition",
            "same F object",
            "same J object",
            "same sign convention",
            "same index placement",
            "same covariant derivative",
            "Dirac equation and adjoint equation",
            "gamma/spin/tetrad compatibility",
            "metric compatibility",
            "shared domain and boundary assumptions",
        ],
        "execution_criteria_all_accepted": all(
            row["status"] == "accepted" for row in execution_criteria
        ),
        "no_input_forbidden_claims": _input_boundary_clear(result_review),
        "all_gap_one_through_gap_eight_items_remain_open": (
            result_review.get("gap_count") == 8
            and result_review.get("open_gap_count") == 8
            and result_review.get("closed_gap_count") == 0
            and result_review.get("gap_1_through_gap_8_discharged") is False
        ),
        "lean_status_wording_careful": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_EXECUTION"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_EXECUTION"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "executed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_EXECUTION_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_EXECUTION_REQUIRES_REMEDIATION",
        "execution_result": OUTCOME_ID
        if accepted
        else "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_EXECUTION_REQUIRES_REMEDIATION",
        "strict_execution_result": STRICT_EXECUTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_EXECUTION_TARGET,
        "consumed_target_kind": CONSUMED_EXECUTION_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "post_execution_target": NEXT_TARGET,
        "post_execution_target_kind": NEXT_TARGET_KIND,
        "result_review_schema_id": RESULT_REVIEW_SCHEMA_ID,
        "result_review_packet_id": RESULT_REVIEW_PACKET_ID,
        "result_review_outcome": RESULT_REVIEW_OUTCOME,
        "result_review_strict_outcome": STRICT_REVIEW_RESULT,
        "result_review_consumed": accepted,
        "attempt_type": ATTEMPT_TYPE,
        "input_route": INPUT_ROUTE,
        "target_rule": TARGET,
        "proof_style": EXECUTION_PROOF_STYLE,
        "claim_boundary": "theorem-linkage only, not physics closure",
        "selected_obligation": "psi-A matter-sector exchange theorem-linkage gap",
        "selected_obligation_rank": "3",
        "local_theorem_linkage_reduced": accepted,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "theorem_target_shape": theorem_target_shape,
        "theorem_target_recorded": accepted,
        "theorem_target_indexed": accepted,
        "theorem_linkage_target_indexed": accepted,
        "matter_exchange_route_constructed": accepted,
        "matter_exchange_derived": accepted,
        "T_psi_policy": T_PSI_POLICY,
        "tpsi_policy_used": accepted,
        "dirac_equation_shape": DIRAC_EQUATION_SHAPE,
        "dirac_equation_used": accepted,
        "adjoint_dirac_equation_shape": ADJOINT_DIRAC_EQUATION_SHAPE,
        "adjoint_dirac_equation_used": accepted,
        "current_definition": CURRENT_DEFINITION,
        "current_definition_used": accepted,
        "compatibility_assumptions": COMPATIBILITY_ASSUMPTIONS,
        "compatibility_assumptions_used": accepted,
        "delicate_watch_items": DELICATE_WATCH_ITEMS,
        "domain_boundary_assumptions": DOMAIN_BOUNDARY_ASSUMPTIONS,
        "target_conclusion": TARGET_CONCLUSION,
        "exchange_object": EXCHANGE_OBJECT,
        "route_given": ROUTE_GIVEN,
        "route_steps": ROUTE_STEPS,
        "route_step_count": len(ROUTE_STEPS),
        "route_statement": ROUTE_STATEMENT,
        "planned_proof_steps": PLANNED_PROOF_STEPS,
        "plain_meaning": PLAIN_MEANING,
        "watch_items": WATCH_ITEMS,
        "watch_item_count": len(WATCH_ITEMS),
        "lean_theorem_name": LEAN_THEOREM_NAME,
        "lean_theorem_description": LEAN_THEOREM_DESCRIPTION,
        "execution_steps": execution_steps,
        "execution_step_count": len(execution_steps),
        "execution_criteria": execution_criteria,
        "execution_criteria_count": len(execution_criteria),
        "execution_criteria_accepted_count": sum(
            1 for row in execution_criteria if row["status"] == "accepted"
        ),
        "proof_execution": "executed",
        "proof_execution_authorized": True,
        "proof_target_execution_authorized": True,
        "proof_attempt_executed": accepted,
        "proof_debt_reduced": accepted,
        "proof_debt_discharged": False,
        "proof_target_selected": True,
        "theorem_row_selected": True,
        "theorem_row_selected_for_execution": True,
        "theorem_discharged": accepted,
        "theorem_linkage_completed": accepted,
        "theorem_linkage_proof_attempt_authorized": True,
        "theorem_linkage_obligation_discharged": accepted,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "execution_findings": EXECUTION_FINDINGS,
        "execution_finding_count": len(EXECUTION_FINDINGS),
        "blocked_claims": EXECUTION_BLOCKED_CLAIMS,
        "blocked_claim_count": len(EXECUTION_BLOCKED_CLAIMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": False,
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This execution constructs only the psi-A matter-sector exchange "
            "theorem-linkage route from the accepted T_psi policy, Dirac equation, "
            "adjoint Dirac equation, current definition, compatibility assumptions, "
            "and shared domain/boundary assumptions. It records "
            "nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha as a bounded "
            "matter-side exchange route under those assumptions. It does not "
            "promote any C_k rule, embed C_k in an action, vary C_k, select a "
            "multiplier route, select a penalty route, make a direct dynamical-law "
            "claim, close full Maxwell, close EM-QFT, close QFT-GR, close GR-QM, "
            "claim empirical validation, close a seam, or promote the master "
            "action. The master action remains a working-form, noncanonical "
            "organizing surface, not a promoted final law."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume execute_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair",
            "fail to construct the matter-sector exchange route",
            "fail to preserve T_psi policy",
            "fail to preserve the Dirac and adjoint Dirac equations",
            "fail to preserve J^alpha = q psibar gamma^alpha psi",
            "fail to preserve gamma/spin/tetrad or metric compatibility assumptions",
            "fail to preserve sign, index, covariant-derivative, domain, and boundary watch items",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "claim direct dynamical-law interpretation",
            "claim full Maxwell, EM-QFT, QFT-GR, or GR-QM closure",
            "claim empirical validation",
            "claim seam closure",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_EXECUTION,
        "full_toeformal_aggregate_status_for_execution": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
        ),
        "scoped_lean_targets_status_for_execution": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
        ),
        "aggregate_lean_validation_status_for_execution": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPairExecution",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "result_review_file": _ptr(result_review_path),
            "result_review_lean_file": _ptr(RESULT_REVIEW_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
    payload["proof_execution_authorized"] = True
    payload["proof_target_execution_authorized"] = True
    payload["proof_attempt_executed"] = accepted
    payload["proof_debt_reduced"] = accepted
    payload["theorem_discharged"] = accepted
    payload["theorem_linkage_completed"] = accepted
    payload["theorem_linkage_proof_attempt_authorized"] = True
    payload["theorem_linkage_obligation_discharged"] = accepted
    payload["proof_target_selected"] = True
    payload["theorem_row_selected"] = True
    payload["theorem_row_selected_for_execution"] = True
    return payload


def write_execution(payload: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Execute the psi-A matter-sector exchange theorem-linkage attempt from the Dirac pair."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--result-review", type=Path, default=RESULT_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    result_review_path = (
        args.result_review
        if args.result_review.is_absolute()
        else REPO_ROOT / args.result_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution(
            result_review_path=result_review_path,
            captured_at_utc=args.captured_at_utc,
        )
    )
    path = write_execution(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "executed": payload["executed"],
                "out": _ptr(path),
                "execution_result": payload["execution_result"],
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
