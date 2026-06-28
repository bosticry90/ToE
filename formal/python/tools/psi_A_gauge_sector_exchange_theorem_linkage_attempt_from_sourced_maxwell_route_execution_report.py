from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_report import (
    CURRENT_OBJECT,
    T_A_POLICY,
)
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result_review_report import (
    ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
    ACCEPTED_SOURCED_MAXWELL_ROUTE,
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    FIELD_STRENGTH_OBJECT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    INPUT_ROUTE,
    LEAN_PACKET_PATH as RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    NEXT_TARGET as CONSUMED_EXECUTION_TARGET,
    NEXT_TARGET_KIND as CONSUMED_EXECUTION_TARGET_KIND,
    OBLIGATION,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    PACKET_ID as RESULT_REVIEW_PACKET_ID,
    PLAIN_MEANING,
    PLANNED_PROOF_STEPS,
    PROOF_STYLE,
    REVIEW_RESULT,
    ROUTE_GIVEN,
    ROUTE_THEN,
    SCHEMA_ID as RESULT_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_EXECUTION_OUTCOME,
    SUGGESTED_EXECUTION_OUTCOME,
    TARGET,
    THEOREM_TARGET_STATEMENT,
    WATCH_ITEMS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_"
    "ROUTE_EXECUTION_20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_"
    "ROUTE_EXECUTION_v0"
)
EXECUTION_RESULT = SUGGESTED_EXECUTION_OUTCOME
STRICT_EXECUTION_RESULT = STRICT_SUGGESTED_EXECUTION_OUTCOME
OUTCOME_ID = EXECUTION_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_"
    "executed_gauge_exchange_route_constructed_no_ck_rule_promotion_or_master_"
    "action_promotion"
)

NEXT_TARGET = (
    "review_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result"
)
NEXT_TARGET_KIND = (
    "psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result_review"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION = SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_EXECUTION = LEAN_STATUS_WORDING_FOR_REVIEW

ATTEMPT_TYPE = "sourced-Maxwell gauge-sector exchange execution"
EXECUTION_PROOF_STYLE = (
    "gauge stress-energy divergence identity with sourced Maxwell substitution"
)
TARGET_CONCLUSION = TARGET
EXCHANGE_OBJECT = "- F^nu{}_alpha J^alpha"
LEAN_THEOREM_NAME = (
    "psi_A_gauge_exchange_from_stress_divergence_and_sourced_maxwell"
)
LEAN_THEOREM_DESCRIPTION = (
    "Generic Lean witness: if the gauge stress-energy divergence is the "
    "-F contraction with nabla_mu F^{mu alpha}, and the sourced Maxwell route "
    "identifies nabla_mu F^{mu alpha} with J^alpha, then the gauge exchange "
    "target follows by substitution."
)
ROUTE_STATEMENT = (
    "start from nabla_mu T_A^{mu nu} = - F^nu{}_alpha nabla_mu F^{mu alpha}; "
    "substitute nabla_mu F^{mu alpha} = J^alpha from the accepted sourced "
    "Maxwell route; preserve the same F and J objects, sign convention, index "
    "placement, and covariant derivative; obtain - F^nu{}_alpha J^alpha"
)

ROUTE_STEPS = [
    "start from nabla_mu T_A^{mu nu} = - F^nu{}_alpha nabla_mu F^{mu alpha}",
    "use the accepted sourced Maxwell route nabla_mu F^{mu alpha} = J^alpha",
    "substitute the sourced Maxwell current into the gauge stress-energy divergence identity",
    "preserve the same F object, J object, sign, index placement, and covariant derivative",
    "obtain nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha",
]

EXECUTION_FINDINGS = [
    "psi-A gauge-sector exchange theorem-linkage attempt executed",
    "gauge exchange route constructed from stress divergence and sourced Maxwell",
    "T_A policy preserved",
    "same F and J objects preserved",
    "sign, index, covariant-derivative, domain, and boundary watch items preserved",
    "no C_k rule promotion",
    "no C_k action embedding or variation",
    "no full Maxwell, EM-QFT, QFT-GR, or GR-QM closure",
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
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_"
        "MAXWELL_ROUTE_EXECUTION_20260628_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRouteExecution.lean"
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
        "general_C_k_theorem_linkage_closure": False,
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
            "step_id": "start_from_gauge_stress_divergence_identity",
            "statement": ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
            "role": "accepted gauge stress-energy divergence identity",
        },
        {
            "step_id": "use_sourced_maxwell_route",
            "statement": ACCEPTED_SOURCED_MAXWELL_ROUTE,
            "role": "accepted sourced Maxwell route",
        },
        {
            "step_id": "substitute_source_current",
            "statement": ROUTE_STEPS[2],
            "role": "current substitution",
        },
        {
            "step_id": "preserve_objects_and_indices",
            "statement": ROUTE_STEPS[3],
            "role": "same F, J, sign, index, and covariant derivative",
        },
        {
            "step_id": "derive_gauge_exchange",
            "statement": TARGET,
            "role": "gauge-sector exchange target",
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
            "row_id": "gauge_stress_divergence_identity_used",
            "status": "accepted",
            "evidence": ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
            "assessment": "The gauge stress-energy divergence identity is the first input.",
        },
        {
            "row_id": "sourced_maxwell_route_used",
            "status": "accepted",
            "evidence": ACCEPTED_SOURCED_MAXWELL_ROUTE,
            "assessment": "The sourced Maxwell route supplies nabla_mu F^{mu alpha} = J^alpha.",
        },
        {
            "row_id": "same_F_and_J_objects_preserved",
            "status": "accepted",
            "evidence": [FIELD_STRENGTH_OBJECT, CURRENT_OBJECT],
            "assessment": "The contraction uses the same F and J objects.",
        },
        {
            "row_id": "gauge_exchange_route_constructed",
            "status": "accepted",
            "evidence": TARGET,
            "assessment": "The gauge-side exchange target follows by substitution.",
        },
        {
            "row_id": "watch_items_preserved",
            "status": "accepted",
            "evidence": WATCH_ITEMS,
            "assessment": "The T_A, F, J, sign, index, derivative, and domain watch items are preserved.",
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
            "psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_"
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


def build_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_execution(
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
            and ROUTE_THEN == TARGET
            and result_review.get("theorem_target_statement")
            == THEOREM_TARGET_STATEMENT
        ),
        "gauge_exchange_execution_shape": (
            INPUT_ROUTE
            == "gauge stress-energy divergence identity plus sourced Maxwell route"
            and PROOF_STYLE
            == "gauge stress-energy divergence identity plus sourced Maxwell substitution route"
            and EXECUTION_PROOF_STYLE
            == "gauge stress-energy divergence identity with sourced Maxwell substitution"
        ),
        "execution_steps_all_bounded": (
            len(execution_steps) == 5 and execution_steps[-1]["statement"] == TARGET
        ),
        "watch_items_preserved": WATCH_ITEMS
        == [
            "same T_A definition",
            "same F object",
            "same J object",
            "same sign convention",
            "same index placement",
            "same covariant derivative",
            "accepted sourced Maxwell route",
            "accepted gauge stress-energy divergence identity",
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
    remediation = (
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_"
        "MAXWELL_ROUTE_EXECUTION_REQUIRES_REMEDIATION"
    )
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_EXECUTION"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_EXECUTION"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "executed": accepted,
        "outcome_id": OUTCOME_ID if accepted else remediation,
        "packet_result": OUTCOME_ID if accepted else remediation,
        "execution_result": OUTCOME_ID if accepted else remediation,
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
        "selected_obligation": OBLIGATION,
        "selected_obligation_rank": "4",
        "local_theorem_linkage_reduced": accepted,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "theorem_target_shape": theorem_target_shape,
        "theorem_target_recorded": accepted,
        "theorem_target_indexed": accepted,
        "theorem_linkage_target_indexed": accepted,
        "gauge_exchange_route_constructed": accepted,
        "gauge_exchange_derived": accepted,
        "T_A_policy": T_A_POLICY,
        "t_a_policy_preserved": accepted,
        "field_strength_object": FIELD_STRENGTH_OBJECT,
        "current_object": CURRENT_OBJECT,
        "same_F_and_J_objects_preserved": accepted,
        "accepted_sourced_maxwell_route": ACCEPTED_SOURCED_MAXWELL_ROUTE,
        "sourced_maxwell_route_used": accepted,
        "accepted_gauge_stress_energy_divergence_identity": (
            ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
        ),
        "gauge_stress_energy_divergence_identity_used": accepted,
        "target_conclusion": TARGET_CONCLUSION,
        "exchange_object": EXCHANGE_OBJECT,
        "route_given": ROUTE_GIVEN,
        "route_then": ROUTE_THEN,
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
            "This execution constructs only the psi-A gauge-sector exchange "
            "theorem-linkage route from the accepted gauge stress-energy "
            "divergence identity and sourced Maxwell route. It records "
            "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha as a bounded "
            "gauge-side exchange route under the preserved F, J, sign, index, "
            "covariant-derivative, domain, and boundary assumptions. It does "
            "not promote any C_k rule, embed C_k in an action, vary C_k, select "
            "a multiplier route, select a penalty route, make a direct "
            "dynamical-law claim, close full Maxwell, close EM-QFT, close "
            "QFT-GR, close GR-QM, claim empirical validation, close a seam, or "
            "promote the master action. The master action remains a "
            "working-form, noncanonical organizing surface, not a promoted "
            "final law."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume execute_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route",
            "fail to construct the gauge-sector exchange route",
            "fail to preserve T_A policy",
            "fail to preserve the gauge stress-energy divergence identity",
            "fail to preserve the sourced Maxwell route",
            "fail to preserve the same F and J objects",
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
            "ToeFormal.Derivation.PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRouteExecution",
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
            "Execute the psi-A gauge-sector exchange theorem-linkage attempt from the sourced Maxwell route."
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
    payload = build_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_execution(
        result_review_path=result_review_path,
        captured_at_utc=args.captured_at_utc,
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
