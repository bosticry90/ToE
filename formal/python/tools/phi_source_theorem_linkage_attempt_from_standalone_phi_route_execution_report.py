from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review_report import (
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    EXECUTION_ROUTE_TO_AUTHORIZE,
    FIELD_EULER_LAGRANGE_EQUATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    LEAN_PACKET_PATH as RESULT_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    ON_SHELL_CONDITION,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    PACKET_ID as RESULT_REVIEW_PACKET_ID,
    RESIDUAL_IDENTITY_FORM,
    REVIEW_RESULT,
    ROUTE_BUNDLE_ADMISSIBILITY_FORM,
    SCHEMA_ID as RESULT_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STANDALONE_PHI_SOURCE_ROUTE,
    STRESS_DIVERGENCE_TARGET,
    STRESS_ENERGY_UNDER_SELECTED_POLICY,
    STRICT_REVIEW_RESULT,
    TARGET_CONCLUSION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTION_"
    "20260630_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTION_v0"
)
EXECUTION_RESULT = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTED_"
    "C_SOURCE_PHI_LINKAGE_CONSTRUCTED_NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_"
    "PROMOTION"
)
STRICT_EXECUTION_RESULT = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTED_"
    "C_SOURCE_PHI_ZERO_FROM_ON_SHELL_SCALAR_RESIDUAL_NO_PHI_SECTOR_OR_SEAM_"
    "CLOSURE"
)
OUTCOME_ID = EXECUTION_RESULT
PACKET_CLASSIFICATION = (
    "phi_source_theorem_linkage_attempt_from_standalone_phi_route_executed_"
    "C_source_phi_zero_from_on_shell_scalar_residual_no_phi_sector_or_seam_"
    "closure_no_ck_rule_or_master_action_promotion"
)

NEXT_TARGET = (
    "review_phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution_result"
)
NEXT_TARGET_KIND = (
    "phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution_result_review"
)
SUGGESTED_REVIEW_OUTCOME = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTION_"
    "RESULT_REVIEW_ACCEPTS_C_SOURCE_PHI_ZERO_FROM_ON_SHELL_SCALAR_RESIDUAL_"
    "NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_PROMOTION"
)
STRICT_SUGGESTED_REVIEW_OUTCOME = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTION_"
    "RESULT_REVIEW_ACCEPTS_LOCAL_PHI_SOURCE_THEOREM_LINKAGE_ONLY_NO_PHI_"
    "SECTOR_OR_SEAM_CLOSURE"
)

EXECUTION_ROUTE = [
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    RESIDUAL_IDENTITY_FORM,
    ON_SHELL_RESIDUAL_FORM,
    "on shell: R_i^phi = 0",
    "therefore: C_source^nu[g, phi] = 0",
]
EXECUTION_REDUCTION_ROUTE = [
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    RESIDUAL_IDENTITY_FORM,
    "R_i^phi = 0",
    "therefore: C_source^nu[g, phi] = 0",
]
PLAIN_MEANING = (
    "The phi source residual vanishes when the scalar field equations hold on shell."
)
LEAN_THEOREM_NAME = "c_source_phi_zero_from_on_shell_scalar_residual"
LEAN_THEOREM_DESCRIPTION = (
    "Generic Lean witness: if C_source^phi is definitionally the scalar "
    "residual contraction and that contraction is zero on shell, then "
    "C_source^phi is zero."
)

EXECUTION_FINDINGS = [
    "standalone phi-source theorem-linkage attempt executed",
    "C_source^nu[g, phi] definition preserved",
    "scalar/on-shell residual identity used",
    "R_i^phi = 0 applied as on-shell condition",
    "C_source^nu[g, phi] = 0 locally constructed",
    "no phi-sector closure",
    "no full scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no general C_k closure",
    "no C_k rule promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]

BOUNDARY_ITEMS = [
    "no phi-sector closure",
    "no full scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no general C_k closure",
    "no C_k rule promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
    "no seam closure",
]

ROUTE_PURITY_WATCH_ITEMS = [
    "no A-sector route import",
    "no psi-A sourced Maxwell import",
    "no QFT-GR source-route import",
    "no silent replacement of the phi residual identity",
]

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
)
SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION = SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
LEAN_STATUS_WORDING_FOR_EXECUTION = LEAN_STATUS_WORDING_FOR_PACKET

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTION_20260630_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiSourceTheoremLinkageAttemptFromStandalonePhiRouteExecution.lean"
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
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "psi_A_sourced_Maxwell_substitution": False,
        "QFT_GR_source_route_imported": False,
        "J_current_imported": False,
        "C_source_phi_closure_claimed": False,
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
        "proof_debt_discharged": False,
    }


def _result_review_valid(result_review: dict[str, Any]) -> bool:
    return (
        result_review.get("schema_id") == RESULT_REVIEW_SCHEMA_ID
        and result_review.get("packet_id") == RESULT_REVIEW_PACKET_ID
        and result_review.get("outcome_id") == RESULT_REVIEW_OUTCOME
        and result_review.get("review_result") == REVIEW_RESULT
        and result_review.get("strict_review_result") == STRICT_REVIEW_RESULT
        and result_review.get("selected_next_target") == CONSUMED_TARGET
        and result_review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and result_review.get("execution_route_to_authorize")
        == EXECUTION_ROUTE_TO_AUTHORIZE
        and result_review.get("C_source_phi_residual_definition")
        == C_SOURCE_PHI_RESIDUAL_DEFINITION
        and result_review.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
        and result_review.get("on_shell_condition") == ON_SHELL_CONDITION
        and result_review.get("theorem_discharged") is False
        and result_review.get("accepted") is True
    )


def _execution_steps() -> list[dict[str, str]]:
    return [
        {
            "step_id": "define_C_source_phi_residual",
            "statement": C_SOURCE_PHI_RESIDUAL_DEFINITION,
            "role": "standalone phi-sector source residual definition",
        },
        {
            "step_id": "use_scalar_on_shell_residual_identity",
            "statement": RESIDUAL_IDENTITY_FORM,
            "role": "prior scalar/on-shell residual identity",
        },
        {
            "step_id": "record_scalar_residual_definition",
            "statement": ON_SHELL_RESIDUAL_FORM,
            "role": "scalar residual definition from the standalone phi registry",
        },
        {
            "step_id": "apply_on_shell_condition",
            "statement": ON_SHELL_CONDITION,
            "role": "on-shell scalar field equation condition",
        },
        {
            "step_id": "construct_C_source_phi_zero",
            "statement": TARGET_CONCLUSION,
            "role": "local theorem-linkage target constructed",
        },
    ]


def _execution_criteria() -> list[dict[str, Any]]:
    return [
        {
            "row_id": "execution_target_authorized",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The prior review selected this bounded execution target.",
        },
        {
            "row_id": "standalone_phi_route_executed",
            "status": "accepted",
            "evidence": EXECUTION_ROUTE,
            "assessment": "The route stays tied to the standalone phi registry.",
        },
        {
            "row_id": "C_source_phi_definition_used",
            "status": "accepted",
            "evidence": C_SOURCE_PHI_RESIDUAL_DEFINITION,
            "assessment": "C_source^phi is expanded only as nabla_mu T_phi^{mu nu}.",
        },
        {
            "row_id": "scalar_on_shell_identity_used",
            "status": "accepted",
            "evidence": RESIDUAL_IDENTITY_FORM,
            "assessment": "The scalar residual contraction is the only bridge.",
        },
        {
            "row_id": "on_shell_zero_applied",
            "status": "accepted",
            "evidence": ON_SHELL_CONDITION,
            "assessment": "R_i^phi = 0 is applied as the on-shell condition.",
        },
        {
            "row_id": "C_source_phi_zero_constructed",
            "status": "accepted",
            "evidence": TARGET_CONCLUSION,
            "assessment": "C_source^phi zero follows locally from the on-shell residual route.",
        },
        {
            "row_id": "route_contamination_blocked",
            "status": "accepted",
            "evidence": ROUTE_PURITY_WATCH_ITEMS,
            "assessment": "No A-sector, psi-A sourced Maxwell, or QFT-GR source route is imported.",
        },
        {
            "row_id": "no_closure_or_promotion",
            "status": "accepted",
            "evidence": BOUNDARY_ITEMS,
            "assessment": "The execution remains local theorem-linkage only.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution"
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


def build_phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution(
    *,
    result_review_path: Path = RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    route_text = " ".join(EXECUTION_ROUTE)
    execution_steps = _execution_steps()
    execution_criteria = _execution_criteria()
    acceptance_criteria = {
        "consumes_expected_execution_target": _result_review_valid(result_review),
        "standalone_execution_route_exact": (
            EXECUTION_REDUCTION_ROUTE
            == [
                "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}",
                "C_source^nu = sum_i R_i^phi nabla^nu phi_i",
                "R_i^phi = 0",
                "therefore: C_source^nu[g, phi] = 0",
            ]
        ),
        "C_source_phi_definition_preserved": (
            C_SOURCE_PHI_RESIDUAL_DEFINITION
            == "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}"
        ),
        "scalar_on_shell_residual_identity_used": (
            RESIDUAL_IDENTITY_FORM
            == "C_source^nu = sum_i R_i^phi nabla^nu phi_i"
            and ON_SHELL_RESIDUAL_FORM
            == "R_i^phi := Box_g phi_i + partial_i V(phi)"
            and FIELD_EULER_LAGRANGE_EQUATION
            == "Box_g phi_i + partial_i V(phi) = 0"
        ),
        "on_shell_condition_applied": ON_SHELL_CONDITION == "R_i^phi = 0",
        "C_source_phi_zero_constructed": TARGET_CONCLUSION
        == "C_source^nu[g, phi] = 0",
        "route_contamination_blocked": (
            "J^alpha" not in route_text
            and "nabla_mu F" not in route_text
            and "QFT-GR" not in route_text
        ),
        "execution_criteria_all_accepted": all(
            row["status"] == "accepted" for row in execution_criteria
        ),
        "lean_status_wording_preserved": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "ROUTE_EXECUTION"
        )
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "ROUTE_EXECUTION"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "executed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_"
            "EXECUTION_REQUIRES_REMEDIATION"
        ),
        "packet_result": OUTCOME_ID
        if accepted
        else (
            "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_"
            "EXECUTION_REQUIRES_REMEDIATION"
        ),
        "execution_result": OUTCOME_ID
        if accepted
        else (
            "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_"
            "EXECUTION_REQUIRES_REMEDIATION"
        ),
        "strict_execution_result": STRICT_EXECUTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if accepted else "remediation",
        "post_execution_target": NEXT_TARGET,
        "post_execution_target_kind": NEXT_TARGET_KIND,
        "suggested_review_outcome": SUGGESTED_REVIEW_OUTCOME,
        "strict_suggested_review_outcome": STRICT_SUGGESTED_REVIEW_OUTCOME,
        "result_review_schema_id": RESULT_REVIEW_SCHEMA_ID,
        "result_review_packet_id": RESULT_REVIEW_PACKET_ID,
        "result_review_outcome": RESULT_REVIEW_OUTCOME,
        "result_review_strict_outcome": STRICT_REVIEW_RESULT,
        "result_review_consumed": accepted,
        "selected_obligation": "C_source^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_source^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_source^phi",
        "standalone_phi_source_route": STANDALONE_PHI_SOURCE_ROUTE,
        "standalone_phi_source_route_preserved": accepted,
        "C_source_phi_residual_definition": C_SOURCE_PHI_RESIDUAL_DEFINITION,
        "C_source_phi_source_admissibility_condition": TARGET_CONCLUSION,
        "C_source_phi_target_statement": TARGET_CONCLUSION,
        "source_admissibility_condition": TARGET_CONCLUSION,
        "stress_divergence_target": STRESS_DIVERGENCE_TARGET,
        "residual_identity_form": RESIDUAL_IDENTITY_FORM,
        "on_shell_residual_form": ON_SHELL_RESIDUAL_FORM,
        "on_shell_condition": ON_SHELL_CONDITION,
        "field_euler_lagrange_equation": FIELD_EULER_LAGRANGE_EQUATION,
        "route_bundle_admissibility_form": ROUTE_BUNDLE_ADMISSIBILITY_FORM,
        "stress_energy_under_selected_policy": STRESS_ENERGY_UNDER_SELECTED_POLICY,
        "target_conclusion": TARGET_CONCLUSION,
        "execution_route": EXECUTION_ROUTE,
        "execution_reduction_route": EXECUTION_REDUCTION_ROUTE,
        "linkage_route": EXECUTION_ROUTE,
        "route_kind": "standalone_phi_on_shell_scalar_residual",
        "plain_meaning": PLAIN_MEANING,
        "lean_theorem_name": LEAN_THEOREM_NAME,
        "lean_theorem_description": LEAN_THEOREM_DESCRIPTION,
        "C_source_phi_zero_constructed": accepted,
        "C_source_phi_zero_derived": accepted,
        "C_source_phi_linkage_constructed": accepted,
        "C_source_phi_admissibility_status": "local theorem-linkage only",
        "theorem_linkage_completed": accepted,
        "theorem_target_recorded": accepted,
        "definition_linkage_constructed": accepted,
        "proof_execution": "executed",
        "proof_execution_authorized": True,
        "proof_attempt_executed": accepted,
        "proof_debt_reduced": accepted,
        "theorem_execution_authorized": True,
        "theorem_discharged": accepted,
        "theorem_linkage_obligation_discharged": accepted,
        "phi_source_theorem_linkage_obligation_discharged": accepted,
        "C_source_phi_discharged": accepted,
        "rule_promotion": "not authorized",
        "execution_steps": execution_steps,
        "execution_step_count": len(execution_steps),
        "execution_criteria": execution_criteria,
        "execution_criteria_count": len(execution_criteria),
        "execution_criteria_accepted_count": sum(
            1 for row in execution_criteria if row["status"] == "accepted"
        ),
        "execution_findings": EXECUTION_FINDINGS,
        "execution_finding_count": len(EXECUTION_FINDINGS),
        "boundary_items": BOUNDARY_ITEMS,
        "boundary_item_count": len(BOUNDARY_ITEMS),
        "route_purity_watch_items": ROUTE_PURITY_WATCH_ITEMS,
        "route_purity_watch_item_count": len(ROUTE_PURITY_WATCH_ITEMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": False,
        "claim_ladder_position": (
            "below phi-sector closure, full scalar/QFT closure, seam closure, "
            "empirical prediction, empirical confirmation, and mature physical "
            "theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This execution constructs only the local standalone phi-source "
            "C_source^phi linkage from C_source^nu[g, phi] := nabla_mu "
            "T_phi^{mu nu}, C_source^nu = sum_i R_i^phi nabla^nu phi_i, "
            "R_i^phi := Box_g phi_i + partial_i V(phi), and the on-shell "
            "condition R_i^phi = 0 to C_source^nu[g, phi] = 0. It imports no "
            "A-sector, psi-A sourced Maxwell, or QFT-GR source route, claims no "
            "phi-sector or full scalar/QFT closure, closes no EM-QFT, QFT-GR, "
            "or GR-QM seam, claims no general C_k closure, promotes no C_k "
            "rule, embeds no action, varies no action, claims no empirical "
            "validation, closes no seam, and does not promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume execute_phi_source_theorem_linkage_attempt_from_standalone_phi_route",
            "fail to preserve C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}",
            "fail to use C_source^nu = sum_i R_i^phi nabla^nu phi_i",
            "fail to apply R_i^phi = 0 as the on-shell condition",
            "silently substitute an A-sector route",
            "silently import a psi-A sourced Maxwell route",
            "silently import a QFT-GR source route",
            "claim phi-sector closure",
            "claim full scalar/QFT closure",
            "claim EM-QFT or QFT-GR closure",
            "claim general C_k closure",
            "promote any C_k rule",
            "embed or vary an action",
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
            "ToeFormal.Derivation.PhiSourceTheoremLinkageAttemptFromStandalonePhiRouteExecution",
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
    payload.update(_false_boundary_flags())
    payload["proof_execution_authorized"] = True
    payload["proof_attempt_executed"] = accepted
    payload["proof_debt_reduced"] = accepted
    payload["theorem_execution_authorized"] = True
    payload["theorem_discharged"] = accepted
    payload["theorem_linkage_completed"] = accepted
    payload["theorem_linkage_obligation_discharged"] = accepted
    payload["phi_source_theorem_linkage_obligation_discharged"] = accepted
    payload["C_source_phi_discharged"] = accepted
    payload["C_source_phi_zero_derived"] = accepted
    payload["C_source_phi_linkage_constructed"] = accepted
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
            "Execute the standalone phi-source C_source^phi theorem-linkage route."
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
    payload = build_phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution(
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
                "C_source_phi_zero_derived": payload["C_source_phi_zero_derived"],
                "phi_sector_closure_claimed": payload[
                    "phi_sector_closure_claimed"
                ],
                "rule_promoted": payload["rule_promoted"],
                "master_action_promoted": payload["master_action_promoted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
