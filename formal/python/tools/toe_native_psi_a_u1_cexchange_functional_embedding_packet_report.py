from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_cexchange_constraint_candidate_packet_result_review_report import (
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as CANDIDATE_REVIEW_PATH,
    EXCHANGE_TERM_CANCELLATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAUGE_SECTOR_EXCHANGE_TERM,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MATTER_SECTOR_EXCHANGE_TERM,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as CANDIDATE_REVIEW_OUTCOME,
    PACKET_CLASSIFICATION as CANDIDATE_REVIEW_CLASSIFICATION,
    PACKET_ID as CANDIDATE_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT as CANDIDATE_REVIEW_RESULT,
    SCHEMA_ID as CANDIDATE_REVIEW_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TARGETED_LEAN_BUILD_STATUS,
    TOTAL_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-25T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_20260625_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_v0"
PACKET_RESULT = "OPTIONS_RECORDED_ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
OUTCOME_ID = (
    "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_PREPARED_"
    + PACKET_RESULT
)
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_cexchange_functional_embedding_packet_prepared_"
    "options_recorded_admissibility_only_route_selected_no_action_variation"
)
NEXT_TARGET = "review_toe_native_psi_A_u1_cexchange_functional_embedding_packet_result"
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_cexchange_functional_embedding_packet_result_review"
)

ADMISSIBILITY_ONLY_ROUTE_ID = "psi_A_u1_cexchange_admissibility_only_route"
ADMISSIBILITY_CONSTRAINT_FORM = C_EXCHANGE_ADMISSIBILITY_CONDITION
ADMISSIBILITY_ONLY_ROUTE_STATUS = (
    "selected_non_dynamical_interaction_admissibility_rule"
)

MULTIPLIER_ACTION_ROUTE_ID = "psi_A_u1_cexchange_multiplier_action_route"
MULTIPLIER_ACTION_FORM = (
    "S_Cexchange = int d^4x sqrt(-g) lambda_nu C_exchange^{Apsi,nu}"
)
MULTIPLIER_ROUTE_STATUS = (
    "blocked_by_multiplier_type_index_units_boundary_variation_"
    "higher_derivative_circularity_and_stability_requirements"
)
MULTIPLIER_BLOCKING_REASONS = [
    "multiplier field type not selected",
    "index placement not selected",
    "units not fixed",
    "boundary terms not controlled",
    "metric/tetrad variation behavior not analyzed",
    "higher-derivative risk not resolved",
    "circularity control not established",
    "stability analysis not completed",
]

PENALTY_ROUTE_ID = "psi_A_u1_cexchange_quadratic_penalty_route"
PENALTY_ACTION_FORM = (
    "S_Cexchange_penalty = int d^4x sqrt(-g) C_exchange_nu C_exchange^nu"
)
PENALTY_ROUTE_STATUS = "recorded_unlicensed_dynamical_penalty"
PENALTY_BLOCKING_REASONS = [
    "could introduce new dynamics",
    "stability problems not analyzed",
    "unit/sign issues not resolved",
]

ALLOWED_CLAIMS = [
    "functional-embedding options recorded",
    "admissibility-only route selected",
    "multiplier/action route recorded as blocked",
    "penalty route recorded as unlicensed",
    "direct dynamical-law interpretation blocked",
    "no action variation executed",
]

BLOCKED_CLAIMS = [
    "no C_exchange closeout",
    "no multiplier/action route",
    "no penalty route",
    "no C_k action variation",
    "no direct dynamical-law interpretation",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no quantized electromagnetism",
    "no anomaly analysis",
    "no Standard Model derivation",
    "no Phase 2 authorization",
    "no empirical validation",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_20260625_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1CExchangeFunctionalEmbeddingPacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _embedding_routes() -> list[dict[str, Any]]:
    return [
        {
            "route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
            "route_type": "admissibility_only_rule",
            "status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
            "constraint_form": ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": (
                "The psi-A interaction route is accepted only if the total "
                "matter-plus-gauge energy-momentum exchange balances."
            ),
            "action_term_selected": False,
            "action_variation_executed": False,
            "selected_for_current_packet": True,
        },
        {
            "route_id": MULTIPLIER_ACTION_ROUTE_ID,
            "route_type": "multiplier_action_embedding",
            "status": MULTIPLIER_ROUTE_STATUS,
            "action_form": MULTIPLIER_ACTION_FORM,
            "blocking_reasons": MULTIPLIER_BLOCKING_REASONS,
            "action_term_selected": False,
            "action_variation_executed": False,
            "selected_for_current_packet": False,
        },
        {
            "route_id": PENALTY_ROUTE_ID,
            "route_type": "quadratic_penalty_action_embedding",
            "status": PENALTY_ROUTE_STATUS,
            "action_form": PENALTY_ACTION_FORM,
            "blocking_reasons": PENALTY_BLOCKING_REASONS,
            "action_term_selected": False,
            "action_variation_executed": False,
            "selected_for_current_packet": False,
        },
    ]


def _review_rows(candidate_review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_expected_functional_embedding_target",
            "status": "accepted",
            "evidence": candidate_review.get("selected_next_target"),
            "assessment": "The accepted C_exchange candidate review authorized this functional-embedding packet.",
        },
        {
            "row_id": "cexchange_candidate_carried_forward",
            "status": "accepted",
            "evidence": [
                C_EXCHANGE_CONSTRAINT_FORM,
                C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
                C_EXCHANGE_ADMISSIBILITY_CONDITION,
            ],
            "assessment": "The interaction exchange-conservation residual candidate is carried forward exactly.",
        },
        {
            "row_id": "total_exchange_route_context_carried_forward",
            "status": "accepted",
            "evidence": [
                GAUGE_SECTOR_EXCHANGE_IDENTITY,
                MATTER_SECTOR_EXCHANGE_IDENTITY,
                EXCHANGE_TERM_CANCELLATION,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            ],
            "assessment": "The accepted gauge-side, matter-side, and total-conservation context is preserved.",
        },
        {
            "row_id": "three_embedding_routes_recorded",
            "status": "accepted",
            "evidence": [
                ADMISSIBILITY_ONLY_ROUTE_ID,
                MULTIPLIER_ACTION_ROUTE_ID,
                PENALTY_ROUTE_ID,
            ],
            "assessment": "Admissibility-only, multiplier/action, and penalty routes are recorded.",
        },
        {
            "row_id": "admissibility_only_route_selected",
            "status": "accepted",
            "evidence": ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "Only the non-dynamical admissibility route is selected.",
        },
        {
            "row_id": "multiplier_action_route_blocked",
            "status": "accepted",
            "evidence": [MULTIPLIER_ACTION_FORM, MULTIPLIER_BLOCKING_REASONS],
            "assessment": "The multiplier/action route is blocked by unresolved multiplier, index, unit, boundary, variation, higher-derivative, circularity, and stability requirements.",
        },
        {
            "row_id": "penalty_route_unlicensed",
            "status": "accepted",
            "evidence": [PENALTY_ACTION_FORM, PENALTY_BLOCKING_REASONS],
            "assessment": "The quadratic penalty route is recorded but unlicensed because it could add dynamics with unresolved stability and unit/sign behavior.",
        },
        {
            "row_id": "direct_dynamical_law_interpretation_blocked",
            "status": "accepted",
            "evidence": [
                "direct_force_law_claimed=false",
                "varied_dynamical_equation_claimed=false",
            ],
            "assessment": "C_exchange remains an admissibility rule, not a new force law or varied dynamical equation.",
        },
        {
            "row_id": "no_action_embedding_or_variation_executed",
            "status": "accepted",
            "evidence": [
                "action_embedding_claimed=false",
                "C_k_action_variation_executed=false",
                "candidate_varied=false",
            ],
            "assessment": "No action embedding, C_k variation, or candidate variation is executed.",
        },
        {
            "row_id": "no_closure_phase2_empirical_or_promotion_claim",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Maxwell, EM-QFT, QFT-GR, quantization, anomaly, Standard Model, Phase 2, empirical, and master-action claims remain blocked.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_psi_A_u1_cexchange_functional_embedding_packet"
        ),
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "targeted_lean_build_status_for_packet": TARGETED_LEAN_BUILD_STATUS,
        "targeted_lean_builds_passed": True,
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "aggregate_lean_validation_status_allowed_values": ["NOT_RUN"],
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_toe_native_psi_a_u1_cexchange_functional_embedding_packet(
    *,
    candidate_review_path: Path = CANDIDATE_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    candidate_review = _read_json(candidate_review_path)
    routes = _embedding_routes()
    review_rows = _review_rows(candidate_review)
    acceptance_criteria = {
        "consumes_expected_target": (
            candidate_review.get("schema_id") == CANDIDATE_REVIEW_SCHEMA_ID
            and candidate_review.get("packet_id") == CANDIDATE_REVIEW_PACKET_ID
            and candidate_review.get("outcome_id") == CANDIDATE_REVIEW_OUTCOME
            and candidate_review.get("review_result") == CANDIDATE_REVIEW_RESULT
            and candidate_review.get("selected_next_target") == CONSUMED_TARGET
            and candidate_review.get("accepted") is True
        ),
        "candidate_shape_carried_forward": (
            candidate_review.get("C_exchange_constraint_id")
            == C_EXCHANGE_CONSTRAINT_ID
            and candidate_review.get("C_exchange_constraint_form")
            == C_EXCHANGE_CONSTRAINT_FORM
            and candidate_review.get("C_exchange_total_stress_energy_form")
            == C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
            and candidate_review.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "exchange_context_preserved": (
            candidate_review.get("gauge_sector_exchange_identity")
            == GAUGE_SECTOR_EXCHANGE_IDENTITY
            and candidate_review.get("matter_sector_exchange_identity")
            == MATTER_SECTOR_EXCHANGE_IDENTITY
            and candidate_review.get("exchange_term_cancellation")
            == EXCHANGE_TERM_CANCELLATION
            and candidate_review.get("total_stress_energy_conservation_identity")
            == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "three_routes_recorded": len(routes) == 3,
        "admissibility_only_selected": (
            routes[0]["route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
            and routes[0]["selected_for_current_packet"] is True
            and routes[0]["action_term_selected"] is False
        ),
        "action_routes_not_licensed": all(
            route["action_term_selected"] is False
            and route["action_variation_executed"] is False
            for route in routes
        ),
        "multiplier_route_blocked": (
            routes[1]["status"] == MULTIPLIER_ROUTE_STATUS
            and routes[1]["blocking_reasons"] == MULTIPLIER_BLOCKING_REASONS
        ),
        "penalty_route_unlicensed": (
            routes[2]["status"] == PENALTY_ROUTE_STATUS
            and routes[2]["blocking_reasons"] == PENALTY_BLOCKING_REASONS
        ),
        "review_rows_all_accepted": all(
            row["status"] == "accepted" for row in review_rows
        ),
        "blocked_claims_exactly_scoped": len(BLOCKED_CLAIMS) == 14,
        "allowed_claims_exactly_scoped": len(ALLOWED_CLAIMS) == 6,
        "next_review_target_selected": NEXT_TARGET
        == "review_toe_native_psi_A_u1_cexchange_functional_embedding_packet_result",
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "candidate_review_outcome": CANDIDATE_REVIEW_OUTCOME,
        "candidate_review_result": CANDIDATE_REVIEW_RESULT,
        "candidate_review_classification": CANDIDATE_REVIEW_CLASSIFICATION,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "source_current": SOURCE_CURRENT,
        "sourced_gauge_route": SOURCED_GAUGE_ROUTE,
        "gauge_sector_exchange_identity": GAUGE_SECTOR_EXCHANGE_IDENTITY,
        "gauge_sector_exchange_term": GAUGE_SECTOR_EXCHANGE_TERM,
        "matter_sector_exchange_identity": MATTER_SECTOR_EXCHANGE_IDENTITY,
        "matter_sector_exchange_term": MATTER_SECTOR_EXCHANGE_TERM,
        "exchange_term_cancellation": EXCHANGE_TERM_CANCELLATION,
        "total_conservation_identity": TOTAL_CONSERVATION_IDENTITY,
        "total_stress_energy_object": TOTAL_STRESS_ENERGY_OBJECT,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_constraint_id": C_EXCHANGE_CONSTRAINT_ID,
        "C_exchange_constraint_form": C_EXCHANGE_CONSTRAINT_FORM,
        "C_exchange_total_stress_energy_form": C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
        "C_exchange_admissibility_condition": C_EXCHANGE_ADMISSIBILITY_CONDITION,
        "C_exchange_plain_meaning": C_EXCHANGE_PLAIN_MEANING,
        "C_exchange_candidate_scope": C_EXCHANGE_CANDIDATE_SCOPE,
        "embedding_routes": routes,
        "embedding_route_count": len(routes),
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_constraint_form": ADMISSIBILITY_CONSTRAINT_FORM,
        "admissibility_only_route_status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
        "multiplier_action_route_id": MULTIPLIER_ACTION_ROUTE_ID,
        "multiplier_action_form": MULTIPLIER_ACTION_FORM,
        "multiplier_route_status": MULTIPLIER_ROUTE_STATUS,
        "multiplier_blocking_reasons": MULTIPLIER_BLOCKING_REASONS,
        "multiplier_blocking_reason_count": len(MULTIPLIER_BLOCKING_REASONS),
        "penalty_route_id": PENALTY_ROUTE_ID,
        "penalty_action_form": PENALTY_ACTION_FORM,
        "penalty_route_status": PENALTY_ROUTE_STATUS,
        "penalty_blocking_reasons": PENALTY_BLOCKING_REASONS,
        "penalty_blocking_reason_count": len(PENALTY_BLOCKING_REASONS),
        "allowed_claims": ALLOWED_CLAIMS,
        "allowed_claim_count": len(ALLOWED_CLAIMS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "review_rows": review_rows,
        "review_row_count": len(review_rows),
        "review_row_accepted_count": sum(
            1 for row in review_rows if row["status"] == "accepted"
        ),
        "review_criteria": review_rows,
        "review_criteria_count": len(review_rows),
        "review_criteria_accepted_count": sum(
            1 for row in review_rows if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "C_exchange_functional_embedding_packet_prepared": accepted,
        "functional_embedding_packet_prepared": accepted,
        "functional_embedding_options_recorded": accepted,
        "C_exchange_functional_embedding_options_recorded": accepted,
        "admissibility_only_route_selected": accepted,
        "admissibility_only_interpretation_retained": accepted,
        "interaction_admissibility_rule_selected": accepted,
        "constraint_as_admissibility_rule_selected": accepted,
        "candidate_based_on_accepted_total_conservation_route": accepted,
        "C_exchange_candidate_carried_forward": accepted,
        "C_exchange_constraint_candidate_result_review_consumed": accepted,
        "total_exchange_conservation_residual_candidate_consumed": accepted,
        "total_stress_energy_object_preserved": accepted,
        "gauge_matter_exchange_balance_context_preserved": accepted,
        "multiplier_action_route_recorded": accepted,
        "multiplier_action_route_blocked": accepted,
        "penalty_route_recorded": accepted,
        "penalty_route_unlicensed": accepted,
        "direct_dynamical_law_interpretation_blocked": accepted,
        "C_exchange_functional_embedding_packet_result_review_selected": accepted,
        "C_exchange_functional_embedding_packet_result_review_authorized": accepted,
        "C_exchange_closeout": False,
        "C_exchange_definition_closeout": False,
        "C_exchange_rule_family_closed": False,
        "C_exchange_functional_embedding_claimed": False,
        "C_exchange_functional_embedding_selected": False,
        "C_exchange_functional_embedding_constructed": False,
        "C_exchange_functional_embedding_constructed_here": False,
        "multiplier_action_route_selected": False,
        "multiplier_action_route_constructed": False,
        "multiplier_field_type_selected": False,
        "multiplier_index_placement_selected": False,
        "multiplier_units_fixed": False,
        "boundary_terms_controlled": False,
        "metric_tetrad_variation_behavior_analyzed": False,
        "higher_derivative_risk_resolved": False,
        "circularity_control_established": False,
        "stability_analysis_completed": False,
        "penalty_route_selected": False,
        "penalty_route_constructed": False,
        "penalty_route_licensed": False,
        "direct_dynamical_law_interpretation_selected": False,
        "direct_force_law_claimed": False,
        "varied_dynamical_equation_claimed": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "candidate_varied": False,
        "action_embedding_claimed": False,
        "full_maxwell_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "quantized_electromagnetism_claimed": False,
        "anomaly_analysis_performed": False,
        "standard_model_derivation_claimed": False,
        "phase2_authorized": False,
        "empirical_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "critical_gate_fail_conditions": [
            "treat the functional-embedding packet as a C_exchange closeout",
            "select the multiplier/action route",
            "select or license the penalty route",
            "execute C_k action variation",
            "interpret C_exchange as a direct dynamical law",
            "claim full Maxwell closure",
            "claim EM-QFT or QFT-GR closure",
            "claim quantized electromagnetism",
            "perform or claim anomaly analysis",
            "derive the Standard Model",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "mathematical_statement": (
            "The packet records three functional-embedding options for "
            f"{C_EXCHANGE_CONSTRAINT_FORM}. The admissibility-only route "
            f"{ADMISSIBILITY_CONSTRAINT_FORM} is selected as a non-dynamical "
            "interaction acceptance rule. The multiplier/action route "
            f"{MULTIPLIER_ACTION_FORM} is blocked, and the quadratic penalty "
            f"{PENALTY_ACTION_FORM} is recorded as unlicensed. No action "
            "embedding, variation, or direct dynamical-law interpretation is "
            "selected."
        ),
        "plain_meaning": (
            "The psi-A interaction is admitted only as a balanced exchange "
            "route; no new action term, force law, or varied equation is "
            "licensed by this packet."
        ),
        "non_claim_boundary": (
            "This is a bounded C_exchange functional-embedding options packet "
            "only. It records the admissibility-only route "
            "C_exchange^{Apsi,nu} = 0 and selects it as a rule for accepting "
            "or rejecting the psi-A interaction route. It also records the "
            "multiplier/action route S_Cexchange = int d^4x sqrt(-g) "
            "lambda_nu C_exchange^{Apsi,nu} as blocked by unresolved "
            "multiplier field type, index placement, units, boundary terms, "
            "metric/tetrad variation behavior, higher-derivative risk, "
            "circularity control, and stability analysis. It records the "
            "penalty route int d^4x sqrt(-g) C_exchange_nu C_exchange^nu as "
            "unlicensed because it could introduce new dynamics with "
            "unresolved stability and unit/sign issues. It records no "
            "C_exchange closeout, no multiplier/action route, no penalty "
            "route, no C_k action variation, no direct dynamical-law "
            "interpretation, no full Maxwell closure, no EM-QFT closure, no "
            "QFT-GR closure, no quantized electromagnetism, no anomaly "
            "analysis, no Standard Model derivation, no Phase 2 "
            "authorization, no empirical validation, and no master-action "
            "promotion. The full ToeFormal aggregate is recorded as NOT_RUN "
            "for this packet."
        ),
        "validation_policy": validation_policy,
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "targeted_lean_build_status_for_packet": TARGETED_LEAN_BUILD_STATUS,
        "targeted_lean_builds_passed": True,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePsiAU1CExchangeFunctionalEmbeddingPacket",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "source_inputs": {
            "cexchange_constraint_candidate_result_review_json": _ptr(
                candidate_review_path
            ),
            "cexchange_constraint_candidate_result_review_outcome": (
                CANDIDATE_REVIEW_OUTCOME
            ),
        },
        "generated_outputs": {
            "json": _ptr(DEFAULT_OUT),
            "lean_marker": _ptr(LEAN_PACKET_PATH),
            "qftgr_aggregate": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "lean_validation_policy": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native psi-A U(1) C_exchange functional-embedding "
            "options packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--candidate-review", type=Path, default=CANDIDATE_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    candidate_review_path = (
        args.candidate_review
        if args.candidate_review.is_absolute()
        else REPO_ROOT / args.candidate_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_toe_native_psi_a_u1_cexchange_functional_embedding_packet(
        candidate_review_path=candidate_review_path,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(out, payload)
    print(
        "toe_native_psi_a_u1_cexchange_functional_embedding_packet: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
