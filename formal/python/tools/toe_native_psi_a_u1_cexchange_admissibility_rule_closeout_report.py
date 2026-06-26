from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_cexchange_functional_embedding_packet_result_review_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ADMISSIBILITY_ONLY_ROUTE_STATUS,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as FUNCTIONAL_EMBEDDING_REVIEW_PATH,
    EXCHANGE_TERM_CANCELLATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as FUNCTIONAL_EMBEDDING_REVIEW_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MULTIPLIER_ACTION_FORM,
    MULTIPLIER_ACTION_ROUTE_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
    PACKET_ID as FUNCTIONAL_EMBEDDING_REVIEW_PACKET_ID,
    PENALTY_ACTION_FORM,
    PENALTY_ROUTE_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT as FUNCTIONAL_EMBEDDING_REVIEW_RESULT,
    SCHEMA_ID as FUNCTIONAL_EMBEDDING_REVIEW_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-25T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_"
    "20260625_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_v0"
CLOSEOUT_RESULT = (
    "TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSED_AS_"
    "INTERACTION_EXCHANGE_BALANCE_RULE_NO_ACTION_VARIATION_OR_EM_QFT_CLOSURE"
)
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_cexchange_admissibility_rule_closed_as_"
    "interaction_exchange_balance_rule_no_action_variation_or_em_qft_closure"
)
NEXT_TARGET = (
    "review_toe_native_psi_A_u1_cexchange_admissibility_rule_closeout_result"
)
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_cexchange_admissibility_rule_closeout_result_review"
)
FOLLOW_ON_SYNTHESIS_TARGET = (
    "prepare_toe_native_psi_A_u1_interaction_exchange_rule_family_synthesis_packet"
)
FOLLOW_ON_SYNTHESIS_OUTCOME = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_PACKET_"
    "PREPARED_CURRENT_SOURCE_EXCHANGE_AND_TOTAL_CONSERVATION_ROUTES_SYNTHESIZED_"
    "NO_EM_QFT_OR_CK_ACTION_CLOSURE"
)

RULE_CLASSIFICATION = "interaction exchange-balance rule"
RULE_EPISTEMIC_STATUS = "admissibility-only"
RULE_SCOPE = (
    "accepted psi-A total stress-energy conservation route recorded as an "
    "interaction exchange-balance admissibility rule only"
)

BLOCKED_CLAIMS = [
    "no C_exchange functional embedding",
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

ACCEPTED_CLOSEOUT_FINDINGS = [
    "C_exchange admissibility rule closed",
    "interaction exchange-balance rule classification recorded",
    "C_exchange candidate preserved",
    "T_total = T_A + T_psi preserved",
    "C_exchange^{Apsi,nu} = 0 preserved",
    "accepted total stress-energy conservation route retained as basis",
    "admissibility-only status preserved",
    "no functionalization or action embedding",
    "no C_k action variation",
    "no EM-QFT or QFT-GR closure",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_"
    "20260625_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1CExchangeAdmissibilityRuleCloseout.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _closeout_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "functional_embedding_review_consumed",
            "status": "accepted",
            "evidence": review.get("review_result"),
            "assessment": "The accepted functional-embedding review is the consumed input.",
        },
        {
            "row_id": "cexchange_rule_closed_as_interaction_exchange_balance",
            "status": "accepted",
            "evidence": CLOSEOUT_RESULT,
            "assessment": "C_exchange is closed only as an interaction exchange-balance rule.",
        },
        {
            "row_id": "cexchange_candidate_form_preserved",
            "status": "accepted",
            "evidence": C_EXCHANGE_CONSTRAINT_FORM,
            "assessment": "The C_exchange residual definition is preserved.",
        },
        {
            "row_id": "total_stress_energy_form_preserved",
            "status": "accepted",
            "evidence": C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
            "assessment": "The total stress-energy definition is preserved.",
        },
        {
            "row_id": "admissibility_condition_preserved",
            "status": "accepted",
            "evidence": C_EXCHANGE_ADMISSIBILITY_CONDITION,
            "assessment": "C_exchange^{Apsi,nu} = 0 is preserved as the rule.",
        },
        {
            "row_id": "accepted_total_conservation_route_basis_preserved",
            "status": "accepted",
            "evidence": TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            "assessment": "The accepted total-conservation route remains the basis.",
        },
        {
            "row_id": "exchange_halves_context_preserved",
            "status": "accepted",
            "evidence": [
                GAUGE_SECTOR_EXCHANGE_IDENTITY,
                MATTER_SECTOR_EXCHANGE_IDENTITY,
                EXCHANGE_TERM_CANCELLATION,
            ],
            "assessment": "The gauge and matter exchange halves remain context.",
        },
        {
            "row_id": "admissibility_only_not_force_law",
            "status": "accepted",
            "evidence": [
                RULE_CLASSIFICATION,
                RULE_EPISTEMIC_STATUS,
                "direct_dynamical_law_interpretation_selected=false",
            ],
            "assessment": "The rule is not a new force law or varied equation.",
        },
        {
            "row_id": "multiplier_penalty_and_action_routes_blocked",
            "status": "accepted",
            "evidence": [MULTIPLIER_ACTION_FORM, PENALTY_ACTION_FORM],
            "assessment": "Multiplier/action and penalty routes remain blocked or unlicensed.",
        },
        {
            "row_id": "no_ck_action_variation_or_functionalization",
            "status": "accepted",
            "evidence": [
                "C_exchange_functional_embedding_constructed=false",
                "C_k_action_variation_executed=false",
                "candidate_varied=false",
            ],
            "assessment": "No functionalization, action embedding, or C_k variation is executed.",
        },
        {
            "row_id": "closure_quantization_phase_validation_and_promotion_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Closure, quantization, anomaly, Standard Model, Phase 2, empirical, and promotion claims remain blocked.",
        },
        {
            "row_id": "closeout_result_review_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is the closeout result review.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_psi_A_u1_cexchange_admissibility_rule_closeout"
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
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "aggregate_lean_validation_status_allowed_values": ["NOT_RUN"],
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "C_exchange_functional_embedding_claimed": False,
        "C_exchange_functional_embedding_selected": False,
        "C_exchange_functional_embedding_constructed": False,
        "functional_action_embedding_claimed": False,
        "functional_action_embedding_selected": False,
        "functional_action_embedding_constructed": False,
        "multiplier_action_route_selected": False,
        "multiplier_action_route_constructed": False,
        "multiplier_field_selected": False,
        "multiplier_field_type_selected": False,
        "penalty_route_selected": False,
        "penalty_route_constructed": False,
        "penalty_route_licensed": False,
        "penalty_functional_selected": False,
        "penalty_functional_defined": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_constructed": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "candidate_varied": False,
        "direct_dynamical_law_interpretation_selected": False,
        "direct_force_law_claimed": False,
        "varied_dynamical_equation_claimed": False,
        "new_force_law_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
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
        "total_interaction_theorem_beyond_accepted_route_scope_claimed": False,
        "interaction_exchange_rule_family_synthesis_packet_prepared": False,
        "interaction_exchange_rule_family_synthesized": False,
    }


def build_toe_native_psi_a_u1_cexchange_admissibility_rule_closeout(
    *,
    functional_embedding_review_path: Path = FUNCTIONAL_EMBEDDING_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(functional_embedding_review_path)
    criteria = _closeout_criteria(review)
    acceptance_criteria = {
        "consumes_expected_closeout_target": (
            review.get("schema_id") == FUNCTIONAL_EMBEDDING_REVIEW_SCHEMA_ID
            and review.get("packet_id") == FUNCTIONAL_EMBEDDING_REVIEW_PACKET_ID
            and review.get("outcome_id") == FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME
            and review.get("review_result") == FUNCTIONAL_EMBEDDING_REVIEW_RESULT
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "candidate_forms_preserved": (
            review.get("C_exchange_constraint_id") == C_EXCHANGE_CONSTRAINT_ID
            and review.get("C_exchange_constraint_form") == C_EXCHANGE_CONSTRAINT_FORM
            and review.get("C_exchange_total_stress_energy_form")
            == C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
            and review.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "accepted_route_context_preserved": (
            review.get("gauge_sector_exchange_identity")
            == GAUGE_SECTOR_EXCHANGE_IDENTITY
            and review.get("matter_sector_exchange_identity")
            == MATTER_SECTOR_EXCHANGE_IDENTITY
            and review.get("exchange_term_cancellation")
            == EXCHANGE_TERM_CANCELLATION
            and review.get("total_stress_energy_conservation_identity")
            == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "admissibility_only_review_accepted": (
            review.get("admissibility_only_route_accepted") is True
            and review.get("admissibility_only_route_selected") is True
            and review.get("constraint_as_admissibility_rule_selected") is True
            and review.get("direct_dynamical_law_interpretation_blocked") is True
        ),
        "action_routes_blocked": (
            review.get("multiplier_action_route_blocked") is True
            and review.get("multiplier_action_route_selected") is False
            and review.get("penalty_route_unlicensed") is True
            and review.get("penalty_route_selected") is False
        ),
        "no_action_embedding_or_variation": all(
            review.get(key) is False
            for key in [
                "functional_action_embedding_claimed",
                "C_exchange_functional_embedding_claimed",
                "C_exchange_functional_embedding_constructed",
                "multiplier_field_selected",
                "penalty_functional_selected",
                "C_k_action_variation_executed",
                "C_k_action_variation_authorized",
                "candidate_varied",
                "action_embedding_claimed",
            ]
        ),
        "no_forbidden_claims": all(
            review.get(key) is False
            for key in [
                "total_interaction_theorem_beyond_accepted_route_scope_claimed",
                "full_maxwell_closure_claimed",
                "em_qft_closure_claimed",
                "qft_gr_closure_claimed",
                "quantized_electromagnetism_claimed",
                "anomaly_analysis_performed",
                "standard_model_derivation_claimed",
                "phase2_authorized",
                "empirical_validation_claimed",
                "master_action_promoted",
                "master_action_promotion_authorized",
                "pillar_completion_inferred",
                "seam_closure_claim",
            ]
        ),
        "criteria_all_accepted": all(row["status"] == "accepted" for row in criteria),
        "blocked_claims_exactly_scoped": len(BLOCKED_CLAIMS) == 14,
    }
    accepted = all(acceptance_criteria.values())
    closeout: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_REQUIRES_REMEDIATION",
        "closeout_result": CLOSEOUT_RESULT,
        "packet_result": "CLOSEOUT_ACCEPTED" if accepted else "CLOSEOUT_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT",
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "functional_embedding_review_outcome": FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
        "functional_embedding_review_result": FUNCTIONAL_EMBEDDING_REVIEW_RESULT,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "source_current": SOURCE_CURRENT,
        "sourced_gauge_route": SOURCED_GAUGE_ROUTE,
        "gauge_sector_exchange_identity": GAUGE_SECTOR_EXCHANGE_IDENTITY,
        "matter_sector_exchange_identity": MATTER_SECTOR_EXCHANGE_IDENTITY,
        "exchange_term_cancellation": EXCHANGE_TERM_CANCELLATION,
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
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
        "rule_classification": RULE_CLASSIFICATION,
        "rule_epistemic_status": RULE_EPISTEMIC_STATUS,
        "rule_scope": RULE_SCOPE,
        "multiplier_action_route_id": MULTIPLIER_ACTION_ROUTE_ID,
        "multiplier_action_form": MULTIPLIER_ACTION_FORM,
        "penalty_route_id": PENALTY_ROUTE_ID,
        "penalty_action_form": PENALTY_ACTION_FORM,
        "accepted_closeout_findings": ACCEPTED_CLOSEOUT_FINDINGS,
        "accepted_closeout_findings_count": len(ACCEPTED_CLOSEOUT_FINDINGS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "closeout_criteria": criteria,
        "closeout_criteria_count": len(criteria),
        "closeout_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "admissibility_rule_closeout_prepared": accepted,
        "admissibility_rule_closeout_accepted": accepted,
        "C_exchange_admissibility_rule_closed": accepted,
        "C_exchange_definition_closeout": accepted,
        "C_exchange_rule_closed_as_interaction_exchange_balance_rule": accepted,
        "interaction_exchange_balance_rule_closed": accepted,
        "candidate_recorded_as_rule_only": accepted,
        "admissibility_only_route_selected": accepted,
        "admissibility_only_interpretation_retained": accepted,
        "constraint_as_admissibility_rule_selected": accepted,
        "based_on_accepted_total_stress_energy_conservation_route": accepted,
        "C_exchange_candidate_preserved": accepted,
        "T_total_preserved": accepted,
        "exchange_halves_context_preserved": accepted,
        "closeout_result_review_selected_next": accepted,
        "closeout_result_review_prepared": False,
        "follow_on_synthesis_target": FOLLOW_ON_SYNTHESIS_TARGET,
        "follow_on_synthesis_outcome": FOLLOW_ON_SYNTHESIS_OUTCOME,
        "follow_on_synthesis_prepared": False,
        "mathematical_statement": (
            f"{C_EXCHANGE_CONSTRAINT_FORM}, with "
            f"{C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM} and admissibility rule "
            f"{C_EXCHANGE_ADMISSIBILITY_CONDITION}. The closeout records this "
            "only as an interaction exchange-balance admissibility rule based "
            "on the accepted total stress-energy conservation route."
        ),
        "plain_meaning": (
            "The psi-A interaction is admissible only if matter and gauge-field "
            "energy-momentum exchange balances as one total system."
        ),
        "non_claim_boundary": (
            "This closeout closes C_exchange^{Apsi,nu} = 0 only as an "
            "interaction exchange-balance admissibility rule. It preserves "
            "C_exchange^{Apsi,nu}[g,A,psi] := nabla_mu T_total^{mu nu}, "
            "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}, and "
            "C_exchange^{Apsi,nu} = 0. It is admissibility-only, not "
            "functionalized, not action embedded, not varied, not a new force "
            "law, not Maxwell closure, not EM-QFT closure, not QFT-GR closure, "
            "and not master-action promotion. It keeps the multiplier/action "
            "route blocked, keeps the penalty route unlicensed, records no "
            "C_k action variation, no direct dynamical-law interpretation, no "
            "quantized electromagnetism, no anomaly analysis, no Standard "
            "Model derivation, no Phase 2 authorization, and no empirical "
            "validation. The full ToeFormal aggregate is recorded as NOT_RUN "
            "for this closeout."
        ),
        "critical_gate_fail_conditions": [
            "claim C_exchange functional embedding",
            "select multiplier/action route",
            "license penalty route",
            "execute C_k action variation",
            "interpret C_exchange as a direct dynamical law",
            "claim C_exchange is a new force law",
            "claim full Maxwell closure",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "claim quantized electromagnetism",
            "perform anomaly analysis",
            "derive the Standard Model",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "prepare the interaction-exchange synthesis packet before review",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePsiAU1CExchangeAdmissibilityRuleCloseout",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "functional_embedding_review_file": _ptr(
                functional_embedding_review_path
            ),
            "functional_embedding_review_lean_packet_file": _ptr(
                FUNCTIONAL_EMBEDDING_REVIEW_LEAN_PACKET_PATH
            ),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }
    closeout.update(_false_boundary_flags())
    return closeout


def write_closeout(closeout: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(closeout, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native psi-A U(1) C_exchange admissibility-rule "
            "closeout."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    closeout = build_toe_native_psi_a_u1_cexchange_admissibility_rule_closeout(
        captured_at_utc=args.captured_at_utc
    )
    path = write_closeout(closeout, args.out)
    print(
        json.dumps(
            {
                "accepted": closeout["accepted"],
                "closeout_result": closeout["closeout_result"],
                "out": _ptr(path),
                "selected_next_target": closeout["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
