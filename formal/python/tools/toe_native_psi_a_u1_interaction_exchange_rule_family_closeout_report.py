from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as SYNTHESIS_RESULT_REVIEW_PATH,
    EXCHANGE_TERM_CANCELLATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as SYNTHESIS_RESULT_REVIEW_OUTCOME,
    PACKET_ID as SYNTHESIS_RESULT_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT as SYNTHESIS_REVIEW_RESULT,
    RULE_CLASSIFICATION,
    RULE_EPISTEMIC_STATUS,
    RULE_FAMILY_CLASSIFICATION,
    RULE_FAMILY_EPISTEMIC_STATUS,
    RULE_FAMILY_ID,
    SCHEMA_ID as SYNTHESIS_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_20260626_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_v0"
CLOSEOUT_RESULT = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSED_AS_BOUNDED_"
    "CURRENT_SOURCE_AND_EXCHANGE_ADMISSIBILITY_FAMILY_NO_EM_QFT_OR_CK_ACTION_CLOSURE"
)
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_interaction_exchange_rule_family_closeout_closed_as_"
    "bounded_current_source_and_exchange_admissibility_family_no_em_qft_or_ck_action_closure"
)
NEXT_TARGET = (
    "review_toe_native_psi_A_u1_interaction_exchange_rule_family_closeout_result"
)
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_interaction_exchange_rule_family_closeout_result_review"
)
FOLLOW_ON_DECISION_TARGET_HINT = (
    "select_next_master_action_surface_after_psi_A_u1_interaction_exchange_family"
)
NARROW_FOLLOW_ON_SYNTHESIS_TARGET_HINT = (
    "prepare_master_action_ck_family_status_synthesis_after_phi_A_and_psi_A"
)
FAMILY_CLASSIFICATION = (
    "bounded psi-A U(1) current/source/exchange/total-conservation/C_exchange "
    "interaction admissibility family"
)
FAMILY_SCOPE = "bounded psi-A U(1) interaction"
FAMILY_EPISTEMIC_STATUS = "closed as bounded admissibility family; no seam closure"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_"
    "20260626_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1InteractionExchangeRuleFamilyCloseout.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "functional_action_embedding_claimed": False,
        "C_exchange_functional_embedding_claimed": False,
        "C_k_action_embedding_claimed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "multiplier_route_selected": False,
        "multiplier_action_route_selected": False,
        "penalty_route_selected": False,
        "candidate_varied": False,
        "direct_dynamical_law_claimed": False,
        "direct_dynamical_law_interpretation_selected": False,
        "direct_force_law_claimed": False,
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
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "master_action_promotion": False,
        "post_closeout_decision_executed": False,
        "master_action_surface_selected_after_closeout": False,
        "ck_family_status_synthesis_prepared": False,
    }


def _closeout_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "synthesis_result_review_consumed",
            "status": "accepted",
            "evidence": review.get("review_result"),
            "assessment": "The accepted interaction exchange synthesis result review is consumed.",
        },
        {
            "row_id": "current_route_closed_in_family",
            "status": "accepted",
            "evidence": CURRENT_CANDIDATE,
            "assessment": "The psi-A current route is included in the closed family.",
        },
        {
            "row_id": "current_conservation_closed_in_family",
            "status": "accepted",
            "evidence": CURRENT_CONSERVATION_RESULT,
            "assessment": "The current-conservation route is included in the closed family.",
        },
        {
            "row_id": "sourced_gauge_route_closed_in_family",
            "status": "accepted",
            "evidence": [SOURCE_CURRENT, SOURCED_GAUGE_ROUTE],
            "assessment": "The sourced Maxwell route is included as bounded sourced-gauge context.",
        },
        {
            "row_id": "exchange_halves_closed_in_family",
            "status": "accepted",
            "evidence": [GAUGE_SECTOR_EXCHANGE_IDENTITY, MATTER_SECTOR_EXCHANGE_IDENTITY],
            "assessment": "The gauge and matter equal-and-opposite exchange routes are closed in the family.",
        },
        {
            "row_id": "total_stress_energy_conservation_closed_in_family",
            "status": "accepted",
            "evidence": [
                TOTAL_STRESS_ENERGY_OBJECT,
                EXCHANGE_TERM_CANCELLATION,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            ],
            "assessment": "The total stress-energy conservation route is closed in the family.",
        },
        {
            "row_id": "C_exchange_admissibility_rule_closed_in_family",
            "status": "accepted",
            "evidence": [
                C_EXCHANGE_CONSTRAINT_FORM,
                C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
                C_EXCHANGE_ADMISSIBILITY_CONDITION,
            ],
            "assessment": "C_exchange closes only as an interaction exchange-balance admissibility rule.",
        },
        {
            "row_id": "bounded_admissibility_family_not_seam_closure",
            "status": "accepted",
            "evidence": [
                FAMILY_CLASSIFICATION,
                "seam_closure_claim=false",
                "master_action_promoted=false",
            ],
            "assessment": "The family is closed only as a bounded admissibility family.",
        },
        {
            "row_id": "no_forbidden_action_closure_or_empirical_claim",
            "status": "accepted",
            "evidence": [
                "C_k_action_embedding_claimed=false",
                "C_k_action_variation_executed=false",
                "multiplier_route_selected=false",
                "penalty_route_selected=false",
                "full_maxwell_closure_claimed=false",
                "em_qft_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "empirical_validation_claimed=false",
            ],
            "assessment": "No action, closure, quantization, empirical, Phase 2, or promotion claim is accepted.",
        },
        {
            "row_id": "closeout_result_review_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is the closeout result review only.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_psi_A_u1_interaction_exchange_rule_family_closeout"
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


def build_toe_native_psi_a_u1_interaction_exchange_rule_family_closeout(
    *,
    synthesis_result_review_path: Path = SYNTHESIS_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(synthesis_result_review_path)
    closeout_criteria = _closeout_criteria(review)
    acceptance_criteria = {
        "consumes_expected_synthesis_result_review": (
            review.get("schema_id") == SYNTHESIS_RESULT_REVIEW_SCHEMA_ID
            and review.get("packet_id") == SYNTHESIS_RESULT_REVIEW_PACKET_ID
            and review.get("outcome_id") == SYNTHESIS_RESULT_REVIEW_OUTCOME
            and review.get("review_result") == SYNTHESIS_REVIEW_RESULT
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "route_family_chain_complete": (
            [row.get("route_id") for row in review.get("route_family_chain", [])]
            == [
                "A_variation_current_candidate",
                "current_conservation",
                "sourced_maxwell_route",
                "gauge_sector_exchange",
                "matter_sector_exchange",
                "total_stress_energy_conservation",
                "C_exchange_rule",
            ]
        ),
        "required_forms_preserved": (
            review.get("current_candidate") == CURRENT_CANDIDATE
            and review.get("current_conservation_result") == CURRENT_CONSERVATION_RESULT
            and review.get("sourced_gauge_route") == SOURCED_GAUGE_ROUTE
            and review.get("gauge_sector_exchange_identity")
            == GAUGE_SECTOR_EXCHANGE_IDENTITY
            and review.get("matter_sector_exchange_identity")
            == MATTER_SECTOR_EXCHANGE_IDENTITY
            and review.get("total_stress_energy_object") == TOTAL_STRESS_ENERGY_OBJECT
            and review.get("total_stress_energy_conservation_identity")
            == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
            and review.get("C_exchange_constraint_form") == C_EXCHANGE_CONSTRAINT_FORM
            and review.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "C_exchange_rule_admissibility_only": (
            review.get("C_exchange_rule_classification") == RULE_CLASSIFICATION
            and review.get("C_exchange_rule_epistemic_status") == RULE_EPISTEMIC_STATUS
            and review.get("C_exchange_remains_admissibility_only") is True
        ),
        "no_forbidden_claims": all(
            review.get(key) is False
            for key in _false_boundary_flags()
            if key in review
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            review.get("aggregate_lean_validation_status_for_review")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and review.get("full_toeformal_aggregate_status_for_review")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and review.get("full_toeformal_aggregate_passed") is False
            and review.get("full_toeformal_aggregate_failed") is False
            and review.get("full_toeformal_aggregate_timed_out") is False
        ),
        "closeout_criteria_all_accepted": all(
            row["status"] == "accepted" for row in closeout_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_"
            "REQUIRES_REMEDIATION"
        ),
        "closeout_result": CLOSEOUT_RESULT,
        "packet_result": CLOSEOUT_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "synthesis_result_review_packet_id": SYNTHESIS_RESULT_REVIEW_PACKET_ID,
        "synthesis_result_review_outcome": SYNTHESIS_RESULT_REVIEW_OUTCOME,
        "synthesis_review_result": SYNTHESIS_REVIEW_RESULT,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
        "family_classification": FAMILY_CLASSIFICATION,
        "family_scope": FAMILY_SCOPE,
        "family_epistemic_status": FAMILY_EPISTEMIC_STATUS,
        "rule_family_id": RULE_FAMILY_ID,
        "rule_family_classification": RULE_FAMILY_CLASSIFICATION,
        "rule_family_epistemic_status": RULE_FAMILY_EPISTEMIC_STATUS,
        "route_family_chain": review.get("route_family_chain", []),
        "route_family_chain_count": len(review.get("route_family_chain", [])),
        "closed_route_roles": [
            "current candidate",
            "current conservation",
            "sourced gauge route",
            "gauge-sector exchange",
            "matter-sector exchange",
            "total stress-energy conservation",
            "interaction exchange-balance admissibility rule",
        ],
        "current_candidate": CURRENT_CANDIDATE,
        "source_current": SOURCE_CURRENT,
        "current_conservation_result": CURRENT_CONSERVATION_RESULT,
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
        "C_exchange_candidate_scope": C_EXCHANGE_CANDIDATE_SCOPE,
        "C_exchange_plain_meaning": C_EXCHANGE_PLAIN_MEANING,
        "C_exchange_rule_classification": RULE_CLASSIFICATION,
        "C_exchange_rule_epistemic_status": RULE_EPISTEMIC_STATUS,
        "closeout_criteria": closeout_criteria,
        "closeout_criteria_count": len(closeout_criteria),
        "closeout_criteria_accepted_count": sum(
            1 for row in closeout_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "closeout_prepared": accepted,
        "closeout_accepted": accepted,
        "review_accepted": accepted,
        "synthesis_result_review_accepted": accepted,
        "interaction_exchange_rule_family_closed": accepted,
        "bounded_current_source_exchange_admissibility_family_closed": accepted,
        "psi_A_current_route_closed": accepted,
        "current_conservation_route_closed": accepted,
        "sourced_maxwell_route_closed_as_bounded_context": accepted,
        "gauge_sector_exchange_route_closed": accepted,
        "matter_sector_exchange_route_closed": accepted,
        "total_stress_energy_conservation_route_closed": accepted,
        "C_exchange_admissibility_rule_closed": accepted,
        "C_exchange_rule_closed_as_interaction_exchange_balance_rule": accepted,
        "C_exchange_remains_admissibility_only": accepted,
        "master_action_remains_working_form_noncanonical": accepted,
        "claim_ladder_below_seam_closure": accepted,
        "closeout_result_review_authorized": accepted,
        "follow_on_decision_target_hint": FOLLOW_ON_DECISION_TARGET_HINT,
        "narrow_follow_on_synthesis_target_hint": NARROW_FOLLOW_ON_SYNTHESIS_TARGET_HINT,
        "follow_on_decision_executed": False,
        "mathematical_statement": (
            "The bounded psi-A U(1) interaction exchange family closes as: "
            f"{CURRENT_CANDIDATE}; {CURRENT_CONSERVATION_RESULT}; "
            f"{SOURCED_GAUGE_ROUTE}; {GAUGE_SECTOR_EXCHANGE_IDENTITY}; "
            f"{MATTER_SECTOR_EXCHANGE_IDENTITY}; "
            f"{C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM}; "
            f"{TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY}; "
            f"{C_EXCHANGE_CONSTRAINT_FORM}; {C_EXCHANGE_ADMISSIBILITY_CONDITION}."
        ),
        "plain_meaning": (
            "The interaction family closes only because the current, source, "
            "exchange, and total-balance chain is preserved: what one side "
            "loses, the other side gains, and C_exchange records that balance "
            "as an admissibility rule."
        ),
        "non_claim_boundary": (
            "This closeout records only the bounded psi-A U(1) interaction "
            "current/source/exchange/total-conservation/C_exchange admissibility "
            "family. It preserves J^mu = q psibar gamma^mu psi, nabla_mu J^mu = 0, "
            "nabla_mu F^{mu nu} = J^nu, nabla_mu T_A^{mu nu} = - F^nu{}_alpha "
            "J^alpha, nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha, "
            "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}, nabla_mu "
            "T_total^{mu nu} = 0, C_exchange^{Apsi,nu}[g,A,psi] := nabla_mu "
            "T_total^{mu nu}, and C_exchange^{Apsi,nu} = 0. It records no C_k "
            "action embedding, no C_k action variation, no multiplier route, no "
            "penalty route, no direct dynamical-law claim, no full Maxwell "
            "closure, no EM-QFT closure, no QFT-GR closure, no quantized "
            "electromagnetism, no anomaly analysis, no Standard Model derivation, "
            "no Phase 2 authorization, no empirical validation, and no "
            "master-action promotion. The master action remains a working-form, "
            "noncanonical, non-promoted organizing surface, and this work remains "
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory."
        ),
        "critical_gate_fail_conditions": [
            "drop the current route",
            "drop current conservation",
            "drop the sourced gauge route",
            "drop either exchange half",
            "drop total stress-energy conservation",
            "drop C_exchange admissibility-only status",
            "claim C_k action embedding",
            "execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "interpret C_exchange as a direct dynamical law",
            "claim full Maxwell closure",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "claim quantized electromagnetism",
            "perform anomaly analysis",
            "derive the Standard Model",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "execute the follow-on master-action decision inside this closeout",
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
            "ToeFormal.Derivation.ToeNativePsiAU1InteractionExchangeRuleFamilyCloseout",
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
            "synthesis_result_review_file": _ptr(synthesis_result_review_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }
    payload.update(_false_boundary_flags())
    return payload


def write_closeout(closeout: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(closeout, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native psi-A U(1) interaction exchange rule-family "
            "closeout."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--synthesis-result-review",
        type=Path,
        default=SYNTHESIS_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    synthesis_result_review_path = (
        args.synthesis_result_review
        if args.synthesis_result_review.is_absolute()
        else REPO_ROOT / args.synthesis_result_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_toe_native_psi_a_u1_interaction_exchange_rule_family_closeout(
        synthesis_result_review_path=synthesis_result_review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_closeout(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "closeout_result": payload["closeout_result"],
                "out": _ptr(path),
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
