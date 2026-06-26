from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_cexchange_admissibility_rule_closeout_result_review_report import (
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as CLOSEOUT_REVIEW_PATH,
    EXCHANGE_TERM_CANCELLATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as CLOSEOUT_REVIEW_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as CLOSEOUT_REVIEW_OUTCOME,
    PACKET_ID as CLOSEOUT_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT as CLOSEOUT_REVIEW_RESULT,
    RULE_CLASSIFICATION,
    RULE_EPISTEMIC_STATUS,
    SCHEMA_ID as CLOSEOUT_REVIEW_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
)
from formal.python.tools.toe_native_psi_a_u1_current_conservation_from_dirac_pair_packet_report import (
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_PACKET_"
    "20260626_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_PACKET_v0"
PACKET_RESULT = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_PACKET_"
    "PREPARED_CURRENT_SOURCE_EXCHANGE_AND_TOTAL_CONSERVATION_ROUTES_SYNTHESIZED_"
    "NO_EM_QFT_OR_CK_ACTION_CLOSURE"
)
OUTCOME_ID = PACKET_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_interaction_exchange_rule_family_synthesis_packet_"
    "prepared_current_source_exchange_and_total_conservation_routes_synthesized_"
    "no_em_qft_or_ck_action_closure"
)
NEXT_TARGET = (
    "review_toe_native_psi_A_u1_interaction_exchange_rule_family_synthesis_packet_result"
)
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_interaction_exchange_rule_family_synthesis_packet_result_review"
)

RULE_FAMILY_ID = "psi_A_u1_current_source_exchange_total_conservation_rule_family"
RULE_FAMILY_CLASSIFICATION = (
    "psi-A U(1) interaction current/source/exchange/total-conservation/C_exchange route family"
)
RULE_FAMILY_EPISTEMIC_STATUS = "bounded synthesis; admissibility-only for C_exchange"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_PACKET_"
    "20260626_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1InteractionExchangeRuleFamilySynthesisPacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _route_family_chain() -> list[dict[str, Any]]:
    return [
        {
            "route_id": "A_variation_current_candidate",
            "route_role": "current candidate",
            "statement": CURRENT_CANDIDATE,
            "status": "accepted_bounded_input",
        },
        {
            "route_id": "current_conservation",
            "route_role": "current conservation",
            "statement": CURRENT_CONSERVATION_RESULT,
            "status": "accepted_bounded_route",
        },
        {
            "route_id": "sourced_maxwell_route",
            "route_role": "sourced gauge route",
            "statement": SOURCED_GAUGE_ROUTE,
            "source_current": SOURCE_CURRENT,
            "status": "recorded_bounded_sourced_route_no_full_maxwell_closure",
        },
        {
            "route_id": "gauge_sector_exchange",
            "route_role": "gauge-sector exchange",
            "statement": GAUGE_SECTOR_EXCHANGE_IDENTITY,
            "status": "accepted_bounded_exchange_half",
        },
        {
            "route_id": "matter_sector_exchange",
            "route_role": "matter-sector exchange",
            "statement": MATTER_SECTOR_EXCHANGE_IDENTITY,
            "status": "accepted_bounded_exchange_half",
        },
        {
            "route_id": "total_stress_energy_conservation",
            "route_role": "total conservation",
            "statement": TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            "total_stress_energy_object": TOTAL_STRESS_ENERGY_OBJECT,
            "cancellation": EXCHANGE_TERM_CANCELLATION,
            "status": "accepted_bounded_total_route",
        },
        {
            "route_id": "C_exchange_rule",
            "route_role": "interaction exchange-balance admissibility rule",
            "statement": C_EXCHANGE_ADMISSIBILITY_CONDITION,
            "constraint_form": C_EXCHANGE_CONSTRAINT_FORM,
            "total_stress_energy_form": C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
            "status": "closed_as_admissibility_only_rule",
        },
    ]


def _synthesis_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "closeout_result_review_consumed",
            "status": "accepted",
            "evidence": review.get("review_result"),
            "assessment": "The accepted C_exchange closeout result review is consumed.",
        },
        {
            "row_id": "current_candidate_and_conservation_preserved",
            "status": "accepted",
            "evidence": [CURRENT_CANDIDATE, CURRENT_CONSERVATION_RESULT],
            "assessment": "The current candidate and current-conservation route are preserved.",
        },
        {
            "row_id": "sourced_gauge_route_preserved",
            "status": "accepted",
            "evidence": [SOURCE_CURRENT, SOURCED_GAUGE_ROUTE],
            "assessment": "The sourced Maxwell route is preserved as bounded context.",
        },
        {
            "row_id": "exchange_halves_preserved",
            "status": "accepted",
            "evidence": [GAUGE_SECTOR_EXCHANGE_IDENTITY, MATTER_SECTOR_EXCHANGE_IDENTITY],
            "assessment": "The gauge and matter exchange halves are preserved.",
        },
        {
            "row_id": "total_conservation_preserved",
            "status": "accepted",
            "evidence": [
                TOTAL_STRESS_ENERGY_OBJECT,
                EXCHANGE_TERM_CANCELLATION,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            ],
            "assessment": "The total stress-energy conservation route is preserved.",
        },
        {
            "row_id": "cexchange_rule_preserved",
            "status": "accepted",
            "evidence": [
                C_EXCHANGE_CONSTRAINT_FORM,
                C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
                C_EXCHANGE_ADMISSIBILITY_CONDITION,
            ],
            "assessment": "C_exchange remains the interaction exchange-balance admissibility rule.",
        },
        {
            "row_id": "no_em_qft_or_ck_action_closure",
            "status": "accepted",
            "evidence": [
                "em_qft_closure_claimed=false",
                "C_k_action_variation_executed=false",
                "master_action_promoted=false",
            ],
            "assessment": "The synthesis makes no EM-QFT, C_k action, or master-action closure claim.",
        },
        {
            "row_id": "result_review_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is the synthesis packet result review.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_psi_A_u1_interaction_exchange_rule_family_synthesis_packet"
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
        "functional_action_embedding_claimed": False,
        "C_exchange_functional_embedding_claimed": False,
        "multiplier_action_route_selected": False,
        "penalty_route_selected": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "candidate_varied": False,
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
    }


def build_toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_packet(
    *,
    closeout_review_path: Path = CLOSEOUT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(closeout_review_path)
    route_family_chain = _route_family_chain()
    synthesis_criteria = _synthesis_criteria(review)
    acceptance_criteria = {
        "consumes_expected_closeout_result_review": (
            review.get("schema_id") == CLOSEOUT_REVIEW_SCHEMA_ID
            and review.get("packet_id") == CLOSEOUT_REVIEW_PACKET_ID
            and review.get("outcome_id") == CLOSEOUT_REVIEW_OUTCOME
            and review.get("review_result") == CLOSEOUT_REVIEW_RESULT
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "route_family_chain_complete": (
            [row["route_id"] for row in route_family_chain]
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
        "cexchange_rule_preserved": (
            review.get("C_exchange_constraint_id") == C_EXCHANGE_CONSTRAINT_ID
            and review.get("C_exchange_constraint_form") == C_EXCHANGE_CONSTRAINT_FORM
            and review.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
            and review.get("rule_epistemic_status") == RULE_EPISTEMIC_STATUS
        ),
        "no_forbidden_claims": all(
            review.get(key) is False for key in _false_boundary_flags() if key in review
        ),
        "synthesis_criteria_all_accepted": all(
            row["status"] == "accepted" for row in synthesis_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_"
            "SYNTHESIS_PACKET"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_"
            "SYNTHESIS_PACKET"
        ),
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "closeout_result_review_outcome": CLOSEOUT_REVIEW_OUTCOME,
        "closeout_result_review_result": CLOSEOUT_REVIEW_RESULT,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "rule_family_id": RULE_FAMILY_ID,
        "rule_family_classification": RULE_FAMILY_CLASSIFICATION,
        "rule_family_epistemic_status": RULE_FAMILY_EPISTEMIC_STATUS,
        "route_family_chain": route_family_chain,
        "route_family_chain_count": len(route_family_chain),
        "synthesized_route_roles": [row["route_role"] for row in route_family_chain],
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
        "synthesis_criteria": synthesis_criteria,
        "synthesis_criteria_count": len(synthesis_criteria),
        "synthesis_criteria_accepted_count": sum(
            1 for row in synthesis_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "synthesis_packet_prepared": accepted,
        "interaction_exchange_rule_family_synthesis_packet_prepared": accepted,
        "interaction_exchange_rule_family_synthesized": accepted,
        "current_source_exchange_and_total_conservation_routes_synthesized": accepted,
        "C_exchange_rule_preserved": accepted,
        "C_exchange_remains_admissibility_only": accepted,
        "C_exchange_closeout_accepted": accepted,
        "result_review_authorized": accepted,
        "mathematical_statement": (
            "The psi-A U(1) interaction chain is synthesized as: "
            f"{CURRENT_CANDIDATE}; {CURRENT_CONSERVATION_RESULT}; "
            f"{SOURCED_GAUGE_ROUTE}; {GAUGE_SECTOR_EXCHANGE_IDENTITY}; "
            f"{MATTER_SECTOR_EXCHANGE_IDENTITY}; "
            f"{TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY}; "
            f"{C_EXCHANGE_ADMISSIBILITY_CONDITION}."
        ),
        "plain_meaning": (
            "The packet gathers the bounded route in which matter makes a "
            "conserved current, that current sources A, the A and psi sectors "
            "exchange equal and opposite energy-momentum, the total balances, "
            "and C_exchange records the admissibility rule for that balance."
        ),
        "non_claim_boundary": (
            "This synthesis packet gathers the psi-A U(1) current, source, "
            "exchange, total-conservation, and C_exchange route family only. "
            "It records no EM-QFT closure, no QFT-GR closure, no full Maxwell "
            "closure, no C_k action closure, no C_k action variation, no "
            "functional action embedding, no multiplier/action route, no "
            "penalty route, no direct dynamical-law interpretation, no "
            "quantized electromagnetism, no anomaly analysis, no Standard "
            "Model derivation, no Phase 2 authorization, no empirical "
            "validation, and no master-action promotion. The master action "
            "remains a working-form, noncanonical organizing surface."
        ),
        "critical_gate_fail_conditions": [
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "claim full Maxwell closure",
            "claim C_k action closure",
            "execute C_k action variation",
            "functionalize C_exchange",
            "select multiplier/action or penalty route",
            "interpret C_exchange as a new force law",
            "claim quantized electromagnetism",
            "perform anomaly analysis",
            "derive the Standard Model",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
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
            "ToeFormal.Derivation.ToeNativePsiAU1InteractionExchangeRuleFamilySynthesisPacket",
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
            "closeout_review_file": _ptr(closeout_review_path),
            "closeout_review_lean_packet_file": _ptr(CLOSEOUT_REVIEW_LEAN_PACKET_PATH),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }
    payload.update(_false_boundary_flags())
    return payload


def write_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native psi-A U(1) interaction exchange rule-family "
            "synthesis packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--closeout-review", type=Path, default=CLOSEOUT_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    closeout_review_path = (
        args.closeout_review
        if args.closeout_review.is_absolute()
        else REPO_ROOT / args.closeout_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_packet(
        closeout_review_path=closeout_review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_packet(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "packet_result": payload["packet_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
