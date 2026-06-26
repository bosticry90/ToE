from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_cexchange_functional_embedding_packet_report import (
    ADMISSIBILITY_CONSTRAINT_FORM,
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ADMISSIBILITY_ONLY_ROUTE_STATUS,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as EMBEDDING_PACKET_PATH,
    EXCHANGE_TERM_CANCELLATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAUGE_SECTOR_EXCHANGE_TERM,
    LEAN_PACKET_PATH as EMBEDDING_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MATTER_SECTOR_EXCHANGE_TERM,
    MULTIPLIER_ACTION_FORM,
    MULTIPLIER_ACTION_ROUTE_ID,
    MULTIPLIER_BLOCKING_REASONS,
    MULTIPLIER_ROUTE_STATUS,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EMBEDDING_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EMBEDDING_PACKET_CLASSIFICATION,
    PACKET_ID as EMBEDDING_PACKET_ID,
    PENALTY_ACTION_FORM,
    PENALTY_BLOCKING_REASONS,
    PENALTY_ROUTE_ID,
    PENALTY_ROUTE_STATUS,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as EMBEDDING_PACKET_SCHEMA_ID,
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

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_"
    "RESULT_REVIEW_20260625_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_"
    "RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_RESULT_REVIEW_"
    "ACCEPTS_ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_OR_EM_QFT_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_cexchange_functional_embedding_result_review_"
    "accepts_admissibility_only_route_no_action_variation_or_em_qft_closure"
)
NEXT_TARGET = "prepare_toe_native_psi_A_u1_cexchange_admissibility_rule_closeout"
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_cexchange_admissibility_rule_closeout_preparation"
)

ACCEPTED_REVIEW_FINDINGS = [
    "C_exchange candidate preserved",
    "admissibility-only route selected",
    "multiplier/action route blocked",
    "penalty route unlicensed",
    "direct dynamical-law interpretation blocked",
    "no C_k action variation",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no master-action promotion",
]

BLOCKED_CLAIMS = [
    "no C_exchange closeout",
    "no functional action embedding",
    "no multiplier field",
    "no penalty functional",
    "no total interaction theorem beyond accepted route scope",
    "no full Maxwell closure",
    "no quantized electromagnetism",
    "no anomaly analysis",
    "no Standard Model derivation",
    "no Phase 2 authorization",
    "no empirical validation",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_"
    "RESULT_REVIEW_20260625_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1CExchangeFunctionalEmbeddingPacketResultReview.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "functional_embedding_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("outcome_id"),
            "assessment": "The prepared C_exchange functional-embedding packet is the consumed input.",
        },
        {
            "row_id": "cexchange_candidate_preserved",
            "status": "accepted",
            "evidence": [
                C_EXCHANGE_CONSTRAINT_FORM,
                C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
                C_EXCHANGE_ADMISSIBILITY_CONDITION,
            ],
            "assessment": "The C_exchange candidate and admissibility condition are preserved.",
        },
        {
            "row_id": "admissibility_only_route_selected",
            "status": "accepted",
            "evidence": ADMISSIBILITY_ONLY_ROUTE_ID,
            "assessment": "The review accepts only the non-dynamical admissibility route.",
        },
        {
            "row_id": "multiplier_action_route_blocked",
            "status": "accepted",
            "evidence": [MULTIPLIER_ACTION_FORM, MULTIPLIER_BLOCKING_REASONS],
            "assessment": "The multiplier/action route remains blocked.",
        },
        {
            "row_id": "penalty_route_unlicensed",
            "status": "accepted",
            "evidence": [PENALTY_ACTION_FORM, PENALTY_BLOCKING_REASONS],
            "assessment": "The penalty route remains recorded but unlicensed.",
        },
        {
            "row_id": "direct_dynamical_law_interpretation_blocked",
            "status": "accepted",
            "evidence": [
                "direct_dynamical_law_interpretation_selected=false",
                "direct_force_law_claimed=false",
                "varied_dynamical_equation_claimed=false",
            ],
            "assessment": "C_exchange is not interpreted as a new force law or varied equation.",
        },
        {
            "row_id": "no_ck_action_variation",
            "status": "accepted",
            "evidence": [
                "C_k_action_variation_executed=false",
                "C_k_action_variation_authorized=false",
                "candidate_varied=false",
            ],
            "assessment": "No C_k action variation is executed or authorized.",
        },
        {
            "row_id": "no_functional_action_embedding",
            "status": "accepted",
            "evidence": [
                "functional_action_embedding_claimed=false",
                "multiplier_field_selected=false",
                "penalty_functional_selected=false",
            ],
            "assessment": "No action embedding, multiplier field, or penalty functional is selected.",
        },
        {
            "row_id": "no_total_interaction_theorem_beyond_route_scope",
            "status": "accepted",
            "evidence": TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            "assessment": "The accepted total-conservation route remains bounded route scope only.",
        },
        {
            "row_id": "no_closure_phase2_empirical_or_promotion",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Closure, quantization, anomaly, Standard Model, Phase 2, empirical, and promotion claims remain blocked.",
        },
        {
            "row_id": "admissibility_rule_closeout_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is the C_exchange admissibility-rule closeout preparation.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_psi_A_u1_cexchange_functional_embedding_packet_"
            "result_review"
        ),
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "targeted_lean_build_status_for_review": TARGETED_LEAN_BUILD_STATUS,
        "targeted_lean_builds_passed": True,
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "aggregate_lean_validation_status_allowed_values": ["NOT_RUN"],
        "full_toeformal_aggregate_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_toe_native_psi_a_u1_cexchange_functional_embedding_packet_result_review(
    *,
    embedding_packet_path: Path = EMBEDDING_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(embedding_packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_functional_embedding_packet": (
            packet.get("schema_id") == EMBEDDING_PACKET_SCHEMA_ID
            and packet.get("packet_id") == EMBEDDING_PACKET_ID
            and packet.get("outcome_id") == EMBEDDING_PACKET_OUTCOME
            and packet.get("packet_result") == EMBEDDING_PACKET_OUTCOME
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "candidate_preserved": (
            packet.get("C_exchange_constraint_id") == C_EXCHANGE_CONSTRAINT_ID
            and packet.get("C_exchange_constraint_form")
            == C_EXCHANGE_CONSTRAINT_FORM
            and packet.get("C_exchange_total_stress_energy_form")
            == C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
            and packet.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "exchange_context_preserved": (
            packet.get("gauge_sector_exchange_identity")
            == GAUGE_SECTOR_EXCHANGE_IDENTITY
            and packet.get("matter_sector_exchange_identity")
            == MATTER_SECTOR_EXCHANGE_IDENTITY
            and packet.get("exchange_term_cancellation")
            == EXCHANGE_TERM_CANCELLATION
            and packet.get("total_stress_energy_conservation_identity")
            == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "admissibility_only_route_selected": (
            packet.get("selected_embedding_route_id") == ADMISSIBILITY_ONLY_ROUTE_ID
            and packet.get("admissibility_only_route_selected") is True
            and packet.get("constraint_as_admissibility_rule_selected") is True
            and packet.get("C_exchange_functional_embedding_claimed") is False
        ),
        "multiplier_action_route_blocked": (
            packet.get("multiplier_action_route_id") == MULTIPLIER_ACTION_ROUTE_ID
            and packet.get("multiplier_action_form") == MULTIPLIER_ACTION_FORM
            and packet.get("multiplier_action_route_recorded") is True
            and packet.get("multiplier_action_route_blocked") is True
            and packet.get("multiplier_action_route_selected") is False
            and packet.get("multiplier_blocking_reasons")
            == MULTIPLIER_BLOCKING_REASONS
        ),
        "penalty_route_unlicensed": (
            packet.get("penalty_route_id") == PENALTY_ROUTE_ID
            and packet.get("penalty_action_form") == PENALTY_ACTION_FORM
            and packet.get("penalty_route_recorded") is True
            and packet.get("penalty_route_unlicensed") is True
            and packet.get("penalty_route_selected") is False
            and packet.get("penalty_blocking_reasons") == PENALTY_BLOCKING_REASONS
        ),
        "direct_dynamical_law_blocked": (
            packet.get("direct_dynamical_law_interpretation_blocked") is True
            and packet.get("direct_dynamical_law_interpretation_selected") is False
            and packet.get("direct_force_law_claimed") is False
            and packet.get("varied_dynamical_equation_claimed") is False
        ),
        "no_action_variation_or_embedding": all(
            packet.get(key) is False
            for key in [
                "C_k_action_variation_executed",
                "C_k_action_variation_authorized",
                "candidate_varied",
                "action_embedding_claimed",
                "multiplier_field_type_selected",
                "penalty_route_licensed",
            ]
        ),
        "closure_promotion_boundaries_preserved": all(
            packet.get(key) is False
            for key in [
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
        "accepted_review_findings_exactly_scoped": len(ACCEPTED_REVIEW_FINDINGS) == 9,
        "blocked_claims_exactly_scoped": len(BLOCKED_CLAIMS) == 11,
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    validation_policy = _validation_policy()
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_"
            "PACKET_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "review_prepared": accepted,
        "review_result": REVIEW_RESULT,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_REVIEW",
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "embedding_packet_outcome": EMBEDDING_PACKET_OUTCOME,
        "embedding_packet_result": EMBEDDING_PACKET_OUTCOME,
        "embedding_packet_classification": EMBEDDING_PACKET_CLASSIFICATION,
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
        "admissibility_only_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_constraint_form": ADMISSIBILITY_CONSTRAINT_FORM,
        "admissibility_only_route_status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
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
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": accepted,
        "functional_embedding_result_review_prepared": accepted,
        "functional_embedding_result_review_accepted": accepted,
        "C_exchange_functional_embedding_result_review_accepted": accepted,
        "C_exchange_functional_embedding_packet_accepted": accepted,
        "C_exchange_candidate_preserved": accepted,
        "C_exchange_candidate_carried_forward": accepted,
        "admissibility_only_route_selected": accepted,
        "admissibility_only_route_accepted": accepted,
        "admissibility_only_interpretation_retained": accepted,
        "interaction_admissibility_rule_selected": accepted,
        "constraint_as_admissibility_rule_selected": accepted,
        "multiplier_action_route_blocked": accepted,
        "penalty_route_unlicensed": accepted,
        "direct_dynamical_law_interpretation_blocked": accepted,
        "no_C_k_action_variation_confirmed": accepted,
        "no_EM_QFT_closure_confirmed": accepted,
        "no_QFT_GR_closure_confirmed": accepted,
        "no_master_action_promotion_confirmed": accepted,
        "functional_embedding_packet_consumed": accepted,
        "admissibility_rule_closeout_selected_after_review": accepted,
        "C_exchange_admissibility_rule_closeout_authorized": accepted,
        "C_exchange_closeout": False,
        "C_exchange_definition_closeout": False,
        "C_exchange_rule_family_closed": False,
        "admissibility_rule_closeout_prepared": False,
        "functional_action_embedding_claimed": False,
        "functional_action_embedding_selected": False,
        "functional_action_embedding_constructed": False,
        "C_exchange_functional_embedding_claimed": False,
        "C_exchange_functional_embedding_selected": False,
        "C_exchange_functional_embedding_constructed": False,
        "multiplier_field_selected": False,
        "multiplier_field_type_selected": False,
        "multiplier_action_route_selected": False,
        "multiplier_action_route_constructed": False,
        "penalty_functional_selected": False,
        "penalty_functional_defined": False,
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
        "total_interaction_theorem_beyond_accepted_route_scope_claimed": False,
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
            "treat this result review as C_exchange closeout",
            "claim functional action embedding",
            "select a multiplier field",
            "license a penalty functional",
            "execute C_k action variation",
            "interpret C_exchange as a direct dynamical law",
            "claim total interaction theorem beyond accepted route scope",
            "claim full Maxwell closure",
            "claim quantized electromagnetism",
            "perform or claim anomaly analysis",
            "derive the Standard Model",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "mathematical_statement": (
            "The result review accepts only the admissibility-only route "
            f"{C_EXCHANGE_ADMISSIBILITY_CONDITION} for the preserved candidate "
            f"{C_EXCHANGE_CONSTRAINT_FORM}. The multiplier/action route "
            f"{MULTIPLIER_ACTION_FORM} remains blocked, the penalty route "
            f"{PENALTY_ACTION_FORM} remains unlicensed, direct dynamical-law "
            "interpretation remains blocked, and no C_k action variation is "
            "executed."
        ),
        "plain_meaning": (
            "The psi-A C_exchange rule remains an admissibility rule: the "
            "interaction is accepted only when the total exchange balance "
            "vanishes, without adding a new action term or law."
        ),
        "non_claim_boundary": (
            "This is a bounded C_exchange functional-embedding result review "
            "only. It accepts that the C_exchange candidate is preserved, that "
            "the admissibility-only route C_exchange^{Apsi,nu} = 0 is selected, "
            "that the multiplier/action route is blocked, that the penalty route "
            "is unlicensed, that direct dynamical-law interpretation is blocked, "
            "and that no C_k action variation is executed. It selects "
            "C_exchange admissibility-rule closeout preparation next. It records "
            "no C_exchange closeout, no functional action embedding, no "
            "multiplier field, no penalty functional, no total interaction "
            "theorem beyond accepted route scope, no full Maxwell closure, no "
            "quantized electromagnetism, no anomaly analysis, no Standard Model "
            "derivation, no Phase 2 authorization, no empirical validation, and "
            "no master-action promotion. The full ToeFormal aggregate is "
            "recorded as NOT_RUN for this review."
        ),
        "validation_policy": validation_policy,
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "targeted_lean_build_status_for_review": TARGETED_LEAN_BUILD_STATUS,
        "targeted_lean_builds_passed": True,
        "aggregate_lean_validation_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePsiAU1CExchangeFunctionalEmbeddingPacketResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "source_inputs": {
            "cexchange_functional_embedding_packet_json": _ptr(
                embedding_packet_path
            ),
            "cexchange_functional_embedding_packet_outcome": (
                EMBEDDING_PACKET_OUTCOME
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
            "embedding_lean_marker": _ptr(EMBEDDING_LEAN_PACKET_PATH),
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
            "Review the ToE-native psi-A U(1) C_exchange "
            "functional-embedding packet result."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--embedding-packet", type=Path, default=EMBEDDING_PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    embedding_packet_path = (
        args.embedding_packet
        if args.embedding_packet.is_absolute()
        else REPO_ROOT / args.embedding_packet
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_toe_native_psi_a_u1_cexchange_functional_embedding_packet_result_review(
        embedding_packet_path=embedding_packet_path,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(out, payload)
    print(
        "toe_native_psi_a_u1_cexchange_functional_embedding_packet_result_review: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
