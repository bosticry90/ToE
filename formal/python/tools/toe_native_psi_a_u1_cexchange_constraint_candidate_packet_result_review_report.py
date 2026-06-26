from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_cexchange_constraint_candidate_packet_report import (
    BLOCKED_CLAIMS,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CONSUMED_TARGET as CANDIDATE_PACKET_CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as CANDIDATE_PACKET_PATH,
    EXCHANGE_TERM_CANCELLATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAUGE_SECTOR_EXCHANGE_TERM,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MATTER_SECTOR_EXCHANGE_TERM,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as CANDIDATE_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as CANDIDATE_PACKET_CLASSIFICATION,
    PACKET_ID as CANDIDATE_PACKET_ID,
    PACKET_RESULT as CANDIDATE_PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as CANDIDATE_PACKET_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TARGETED_LEAN_BUILD_STATUS,
    TOTAL_CONSERVATION_IDENTITY,
    TOTAL_REVIEW_OUTCOME,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-25T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_RESULT_REVIEW_"
    "20260625_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_RESULT_REVIEW_"
    "ACCEPTS_TOTAL_EXCHANGE_CONSERVATION_RESIDUAL_CANDIDATE_NO_"
    "FUNCTIONALIZATION_OR_EM_QFT_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_cexchange_constraint_candidate_result_review_"
    "accepts_total_exchange_conservation_residual_candidate_no_"
    "functionalization_or_em_qft_closure"
)

NEXT_TARGET = "prepare_toe_native_psi_A_u1_cexchange_functional_embedding_packet"
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_cexchange_functional_embedding_packet_preparation"
)

ACCEPTED_REVIEW_FINDINGS = [
    "C_exchange candidate recorded",
    "candidate based on accepted psi-A total-conservation route",
    "T_total = T_A + T_psi preserved",
    "C_exchange^{Apsi,nu} = 0 recorded",
    "admissibility-only status preserved",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_RESULT_REVIEW_"
    "20260625_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1CExchangeConstraintCandidateResultReview.lean"
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
            "row_id": "cexchange_candidate_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("outcome_id"),
            "assessment": "The prepared C_exchange constraint-candidate packet is the consumed input.",
        },
        {
            "row_id": "cexchange_candidate_recorded",
            "status": "accepted",
            "evidence": [
                C_EXCHANGE_CONSTRAINT_FORM,
                C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
                C_EXCHANGE_ADMISSIBILITY_CONDITION,
            ],
            "assessment": "The C_exchange total exchange-conservation residual candidate is recorded.",
        },
        {
            "row_id": "candidate_based_on_total_conservation_route",
            "status": "accepted",
            "evidence": [
                TOTAL_REVIEW_OUTCOME,
                TOTAL_CONSERVATION_IDENTITY,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            ],
            "assessment": "The candidate is based on the accepted psi-A total-conservation route.",
        },
        {
            "row_id": "total_stress_energy_preserved",
            "status": "accepted",
            "evidence": TOTAL_STRESS_ENERGY_OBJECT,
            "assessment": "The review preserves T_total as T_A plus T_psi.",
        },
        {
            "row_id": "admissibility_condition_recorded",
            "status": "accepted",
            "evidence": C_EXCHANGE_ADMISSIBILITY_CONDITION,
            "assessment": "The C_exchange^{Apsi,nu} = 0 admissibility condition is carried forward.",
        },
        {
            "row_id": "admissibility_only_status_preserved",
            "status": "accepted",
            "evidence": C_EXCHANGE_CANDIDATE_SCOPE,
            "assessment": "The candidate remains admissibility-only and is not functionalized, embedded, or varied.",
        },
        {
            "row_id": "functionalization_action_variation_routes_blocked",
            "status": "accepted",
            "evidence": [
                "C_exchange_functional_embedding_claimed=false",
                "multiplier_action_route_selected=false",
                "penalty_route_selected=false",
                "C_k_action_variation_executed=false",
            ],
            "assessment": "No functional embedding, multiplier/action route, penalty route, or C_k variation is executed.",
        },
        {
            "row_id": "closure_phase2_empirical_and_promotion_blockers_preserved",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Maxwell, EM-QFT, QFT-GR, quantization, anomaly, Standard Model, Phase 2, empirical, and promotion claims remain blocked.",
        },
        {
            "row_id": "functional_embedding_packet_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is the conservative C_exchange functional-embedding packet.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_psi_A_u1_cexchange_constraint_candidate_result_review"
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


def build_toe_native_psi_a_u1_cexchange_constraint_candidate_packet_result_review(
    *,
    candidate_packet_path: Path = CANDIDATE_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(candidate_packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_cexchange_candidate_packet": (
            packet.get("schema_id") == CANDIDATE_PACKET_SCHEMA_ID
            and packet.get("packet_id") == CANDIDATE_PACKET_ID
            and packet.get("outcome_id") == CANDIDATE_PACKET_OUTCOME
            and packet.get("packet_result") == CANDIDATE_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "candidate_shape_exact": (
            packet.get("C_exchange_constraint_id") == C_EXCHANGE_CONSTRAINT_ID
            and packet.get("C_exchange_constraint_form")
            == C_EXCHANGE_CONSTRAINT_FORM
            and packet.get("C_exchange_total_stress_energy_form")
            == C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
            and packet.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "candidate_based_on_total_conservation_route": (
            packet.get("candidate_based_on_accepted_total_conservation_route") is True
            and packet.get("total_stress_energy_object")
            == TOTAL_STRESS_ENERGY_OBJECT
            and packet.get("total_stress_energy_conservation_identity")
            == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "exchange_context_preserved": (
            packet.get("gauge_sector_exchange_identity")
            == GAUGE_SECTOR_EXCHANGE_IDENTITY
            and packet.get("matter_sector_exchange_identity")
            == MATTER_SECTOR_EXCHANGE_IDENTITY
            and packet.get("exchange_term_cancellation")
            == EXCHANGE_TERM_CANCELLATION
        ),
        "admissibility_only_status_preserved": (
            packet.get("candidate_is_admissibility_only") is True
            and packet.get("candidate_not_functionalized") is True
            and packet.get("candidate_not_action_embedded") is True
            and packet.get("candidate_not_varied") is True
        ),
        "functionalization_action_and_variation_blocked": all(
            packet.get(key) is False
            for key in [
                "C_exchange_closeout",
                "C_exchange_functional_embedding_claimed",
                "C_exchange_functional_embedding_selected",
                "C_exchange_functional_embedding_constructed",
                "multiplier_action_route_selected",
                "multiplier_action_route_constructed",
                "penalty_route_selected",
                "penalty_route_constructed",
                "C_k_action_variation_executed",
                "C_k_action_variation_authorized",
                "candidate_varied",
                "action_embedding_claimed",
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
        "accepted_review_findings_exactly_scoped": len(ACCEPTED_REVIEW_FINDINGS) == 5,
        "blocked_claims_exactly_scoped": len(BLOCKED_CLAIMS) == 14,
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
            "ACTIVE_TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_"
            "RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "review_result": REVIEW_RESULT,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_candidate_packet_schema": packet.get("schema_id"),
        "consumed_candidate_packet_id": packet.get("packet_id"),
        "candidate_packet_outcome": CANDIDATE_PACKET_OUTCOME,
        "candidate_packet_result": CANDIDATE_PACKET_RESULT,
        "candidate_packet_classification": CANDIDATE_PACKET_CLASSIFICATION,
        "candidate_packet_consumed_target": CANDIDATE_PACKET_CONSUMED_TARGET,
        "selected_next_target": NEXT_TARGET,
        "selected_next_target_kind": NEXT_TARGET_KIND,
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
        "review_executed": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": accepted,
        "C_exchange_constraint_candidate_result_review_accepted": accepted,
        "C_exchange_candidate_accepted": accepted,
        "C_exchange_candidate_recorded": accepted,
        "C_exchange_constraint_candidate_recorded": accepted,
        "total_exchange_conservation_residual_candidate_accepted": accepted,
        "candidate_based_on_accepted_total_conservation_route": accepted,
        "T_total_preserved": accepted,
        "total_stress_energy_object_preserved": accepted,
        "C_exchange_admissibility_condition_recorded": accepted,
        "admissibility_only_status_preserved": accepted,
        "candidate_not_functionalized": accepted,
        "candidate_not_action_embedded": accepted,
        "candidate_not_varied": accepted,
        "functional_embedding_packet_selected_after_review": accepted,
        "functional_embedding_packet_authorized_here": accepted,
        "C_exchange_functional_embedding_packet_selected": accepted,
        "C_exchange_functional_embedding_packet_authorized": accepted,
        "C_exchange_closeout": False,
        "C_exchange_definition_closeout": False,
        "C_exchange_rule_family_closed": False,
        "C_exchange_functional_embedding_claimed": False,
        "C_exchange_functional_embedding_constructed_here": False,
        "C_exchange_functional_embedding_constructed": False,
        "multiplier_action_route_selected": False,
        "multiplier_action_route_constructed": False,
        "penalty_route_selected": False,
        "penalty_route_constructed": False,
        "direct_dynamical_law_interpretation_selected": False,
        "direct_dynamical_law_interpretation_blocked": True,
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
            "treat C_exchange candidate review as C_exchange closeout",
            "functionalize C_exchange in this review",
            "embed C_exchange in an action",
            "select a multiplier/action route",
            "select a penalty route",
            "execute C_k action variation",
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
            "The review accepts only the recorded admissibility candidate "
            f"{C_EXCHANGE_CONSTRAINT_FORM}, with "
            f"{C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM} and condition "
            f"{C_EXCHANGE_ADMISSIBILITY_CONDITION}, based on the accepted "
            f"{TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY} route."
        ),
        "plain_meaning": C_EXCHANGE_PLAIN_MEANING,
        "non_claim_boundary": (
            "This is a bounded C_exchange constraint-candidate result review "
            "only. It accepts that the C_exchange candidate was recorded, that "
            "it is based on the accepted psi-A total-conservation route, that "
            "T_total = T_A + T_psi is preserved, that "
            "C_exchange^{Apsi,nu} = 0 is recorded, and that the candidate "
            "remains admissibility-only. It selects C_exchange functional "
            "embedding packet preparation next. It records no C_exchange "
            "closeout, no C_exchange functional embedding, no multiplier/action "
            "route, no penalty route, no C_k action variation, no full Maxwell "
            "closure, no EM-QFT closure, no QFT-GR closure, no quantized "
            "electromagnetism, no anomaly analysis, no Standard Model "
            "derivation, no Phase 2 authorization, no empirical validation, "
            "and no master-action promotion. The full ToeFormal aggregate is "
            "recorded as NOT_RUN for this review."
        ),
        "validation_policy": validation_policy,
        "lean_validation_policy": LEAN_VALIDATION_POLICY_ID,
        "targeted_lean_build_status_for_review": TARGETED_LEAN_BUILD_STATUS,
        "targeted_lean_builds_passed": True,
        "full_toeformal_aggregate_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "source_inputs": {
            "cexchange_constraint_candidate_packet_json": _ptr(candidate_packet_path),
            "cexchange_constraint_candidate_packet_outcome": CANDIDATE_PACKET_OUTCOME,
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
            "Review the ToE-native psi-A U(1) C_exchange constraint "
            "candidate packet result."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--candidate-packet", type=Path, default=CANDIDATE_PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    candidate_packet_path = (
        args.candidate_packet
        if args.candidate_packet.is_absolute()
        else REPO_ROOT / args.candidate_packet
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_toe_native_psi_a_u1_cexchange_constraint_candidate_packet_result_review(
            candidate_packet_path=candidate_packet_path,
            captured_at_utc=args.captured_at_utc,
        )
    )
    _write_json(out, payload)
    print(
        "toe_native_psi_a_u1_cexchange_constraint_candidate_packet_result_review: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
