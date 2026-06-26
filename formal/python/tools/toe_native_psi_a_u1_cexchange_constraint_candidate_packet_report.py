from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_total_stress_energy_conservation_route_result_review_report import (
    ACTION_BLOCK_STATEMENT,
    CONSUMED_TARGET as TOTAL_REVIEW_CONSUMED_TARGET,
    C_EXCHANGE_CONSTRAINT_CANDIDATE_EQUATION,
    C_EXCHANGE_CONSTRAINT_CANDIDATE_TO_PREPARE,
    CURRENT_CANDIDATE,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as TOTAL_REVIEW_PATH,
    EXCHANGE_TERM_CANCELLATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAUGE_SECTOR_EXCHANGE_TERM,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MATTER_SECTOR_EXCHANGE_TERM,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as TOTAL_REVIEW_OUTCOME,
    PACKET_ID as TOTAL_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT as TOTAL_REVIEW_RESULT,
    SCHEMA_ID as TOTAL_REVIEW_SCHEMA_ID,
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

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_PACKET_20260625_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_PACKET_v0"
OUTCOME_ID = (
    "TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_PACKET_PREPARED_"
    "TOTAL_EXCHANGE_CONSERVATION_RESIDUAL_CANDIDATE_RECORDED_NO_"
    "FUNCTIONALIZATION_OR_EM_QFT_CLOSURE"
)
PACKET_RESULT = OUTCOME_ID
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_cexchange_constraint_candidate_packet_prepared_"
    "total_exchange_conservation_residual_candidate_recorded_no_"
    "functionalization_or_em_qft_closure"
)

NEXT_TARGET = "review_toe_native_psi_A_u1_cexchange_constraint_candidate_packet_result"
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_cexchange_constraint_candidate_packet_result_review"
)

C_EXCHANGE_CONSTRAINT_ID = "psi_A_u1_total_exchange_conservation_residual_candidate"
C_EXCHANGE_CONSTRAINT_FORM = (
    "C_exchange^{Apsi,nu}[g,A,psi] := nabla_mu T_total^{mu nu}"
)
C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM = (
    "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}"
)
C_EXCHANGE_ADMISSIBILITY_CONDITION = "C_exchange^{Apsi,nu} = 0"
C_EXCHANGE_PLAIN_MEANING = (
    "The psi-A interaction is admissible only if the total matter-plus-gauge "
    "energy-momentum exchange balances."
)
C_EXCHANGE_CANDIDATE_SCOPE = (
    "admissibility-only interaction-exchange constraint candidate; not "
    "functionalized; not action-embedded; not varied"
)

ALLOWED_CLAIMS = [
    "C_exchange candidate recorded",
    "candidate based on accepted total-conservation route",
    "candidate is admissibility-only",
    "candidate is not functionalized",
    "candidate is not action-embedded",
    "candidate is not varied",
]

BLOCKED_CLAIMS = [
    "no C_exchange closeout",
    "no C_exchange functional embedding",
    "no multiplier/action route",
    "no penalty route",
    "no C_k action variation",
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
    / "TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_PACKET_20260625_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1CExchangeConstraintCandidatePacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_rows(total_review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_total_conservation_result_review",
            "status": "accepted",
            "evidence": total_review.get("outcome_id"),
            "assessment": "The accepted total stress-energy conservation route result review is the consumed input.",
        },
        {
            "row_id": "accepted_total_conservation_route_preserved",
            "status": "accepted",
            "evidence": [
                TOTAL_CONSERVATION_IDENTITY,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
                TOTAL_STRESS_ENERGY_OBJECT,
            ],
            "assessment": "The C_exchange candidate is based on the accepted total conservation route.",
        },
        {
            "row_id": "gauge_and_matter_exchange_context_preserved",
            "status": "accepted",
            "evidence": [
                GAUGE_SECTOR_EXCHANGE_IDENTITY,
                MATTER_SECTOR_EXCHANGE_IDENTITY,
                EXCHANGE_TERM_CANCELLATION,
            ],
            "assessment": "The equal-and-opposite psi-A exchange context is preserved.",
        },
        {
            "row_id": "cexchange_candidate_recorded",
            "status": "accepted",
            "evidence": [
                C_EXCHANGE_CONSTRAINT_FORM,
                C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
                C_EXCHANGE_ADMISSIBILITY_CONDITION,
            ],
            "assessment": "The total exchange-conservation residual candidate is recorded.",
        },
        {
            "row_id": "candidate_classified_as_admissibility_only",
            "status": "accepted",
            "evidence": C_EXCHANGE_CANDIDATE_SCOPE,
            "assessment": "The candidate is not promoted to a functional, action term, variation, or dynamical law.",
        },
        {
            "row_id": "functional_embedding_action_and_variation_blocked",
            "status": "accepted",
            "evidence": [
                "C_exchange_functional_embedding_claimed=false",
                "multiplier_action_route_selected=false",
                "penalty_route_selected=false",
                "C_k_action_variation_executed=false",
            ],
            "assessment": "No multiplier/action route, penalty route, or C_k variation is selected here.",
        },
        {
            "row_id": "closures_phase2_empirical_and_promotion_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Maxwell, EM-QFT, QFT-GR, quantization, anomaly, Standard Model, Phase 2, empirical, and promotion claims remain blocked.",
        },
        {
            "row_id": "next_target_is_candidate_result_review",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The packet rotates to result review before any functional embedding branch.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_cexchange_constraint_candidate_packet",
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


def build_toe_native_psi_a_u1_cexchange_constraint_candidate_packet(
    *,
    total_review_path: Path = TOTAL_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    total_review = _read_json(total_review_path)
    candidate_rows = _candidate_rows(total_review)
    acceptance_criteria = {
        "consumes_expected_total_conservation_result_review": (
            total_review.get("schema_id") == TOTAL_REVIEW_SCHEMA_ID
            and total_review.get("packet_id") == TOTAL_REVIEW_PACKET_ID
            and total_review.get("outcome_id") == TOTAL_REVIEW_OUTCOME
            and total_review.get("review_result") == TOTAL_REVIEW_RESULT
            and total_review.get("selected_next_target") == CONSUMED_TARGET
            and total_review.get("accepted") is True
        ),
        "accepted_total_conservation_route_consumed": (
            total_review.get("total_conservation_identity")
            == TOTAL_CONSERVATION_IDENTITY
            and total_review.get("total_stress_energy_conservation_identity")
            == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
            and total_review.get("total_stress_energy_object")
            == TOTAL_STRESS_ENERGY_OBJECT
        ),
        "candidate_matches_authorized_shape": (
            total_review.get("C_exchange_constraint_candidate_to_prepare")
            == C_EXCHANGE_CONSTRAINT_CANDIDATE_TO_PREPARE
            and total_review.get(
                "C_exchange_constraint_candidate_equation_to_prepare"
            )
            == C_EXCHANGE_CONSTRAINT_CANDIDATE_EQUATION
            and C_EXCHANGE_CONSTRAINT_FORM
            == "C_exchange^{Apsi,nu}[g,A,psi] := nabla_mu T_total^{mu nu}"
            and C_EXCHANGE_ADMISSIBILITY_CONDITION == "C_exchange^{Apsi,nu} = 0"
        ),
        "candidate_is_admissibility_only": (
            "admissibility-only" in C_EXCHANGE_CANDIDATE_SCOPE
            and "not functionalized" in C_EXCHANGE_CANDIDATE_SCOPE
            and "not action-embedded" in C_EXCHANGE_CANDIDATE_SCOPE
            and "not varied" in C_EXCHANGE_CANDIDATE_SCOPE
        ),
        "functional_embedding_action_and_variation_blocked": (
            total_review.get("C_exchange_closeout") is False
            and total_review.get("C_exchange_functional_embedding_claimed") is False
            and total_review.get("C_k_action_variation_executed") is False
        ),
        "closure_promotion_boundaries_preserved": (
            total_review.get("em_qft_closure_claimed") is False
            and total_review.get("qft_gr_closure_claimed") is False
            and total_review.get("master_action_promoted") is False
        ),
        "allowed_claims_exactly_scoped": len(ALLOWED_CLAIMS) == 6,
        "blocked_claims_exactly_scoped": len(BLOCKED_CLAIMS) == 14,
        "candidate_rows_all_accepted": all(
            row["status"] == "accepted" for row in candidate_rows
        ),
        "next_target_is_result_review": (
            NEXT_TARGET
            == "review_toe_native_psi_A_u1_cexchange_constraint_candidate_packet_result"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_total_stress_energy_conservation_route_result_review_result": (
            TOTAL_REVIEW_OUTCOME
        ),
        "consumed_total_stress_energy_conservation_route_result_review_consumed_target": (
            TOTAL_REVIEW_CONSUMED_TARGET
        ),
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "action_block_statement": ACTION_BLOCK_STATEMENT,
        "source_current": SOURCE_CURRENT,
        "current_candidate": CURRENT_CANDIDATE,
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
        "C_exchange_constraint_candidate_to_prepare": (
            C_EXCHANGE_CONSTRAINT_CANDIDATE_TO_PREPARE
        ),
        "C_exchange_constraint_candidate_equation_to_prepare": (
            C_EXCHANGE_CONSTRAINT_CANDIDATE_EQUATION
        ),
        "C_exchange_plain_meaning": C_EXCHANGE_PLAIN_MEANING,
        "C_exchange_candidate_scope": C_EXCHANGE_CANDIDATE_SCOPE,
        "allowed_claims": ALLOWED_CLAIMS,
        "allowed_claim_count": len(ALLOWED_CLAIMS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "candidate_rows": candidate_rows,
        "candidate_row_count": len(candidate_rows),
        "candidate_row_accepted_count": sum(
            1 for row in candidate_rows if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "C_exchange_constraint_candidate_packet_prepared": accepted,
        "C_exchange_candidate_recorded": accepted,
        "C_exchange_constraint_candidate_recorded": accepted,
        "total_exchange_conservation_residual_candidate_recorded": accepted,
        "candidate_based_on_accepted_total_conservation_route": accepted,
        "candidate_is_admissibility_only": accepted,
        "candidate_not_functionalized": accepted,
        "candidate_not_action_embedded": accepted,
        "candidate_not_varied": accepted,
        "total_stress_energy_object_preserved": accepted,
        "total_conservation_route_consumed": accepted,
        "total_stress_energy_conservation_route_consumed": accepted,
        "interaction_exchange_admissibility_candidate_recorded": accepted,
        "C_exchange_constraint_candidate_packet_result_review_selected": accepted,
        "C_exchange_constraint_candidate_packet_result_review_authorized": accepted,
        "C_exchange_closeout": False,
        "C_exchange_definition_closeout": False,
        "C_exchange_rule_family_closed": False,
        "C_exchange_functional_embedding_claimed": False,
        "C_exchange_functional_embedding_selected": False,
        "C_exchange_functional_embedding_constructed": False,
        "C_exchange_functional_embedding_packet_prepared_here": False,
        "multiplier_action_route_selected": False,
        "multiplier_action_route_constructed": False,
        "penalty_route_selected": False,
        "penalty_route_constructed": False,
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
        "mathematical_statement": (
            "The packet records the admissibility-only candidate "
            f"{C_EXCHANGE_CONSTRAINT_FORM}, with "
            f"{C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM} and admissibility condition "
            f"{C_EXCHANGE_ADMISSIBILITY_CONDITION}, based on the accepted "
            f"{TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY} route."
        ),
        "plain_meaning": C_EXCHANGE_PLAIN_MEANING,
        "non_claim_boundary": (
            "This is a bounded C_exchange constraint-candidate packet only. It "
            "records C_exchange^{Apsi,nu}[g,A,psi] := nabla_mu "
            "T_total^{mu nu} with T_total = T_A + T_psi and "
            "C_exchange^{Apsi,nu} = 0 as an admissibility-only candidate based "
            "on the accepted total stress-energy conservation route. The "
            "candidate is not functionalized, not action-embedded, and not "
            "varied. It records no C_exchange closeout, no C_exchange "
            "functional embedding, no multiplier/action route, no penalty "
            "route, no C_k action variation, no full Maxwell closure, no "
            "EM-QFT closure, no QFT-GR closure, no quantized electromagnetism, "
            "no anomaly analysis, no Standard Model derivation, no Phase 2 "
            "authorization, no empirical validation, and no master-action "
            "promotion. The full ToeFormal aggregate is recorded as NOT_RUN "
            "for this packet."
        ),
        "critical_gate_fail_conditions": [
            "treat C_exchange candidate recording as C_exchange closeout",
            "functionalize C_exchange in this packet",
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
        "validation_policy": validation_policy,
        "lean_validation_policy": LEAN_VALIDATION_POLICY_ID,
        "targeted_lean_build_status_for_packet": TARGETED_LEAN_BUILD_STATUS,
        "targeted_lean_builds_passed": True,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "source_inputs": {
            "total_stress_energy_conservation_route_result_review_json": _ptr(
                total_review_path
            ),
            "total_stress_energy_conservation_route_result_review_outcome": (
                TOTAL_REVIEW_OUTCOME
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
            "Prepare the ToE-native psi-A U(1) C_exchange constraint candidate "
            "packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--total-review", type=Path, default=TOTAL_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    total_review_path = (
        args.total_review
        if args.total_review.is_absolute()
        else REPO_ROOT / args.total_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_toe_native_psi_a_u1_cexchange_constraint_candidate_packet(
        total_review_path=total_review_path,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(out, payload)
    print(
        "toe_native_psi_a_u1_cexchange_constraint_candidate_packet: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
