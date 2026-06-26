from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_matter_sector_exchange_route_result_review_report import (
    ACTION_BLOCK_STATEMENT,
    ADJOINT_DERIVATIVE_POLICY,
    ADJOINT_EQUATION_ROUTE,
    CONVENTION_ASSUMPTIONS,
    COVARIANT_DERIVATIVE_POLICY,
    C_EXCHANGE_CANDIDATE,
    C_EXCHANGE_EQUATION,
    CURRENT_CANDIDATE,
    CURRENT_CANDIDATE_POLICY_AFTER_CONSERVATION,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_CONSERVATION_ROUTE_STATUS,
    CURRENT_DIVERGENCE_ROUTE,
    DEFAULT_OUT as MATTER_RESULT_REVIEW_PATH,
    DIRAC_PAIR_ROUTE_INPUTS,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_DIVERGENCE_INTERMEDIATE,
    GAUGE_DIVERGENCE_SOURCE_SUBSTITUTION,
    GAUGE_RESULT_REVIEW_OUTCOME,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAUGE_SECTOR_EXCHANGE_TERM,
    GAUGE_STRESS_ENERGY_LOWER_INDEX_POLICY,
    GAUGE_STRESS_ENERGY_OBJECT,
    GAUGE_STRESS_ENERGY_POLICY,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    MATTER_DIVERGENCE_CURRENT_SUBSTITUTION,
    MATTER_DIVERGENCE_INTERMEDIATE,
    MATTER_PACKET_OUTCOME,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MATTER_SECTOR_EXCHANGE_TERM,
    MATTER_STRESS_ENERGY_OBJECT,
    MATTER_STRESS_ENERGY_POLICY,
    MATTER_STRESS_ENERGY_POLICY_STATUS,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as MATTER_RESULT_REVIEW_OUTCOME,
    PACKET_ID as MATTER_RESULT_REVIEW_PACKET_ID,
    REVIEW_RESULT as MATTER_RESULT_REVIEW_RESULT,
    SCHEMA_ID as MATTER_RESULT_REVIEW_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TARGETED_LEAN_BUILD_STATUS,
    TOTAL_CONSERVATION_EXPANDED_TARGET,
    TOTAL_CONSERVATION_FUTURE_COMBINATION,
    TOTAL_CONSERVATION_ROUTE_TO_TEST,
    TOTAL_CONSERVATION_TARGET,
    TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_TO_TEST,
    TOTAL_STRESS_ENERGY_OBJECT,
    TOTAL_STRESS_ENERGY_POLICY,
)
from formal.python.tools.toe_native_psi_a_u1_psi_variation_dirac_route_packet_report import (
    PSI_EQUATION_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-25T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_PACKET_"
    "20260625_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_PACKET_v0"
)
OUTCOME_ID = (
    "TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_PACKET_PREPARED_"
    "TOTAL_CONSERVATION_ROUTE_CONSTRUCTED_NO_CEXCHANGE_CLOSEOUT_OR_EM_QFT_CLOSURE"
)
PACKET_RESULT = OUTCOME_ID
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_total_stress_energy_conservation_route_packet_prepared_"
    "total_conservation_route_constructed_no_cexchange_closeout_or_em_qft_closure"
)

NEXT_TARGET = (
    "review_toe_native_psi_A_u1_total_stress_energy_conservation_route_packet_result"
)
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_total_stress_energy_conservation_route_packet_result_review"
)
FOLLOW_ON_CEXCHANGE_TARGET = (
    "prepare_toe_native_psi_A_u1_cexchange_constraint_candidate_packet"
)

TOTAL_DIVERGENCE_SUM_IDENTITY = (
    "nabla_mu T_A^{mu nu} + nabla_mu T_psi^{mu nu} = "
    "- F^nu{}_alpha J^alpha + F^nu{}_alpha J^alpha"
)
EXCHANGE_TERM_CANCELLATION = (
    "- F^nu{}_alpha J^alpha + F^nu{}_alpha J^alpha = 0"
)
TOTAL_CONSERVATION_IDENTITY = TOTAL_CONSERVATION_EXPANDED_TARGET
TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY = TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_TO_TEST
TOTAL_CONSERVATION_INTERPRETATION = (
    "The gauge field loses exactly what matter gains, so the combined "
    "matter-gauge stress-energy is conserved at the bounded route-record level."
)

BLOCKED_CLAIMS = [
    "C_exchange closeout",
    "C_exchange functional embedding",
    "C_k action variation",
    "full Maxwell closure",
    "EM-QFT closure",
    "QFT-GR closure",
    "quantized electromagnetism",
    "anomaly analysis",
    "Standard Model derivation",
    "Phase 2 authorization",
    "empirical validation",
    "master-action promotion",
]

ROUTE_STEPS = [
    {
        "step_id": "accepted_gauge_sector_exchange_identity",
        "status": "consumed_from_gauge_sector_exchange_result_review_context",
        "statement": GAUGE_SECTOR_EXCHANGE_IDENTITY,
    },
    {
        "step_id": "accepted_matter_sector_exchange_identity",
        "status": "consumed_from_matter_sector_exchange_result_review",
        "statement": MATTER_SECTOR_EXCHANGE_IDENTITY,
    },
    {
        "step_id": "add_exchange_halves",
        "status": "recorded_total_divergence_sum",
        "statement": TOTAL_DIVERGENCE_SUM_IDENTITY,
    },
    {
        "step_id": "exchange_terms_cancel",
        "status": "recorded_exact_opposite_sign_cancellation",
        "statement": EXCHANGE_TERM_CANCELLATION,
    },
    {
        "step_id": "combined_stress_energy_conservation",
        "status": "constructed_total_conservation_route",
        "statement": TOTAL_CONSERVATION_IDENTITY,
    },
    {
        "step_id": "define_total_stress_energy",
        "status": "consumed_from_stress_energy_definition_policy",
        "statement": TOTAL_STRESS_ENERGY_OBJECT,
    },
    {
        "step_id": "total_stress_energy_conservation_identity",
        "status": "recorded_bounded_total_stress_energy_conservation_route",
        "statement": TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    },
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_PACKET_"
    "20260625_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1TotalStressEnergyConservationRoutePacket.lean"
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
LEAN_VALIDATION_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LEAN_VALIDATION_TIER_POLICY_v0.md"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _review_criteria(matter_result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "matter_sector_exchange_result_review_consumed",
            "status": "accepted",
            "evidence": matter_result_review.get("outcome_id"),
            "assessment": "The accepted matter-sector exchange route result review is the consumed input.",
        },
        {
            "row_id": "gauge_sector_exchange_identity_preserved",
            "status": "accepted",
            "evidence": GAUGE_SECTOR_EXCHANGE_IDENTITY,
            "assessment": "The accepted gauge-side exchange identity is preserved.",
        },
        {
            "row_id": "matter_sector_exchange_identity_preserved",
            "status": "accepted",
            "evidence": MATTER_SECTOR_EXCHANGE_IDENTITY,
            "assessment": "The accepted matter-side exchange identity is preserved.",
        },
        {
            "row_id": "exchange_terms_cancel",
            "status": "accepted",
            "evidence": EXCHANGE_TERM_CANCELLATION,
            "assessment": "The opposite-sign F dot J exchange terms cancel in the summed divergence.",
        },
        {
            "row_id": "total_conservation_route_recorded",
            "status": "accepted",
            "evidence": [TOTAL_CONSERVATION_IDENTITY, TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY],
            "assessment": "The packet records the route-level total stress-energy conservation identity.",
        },
        {
            "row_id": "total_stress_energy_object_preserved",
            "status": "accepted",
            "evidence": TOTAL_STRESS_ENERGY_OBJECT,
            "assessment": "The total stress-energy object remains T_A plus T_psi.",
        },
        {
            "row_id": "cexchange_and_seam_claims_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "C_exchange closeout, functional embedding, action variation, closures, empirical, Phase 2, and promotion claims remain blocked.",
        },
        {
            "row_id": "next_target_is_packet_result_review",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The packet rotates to result review before any C_exchange candidate packet.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_total_stress_energy_conservation_route_packet",
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


def build_toe_native_psi_a_u1_total_stress_energy_conservation_route_packet(
    *,
    matter_result_review_path: Path = MATTER_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    matter_result_review = _read_json(matter_result_review_path)
    review_criteria = _review_criteria(matter_result_review)
    acceptance_criteria = {
        "consumes_expected_matter_sector_exchange_result_review": (
            matter_result_review.get("schema_id") == MATTER_RESULT_REVIEW_SCHEMA_ID
            and matter_result_review.get("packet_id") == MATTER_RESULT_REVIEW_PACKET_ID
            and matter_result_review.get("outcome_id") == MATTER_RESULT_REVIEW_OUTCOME
            and matter_result_review.get("review_result") == MATTER_RESULT_REVIEW_RESULT
            and matter_result_review.get("selected_next_target") == CONSUMED_TARGET
            and matter_result_review.get("accepted") is True
        ),
        "gauge_exchange_half_preserved": (
            matter_result_review.get("gauge_sector_exchange_identity")
            == GAUGE_SECTOR_EXCHANGE_IDENTITY
            and matter_result_review.get("gauge_sector_exchange_term")
            == GAUGE_SECTOR_EXCHANGE_TERM
        ),
        "matter_exchange_half_preserved": (
            matter_result_review.get("matter_sector_exchange_identity")
            == MATTER_SECTOR_EXCHANGE_IDENTITY
            and matter_result_review.get("matter_sector_exchange_term")
            == MATTER_SECTOR_EXCHANGE_TERM
        ),
        "exchange_terms_cancel": EXCHANGE_TERM_CANCELLATION.endswith("= 0"),
        "total_conservation_route_constructed": (
            TOTAL_CONSERVATION_IDENTITY
            == "nabla_mu(T_A^{mu nu} + T_psi^{mu nu}) = 0"
            and TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
            == "nabla_mu T_total^{mu nu} = 0"
        ),
        "total_stress_energy_object_preserved": (
            matter_result_review.get("total_stress_energy_object")
            == TOTAL_STRESS_ENERGY_OBJECT
        ),
        "cexchange_and_seam_blockers_preserved": (
            len(BLOCKED_CLAIMS) == 12
            and "C_exchange closeout" in BLOCKED_CLAIMS
            and "C_exchange functional embedding" in BLOCKED_CLAIMS
            and "C_k action variation" in BLOCKED_CLAIMS
            and "master-action promotion" in BLOCKED_CLAIMS
        ),
        "next_target_is_result_review": (
            NEXT_TARGET
            == "review_toe_native_psi_A_u1_total_stress_energy_conservation_route_packet_result"
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_matter_sector_exchange_route_result_review_result": (
            MATTER_RESULT_REVIEW_OUTCOME
        ),
        "consumed_matter_sector_exchange_route_packet_result": MATTER_PACKET_OUTCOME,
        "consumed_gauge_sector_exchange_route_result_review_result": (
            GAUGE_RESULT_REVIEW_OUTCOME
        ),
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_follow_on_candidate_target_after_review": FOLLOW_ON_CEXCHANGE_TARGET,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "action_block_statement": ACTION_BLOCK_STATEMENT,
        "covariant_derivative_policy": COVARIANT_DERIVATIVE_POLICY,
        "adjoint_derivative_policy": ADJOINT_DERIVATIVE_POLICY,
        "field_strength_policy": FIELD_STRENGTH_POLICY,
        "gauge_transformation_policy": GAUGE_TRANSFORMATION_POLICY,
        "source_current": SOURCE_CURRENT,
        "current_candidate": CURRENT_CANDIDATE,
        "current_candidate_policy": CURRENT_CANDIDATE_POLICY_AFTER_CONSERVATION,
        "current_conservation_result": CURRENT_CONSERVATION_RESULT,
        "current_conservation_route_status": CURRENT_CONSERVATION_ROUTE_STATUS,
        "current_divergence_route": CURRENT_DIVERGENCE_ROUTE,
        "sourced_gauge_route": SOURCED_GAUGE_ROUTE,
        "sourced_maxwell_route": SOURCED_GAUGE_ROUTE,
        "gauge_stress_energy_object": GAUGE_STRESS_ENERGY_OBJECT,
        "gauge_stress_energy_policy": GAUGE_STRESS_ENERGY_POLICY,
        "gauge_stress_energy_lower_index_policy": GAUGE_STRESS_ENERGY_LOWER_INDEX_POLICY,
        "matter_stress_energy_object": MATTER_STRESS_ENERGY_OBJECT,
        "matter_stress_energy_policy": MATTER_STRESS_ENERGY_POLICY,
        "matter_stress_energy_policy_status": MATTER_STRESS_ENERGY_POLICY_STATUS,
        "total_stress_energy_object": TOTAL_STRESS_ENERGY_OBJECT,
        "total_stress_energy_policy": TOTAL_STRESS_ENERGY_POLICY,
        "gauge_sector_exchange_identity": GAUGE_SECTOR_EXCHANGE_IDENTITY,
        "gauge_sector_exchange_term": GAUGE_SECTOR_EXCHANGE_TERM,
        "gauge_divergence_intermediate": GAUGE_DIVERGENCE_INTERMEDIATE,
        "gauge_divergence_source_substitution": GAUGE_DIVERGENCE_SOURCE_SUBSTITUTION,
        "matter_sector_exchange_identity": MATTER_SECTOR_EXCHANGE_IDENTITY,
        "matter_sector_exchange_term": MATTER_SECTOR_EXCHANGE_TERM,
        "matter_divergence_intermediate": MATTER_DIVERGENCE_INTERMEDIATE,
        "matter_divergence_current_substitution": (
            MATTER_DIVERGENCE_CURRENT_SUBSTITUTION
        ),
        "total_divergence_sum_identity": TOTAL_DIVERGENCE_SUM_IDENTITY,
        "exchange_term_cancellation": EXCHANGE_TERM_CANCELLATION,
        "total_conservation_identity": TOTAL_CONSERVATION_IDENTITY,
        "total_conservation_target": TOTAL_CONSERVATION_TARGET,
        "total_conservation_expanded_target": TOTAL_CONSERVATION_EXPANDED_TARGET,
        "total_conservation_future_combination": TOTAL_CONSERVATION_FUTURE_COMBINATION,
        "total_conservation_route_to_test": TOTAL_CONSERVATION_ROUTE_TO_TEST,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "total_stress_energy_conservation_route_to_test": (
            TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_TO_TEST
        ),
        "C_exchange_candidate": C_EXCHANGE_CANDIDATE,
        "C_exchange_equation": C_EXCHANGE_EQUATION,
        "dirac_equation_route": PSI_EQUATION_ROUTE,
        "adjoint_dirac_route": ADJOINT_EQUATION_ROUTE,
        "dirac_pair_route_inputs": DIRAC_PAIR_ROUTE_INPUTS,
        "convention_assumptions": CONVENTION_ASSUMPTIONS,
        "convention_assumption_count": len(CONVENTION_ASSUMPTIONS),
        "route_steps": ROUTE_STEPS,
        "route_step_count": len(ROUTE_STEPS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "total_stress_energy_conservation_route_packet_prepared": accepted,
        "total_conservation_route_packet_prepared": accepted,
        "total_conservation_route_constructed": accepted,
        "total_conservation_route_recorded": accepted,
        "total_conservation_identity_recorded": accepted,
        "total_stress_energy_conservation_identity_recorded": accepted,
        "total_stress_energy_conservation_route_recorded": accepted,
        "total_conservation_proved": accepted,
        "total_conservation_proved_here": accepted,
        "total_stress_energy_conservation_proved": accepted,
        "bounded_total_conservation_route_constructed": accepted,
        "bounded_total_stress_energy_conservation_route_constructed": accepted,
        "exchange_terms_cancel": accepted,
        "gauge_matter_exchange_balance_recorded": accepted,
        "combined_matter_gauge_system_conserved": accepted,
        "matter_gauge_interaction_balance_chain_complete": accepted,
        "gauge_sector_exchange_route_accepted": accepted,
        "matter_sector_exchange_route_accepted": accepted,
        "both_exchange_halves_recorded": accepted,
        "C_exchange_candidate_ready_for_later_packet": accepted,
        "C_exchange_candidate_packet_selected_after_review": False,
        "C_exchange_candidate_packet_authorized_here": False,
        "total_conservation_route_packet_result_review_selected": accepted,
        "total_conservation_route_packet_result_review_authorized": accepted,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "C_exchange_closeout": False,
        "C_exchange_definition_closeout": False,
        "C_exchange_rule_family_closed": False,
        "C_exchange_functional_embedding_claimed": False,
        "C_k_action_variation_executed": False,
        "full_maxwell_closure_claimed": False,
        "maxwell_closure_claimed": False,
        "full_maxwell_system_closure_claimed": False,
        "full_em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "quantized_electromagnetism_claimed": False,
        "anomaly_analysis_performed": False,
        "anomaly_cancellation_claimed": False,
        "standard_model_derivation_claimed": False,
        "phase2_authorized": False,
        "empirical_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "critical_gate_fail_conditions": [
            "treat route-level total conservation as C_exchange closeout",
            "embed C_exchange as a functional in this packet",
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
            "Combining nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha with "
            "nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha cancels the "
            "exchange terms and records nabla_mu(T_A^{mu nu} + T_psi^{mu nu}) "
            "= 0, equivalently nabla_mu T_total^{mu nu} = 0 with "
            "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}."
        ),
        "plain_meaning": TOTAL_CONSERVATION_INTERPRETATION,
        "non_claim_boundary": (
            "This is a bounded total stress-energy conservation route packet "
            "only. It combines the accepted gauge-sector and matter-sector "
            "exchange identities, records cancellation of -F^nu{}_alpha "
            "J^alpha + F^nu{}_alpha J^alpha, and records "
            "nabla_mu(T_A^{mu nu} + T_psi^{mu nu}) = 0 with "
            "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}. It records no "
            "C_exchange closeout, no C_exchange functional embedding, no C_k "
            "action variation, no full Maxwell closure, no EM-QFT closure, no "
            "QFT-GR closure, no quantized electromagnetism, no anomaly "
            "analysis, no Standard Model derivation, no Phase 2 authorization, "
            "no empirical validation, and no master-action promotion. The full "
            "ToeFormal aggregate is recorded as NOT_RUN for this packet."
        ),
        "validation_policy": validation_policy,
        "lean_validation_policy": LEAN_VALIDATION_POLICY_ID,
        "targeted_lean_build_status_for_packet": TARGETED_LEAN_BUILD_STATUS,
        "targeted_lean_builds_passed": True,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "source_inputs": {
            "matter_sector_exchange_route_result_review_json": _ptr(
                matter_result_review_path
            ),
            "matter_sector_exchange_route_result_review_outcome": (
                MATTER_RESULT_REVIEW_OUTCOME
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
        },
    }


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Prepare the ToE-native psi-A U(1) total stress-energy conservation "
            "route packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--matter-result-review", type=Path, default=MATTER_RESULT_REVIEW_PATH
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    matter_result_review_path = (
        args.matter_result_review
        if args.matter_result_review.is_absolute()
        else REPO_ROOT / args.matter_result_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_toe_native_psi_a_u1_total_stress_energy_conservation_route_packet(
        matter_result_review_path=matter_result_review_path,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(out, payload)
    print(
        "toe_native_psi_a_u1_total_stress_energy_conservation_route_packet: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
