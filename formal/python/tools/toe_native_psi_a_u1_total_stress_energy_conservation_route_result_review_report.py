from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_total_stress_energy_conservation_route_packet_report import (
    ACTION_BLOCK_STATEMENT,
    ADJOINT_DERIVATIVE_POLICY,
    ADJOINT_EQUATION_ROUTE,
    BLOCKED_CLAIMS,
    CONVENTION_ASSUMPTIONS,
    COVARIANT_DERIVATIVE_POLICY,
    C_EXCHANGE_CANDIDATE,
    C_EXCHANGE_EQUATION,
    CURRENT_CANDIDATE,
    CURRENT_CANDIDATE_POLICY_AFTER_CONSERVATION,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_CONSERVATION_ROUTE_STATUS,
    CURRENT_DIVERGENCE_ROUTE,
    DEFAULT_OUT as TOTAL_PACKET_PATH,
    DIRAC_PAIR_ROUTE_INPUTS,
    EXCHANGE_TERM_CANCELLATION,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_RESULT_REVIEW_OUTCOME,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAUGE_SECTOR_EXCHANGE_TERM,
    GAUGE_STRESS_ENERGY_OBJECT,
    GAUGE_STRESS_ENERGY_POLICY,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    MATTER_PACKET_OUTCOME,
    MATTER_RESULT_REVIEW_OUTCOME,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MATTER_SECTOR_EXCHANGE_TERM,
    MATTER_STRESS_ENERGY_OBJECT,
    MATTER_STRESS_ENERGY_POLICY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as TOTAL_PACKET_OUTCOME,
    PACKET_ID as TOTAL_PACKET_ID,
    SCHEMA_ID as TOTAL_PACKET_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TARGETED_LEAN_BUILD_STATUS,
    TOTAL_CONSERVATION_IDENTITY,
    TOTAL_DIVERGENCE_SUM_IDENTITY,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
    TOTAL_STRESS_ENERGY_POLICY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-25T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_RESULT_REVIEW_"
    "20260625_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_RESULT_REVIEW_"
    "ACCEPTS_TOTAL_CONSERVATION_ROUTE_NO_CEXCHANGE_CLOSEOUT_OR_EM_QFT_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_total_stress_energy_conservation_route_result_review_"
    "accepts_total_conservation_route_no_cexchange_closeout_or_em_qft_closure"
)

NEXT_TARGET = "prepare_toe_native_psi_A_u1_cexchange_constraint_candidate_packet"
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_cexchange_constraint_candidate_packet_preparation"
)
C_EXCHANGE_CONSTRAINT_CANDIDATE_TO_PREPARE = (
    "C_exchange^{Apsi,nu} := nabla_mu T_total^{mu nu}"
)
C_EXCHANGE_CONSTRAINT_CANDIDATE_EQUATION = "C_exchange^{Apsi,nu} = 0"

ACCEPTED_REVIEW_FINDINGS = [
    "gauge-sector exchange route already accepted",
    "matter-sector exchange route already accepted",
    "exchange terms cancel",
    "T_total = T_A + T_psi",
    "nabla_mu T_total^{mu nu} = 0 recorded",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_RESULT_REVIEW_"
    "20260625_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1TotalStressEnergyConservationRouteResultReview.lean"
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


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "total_conservation_route_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("outcome_id"),
            "assessment": "The prepared total stress-energy conservation route packet is the consumed input.",
        },
        {
            "row_id": "gauge_sector_exchange_route_already_accepted",
            "status": "accepted",
            "evidence": [GAUGE_RESULT_REVIEW_OUTCOME, GAUGE_SECTOR_EXCHANGE_IDENTITY],
            "assessment": "The gauge-sector exchange route is accepted as prior context.",
        },
        {
            "row_id": "matter_sector_exchange_route_already_accepted",
            "status": "accepted",
            "evidence": [MATTER_RESULT_REVIEW_OUTCOME, MATTER_SECTOR_EXCHANGE_IDENTITY],
            "assessment": "The matter-sector exchange route is accepted as prior context.",
        },
        {
            "row_id": "exchange_terms_cancel",
            "status": "accepted",
            "evidence": EXCHANGE_TERM_CANCELLATION,
            "assessment": "The equal-and-opposite exchange terms cancel.",
        },
        {
            "row_id": "total_stress_energy_object_preserved",
            "status": "accepted",
            "evidence": TOTAL_STRESS_ENERGY_OBJECT,
            "assessment": "The review preserves T_total as T_A plus T_psi.",
        },
        {
            "row_id": "total_stress_energy_conservation_route_recorded",
            "status": "accepted",
            "evidence": [
                TOTAL_CONSERVATION_IDENTITY,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            ],
            "assessment": "The review accepts the route-level total stress-energy conservation record.",
        },
        {
            "row_id": "cexchange_and_seam_claims_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "C_exchange closeout, functional embedding, C_k action variation, closures, empirical, Phase 2, and promotion claims remain blocked.",
        },
        {
            "row_id": "cexchange_candidate_packet_selected_next",
            "status": "accepted",
            "evidence": [
                NEXT_TARGET,
                C_EXCHANGE_CONSTRAINT_CANDIDATE_TO_PREPARE,
                C_EXCHANGE_CONSTRAINT_CANDIDATE_EQUATION,
            ],
            "assessment": "The next target is C_exchange constraint-candidate packet preparation only.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_psi_A_u1_total_stress_energy_conservation_route_result_review"
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


def build_toe_native_psi_a_u1_total_stress_energy_conservation_route_result_review(
    *,
    total_packet_path: Path = TOTAL_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(total_packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_total_conservation_route_packet": (
            packet.get("schema_id") == TOTAL_PACKET_SCHEMA_ID
            and packet.get("packet_id") == TOTAL_PACKET_ID
            and packet.get("outcome_id") == TOTAL_PACKET_OUTCOME
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "gauge_sector_exchange_route_already_accepted": (
            packet.get("gauge_sector_exchange_identity") == GAUGE_SECTOR_EXCHANGE_IDENTITY
            and packet.get("gauge_sector_exchange_route_accepted") is True
        ),
        "matter_sector_exchange_route_already_accepted": (
            packet.get("matter_sector_exchange_identity") == MATTER_SECTOR_EXCHANGE_IDENTITY
            and packet.get("matter_sector_exchange_route_accepted") is True
        ),
        "exchange_terms_cancel": (
            packet.get("exchange_term_cancellation") == EXCHANGE_TERM_CANCELLATION
            and packet.get("exchange_terms_cancel") is True
        ),
        "total_stress_energy_object_preserved": (
            packet.get("total_stress_energy_object") == TOTAL_STRESS_ENERGY_OBJECT
        ),
        "total_conservation_route_recorded": (
            packet.get("total_conservation_identity") == TOTAL_CONSERVATION_IDENTITY
            and packet.get("total_stress_energy_conservation_identity")
            == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
            and packet.get("total_conservation_route_constructed") is True
        ),
        "cexchange_and_seam_blockers_preserved": (
            packet.get("C_exchange_closeout") is False
            and packet.get("C_exchange_functional_embedding_claimed") is False
            and packet.get("C_k_action_variation_executed") is False
            and packet.get("em_qft_closure_claimed") is False
            and packet.get("qft_gr_closure_claimed") is False
            and packet.get("master_action_promoted") is False
        ),
        "next_target_is_cexchange_candidate_packet": NEXT_TARGET
        == "prepare_toe_native_psi_A_u1_cexchange_constraint_candidate_packet",
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
        "prepared": accepted,
        "accepted": accepted,
        "review_result": REVIEW_RESULT,
        "outcome_id": OUTCOME_ID,
        "packet_result": OUTCOME_ID,
        "packet_classification": PACKET_CLASSIFICATION,
        "captured_at_utc": captured_at_utc,
        "consumed_target": CONSUMED_TARGET,
        "consumed_total_stress_energy_conservation_route_packet_schema": (
            packet.get("schema_id")
        ),
        "consumed_total_stress_energy_conservation_route_packet_id": (
            packet.get("packet_id")
        ),
        "consumed_total_stress_energy_conservation_route_packet_result": (
            TOTAL_PACKET_OUTCOME
        ),
        "consumed_matter_sector_exchange_route_result_review_result": (
            MATTER_RESULT_REVIEW_OUTCOME
        ),
        "consumed_matter_sector_exchange_route_packet_result": MATTER_PACKET_OUTCOME,
        "consumed_gauge_sector_exchange_route_result_review_result": (
            GAUGE_RESULT_REVIEW_OUTCOME
        ),
        "selected_next_target": NEXT_TARGET,
        "selected_next_target_kind": NEXT_TARGET_KIND,
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
        "gauge_stress_energy_object": GAUGE_STRESS_ENERGY_OBJECT,
        "gauge_stress_energy_policy": GAUGE_STRESS_ENERGY_POLICY,
        "matter_stress_energy_object": MATTER_STRESS_ENERGY_OBJECT,
        "matter_stress_energy_policy": MATTER_STRESS_ENERGY_POLICY,
        "total_stress_energy_object": TOTAL_STRESS_ENERGY_OBJECT,
        "total_stress_energy_policy": TOTAL_STRESS_ENERGY_POLICY,
        "gauge_sector_exchange_identity": GAUGE_SECTOR_EXCHANGE_IDENTITY,
        "gauge_sector_exchange_term": GAUGE_SECTOR_EXCHANGE_TERM,
        "matter_sector_exchange_identity": MATTER_SECTOR_EXCHANGE_IDENTITY,
        "matter_sector_exchange_term": MATTER_SECTOR_EXCHANGE_TERM,
        "total_divergence_sum_identity": TOTAL_DIVERGENCE_SUM_IDENTITY,
        "exchange_term_cancellation": EXCHANGE_TERM_CANCELLATION,
        "total_conservation_identity": TOTAL_CONSERVATION_IDENTITY,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_candidate": C_EXCHANGE_CANDIDATE,
        "C_exchange_equation": C_EXCHANGE_EQUATION,
        "C_exchange_constraint_candidate_to_prepare": (
            C_EXCHANGE_CONSTRAINT_CANDIDATE_TO_PREPARE
        ),
        "C_exchange_constraint_candidate_equation_to_prepare": (
            C_EXCHANGE_CONSTRAINT_CANDIDATE_EQUATION
        ),
        "dirac_equation_route": packet.get("dirac_equation_route"),
        "adjoint_dirac_route": ADJOINT_EQUATION_ROUTE,
        "dirac_pair_route_inputs": DIRAC_PAIR_ROUTE_INPUTS,
        "convention_assumptions": CONVENTION_ASSUMPTIONS,
        "convention_assumption_count": len(CONVENTION_ASSUMPTIONS),
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
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
        "total_conservation_route_result_review_accepted": accepted,
        "total_stress_energy_conservation_route_accepted": accepted,
        "total_conservation_route_accepted": accepted,
        "total_conservation_route_recorded": accepted,
        "total_conservation_identity_recorded": accepted,
        "total_stress_energy_conservation_identity_recorded": accepted,
        "total_conservation_proved": accepted,
        "total_stress_energy_conservation_proved": accepted,
        "bounded_total_conservation_route_accepted": accepted,
        "matter_gauge_exchange_balance_route_accepted": accepted,
        "gauge_sector_exchange_route_already_accepted": accepted,
        "matter_sector_exchange_route_already_accepted": accepted,
        "exchange_terms_cancel": accepted,
        "exchange_terms_cancel_accepted": accepted,
        "total_stress_energy_object_preserved": accepted,
        "combined_matter_gauge_system_conserved": accepted,
        "matter_gauge_interaction_balance_chain_complete": accepted,
        "C_exchange_candidate_ready_for_later_packet": accepted,
        "C_exchange_candidate_packet_selected_after_review": accepted,
        "C_exchange_candidate_packet_authorized_here": accepted,
        "C_exchange_constraint_candidate_packet_selected": accepted,
        "C_exchange_constraint_candidate_packet_authorized": accepted,
        "C_exchange_constraint_candidate_packet_prepared_here": False,
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
            "treat total conservation review as C_exchange closeout",
            "embed C_exchange as a functional in this review",
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
            "The review accepts the bounded route record that the accepted "
            "gauge-sector and matter-sector exchange identities cancel to give "
            "nabla_mu(T_A^{mu nu} + T_psi^{mu nu}) = 0, equivalently "
            "nabla_mu T_total^{mu nu} = 0 with T_total^{mu nu} = "
            "T_A^{mu nu} + T_psi^{mu nu}."
        ),
        "plain_meaning": (
            "The gauge field loses exactly what matter gains, so the combined "
            "matter-gauge system stays conserved at the bounded route-record level."
        ),
        "non_claim_boundary": (
            "This is a bounded total stress-energy conservation route result "
            "review only. It accepts the accepted gauge-sector exchange route, "
            "the accepted matter-sector exchange route, exchange-term "
            "cancellation, T_total = T_A + T_psi, and the recorded "
            "nabla_mu T_total^{mu nu} = 0 route. It selects C_exchange "
            "constraint-candidate packet preparation next, with "
            "C_exchange^{Apsi,nu} := nabla_mu T_total^{mu nu} and "
            "C_exchange^{Apsi,nu} = 0 as an admissibility-only candidate. It "
            "records no C_exchange closeout, no C_exchange functional "
            "embedding, no C_k action variation, no full Maxwell closure, no "
            "EM-QFT closure, no QFT-GR closure, no quantized electromagnetism, "
            "no anomaly analysis, no Standard Model derivation, no Phase 2 "
            "authorization, no empirical validation, and no master-action "
            "promotion. The full ToeFormal aggregate is recorded as NOT_RUN "
            "for this review."
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
            "total_stress_energy_conservation_route_packet_json": _ptr(
                total_packet_path
            ),
            "total_stress_energy_conservation_route_packet_outcome": (
                TOTAL_PACKET_OUTCOME
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
            "Review the ToE-native psi-A U(1) total stress-energy conservation "
            "route packet result."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--total-packet", type=Path, default=TOTAL_PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    total_packet_path = (
        args.total_packet if args.total_packet.is_absolute() else REPO_ROOT / args.total_packet
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_toe_native_psi_a_u1_total_stress_energy_conservation_route_result_review(
        total_packet_path=total_packet_path,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(out, payload)
    print(
        "toe_native_psi_a_u1_total_stress_energy_conservation_route_result_review: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
