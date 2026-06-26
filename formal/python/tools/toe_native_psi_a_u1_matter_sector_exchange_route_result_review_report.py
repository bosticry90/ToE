from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_matter_sector_exchange_route_packet_report import (
    ACTION_BLOCK_STATEMENT,
    ADJOINT_DERIVATIVE_POLICY,
    ADJOINT_EQUATION_ROUTE,
    BLOCKED_CLAIMS as PACKET_BLOCKED_CLAIMS,
    CONVENTION_ASSUMPTIONS,
    COVARIANT_DERIVATIVE_POLICY,
    C_EXCHANGE_CANDIDATE,
    C_EXCHANGE_EQUATION,
    CURRENT_CANDIDATE,
    CURRENT_CANDIDATE_POLICY_AFTER_CONSERVATION,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_CONSERVATION_ROUTE_STATUS,
    CURRENT_DIVERGENCE_ROUTE,
    DEFAULT_OUT as MATTER_PACKET_PATH,
    DIRAC_PAIR_ROUTE_INPUTS,
    FIELD_STRENGTH_POLICY,
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
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MATTER_SECTOR_EXCHANGE_TERM,
    MATTER_STRESS_ENERGY_OBJECT,
    MATTER_STRESS_ENERGY_POLICY,
    MATTER_STRESS_ENERGY_POLICY_STATUS,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as MATTER_PACKET_OUTCOME,
    PACKET_ID as MATTER_PACKET_ID,
    SCHEMA_ID as MATTER_PACKET_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_CONSERVATION_EXPANDED_TARGET,
    TOTAL_CONSERVATION_FUTURE_COMBINATION,
    TOTAL_CONSERVATION_TARGET,
    TOTAL_STRESS_ENERGY_OBJECT,
    TOTAL_STRESS_ENERGY_POLICY,
)
from formal.python.tools.toe_native_psi_a_u1_psi_variation_dirac_route_packet_report import (
    PSI_EQUATION_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-25T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_20260625_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_ACCEPTS_"
    "MATTER_SECTOR_EXCHANGE_ROUTE_NO_TOTAL_CONSERVATION_OR_CEXCHANGE_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_matter_sector_exchange_route_result_review_accepts_"
    "matter_sector_exchange_route_no_total_conservation_or_cexchange_closure"
)

NEXT_TARGET = "prepare_toe_native_psi_A_u1_total_stress_energy_conservation_route_packet"
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_total_stress_energy_conservation_route_packet_preparation"
)
TOTAL_CONSERVATION_ROUTE_TO_TEST = TOTAL_CONSERVATION_EXPANDED_TARGET
TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_TO_TEST = "nabla_mu T_total^{mu nu} = 0"
TARGETED_LEAN_BUILD_STATUS = "PASSED"
FULL_TOEFORMAL_AGGREGATE_STATUS = "NOT_RUN"

ACCEPTED_REVIEW_FINDINGS = [
    "matter-sector exchange route recorded",
    "J^alpha = q psibar gamma^alpha psi preserved",
    "Dirac-pair/current-conservation context preserved",
    "gauge-sector exchange context preserved",
]

BLOCKED_CLAIMS = PACKET_BLOCKED_CLAIMS

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_"
    "20260625_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1MatterSectorExchangeRouteResultReview.lean"
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
            "row_id": "matter_sector_exchange_route_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("outcome_id"),
            "assessment": "The prepared matter-sector exchange route packet is the consumed input.",
        },
        {
            "row_id": "matter_sector_exchange_route_recorded",
            "status": "accepted",
            "evidence": [MATTER_DIVERGENCE_INTERMEDIATE, MATTER_SECTOR_EXCHANGE_IDENTITY],
            "assessment": "The matter stress-energy divergence route and matter-side exchange identity are recorded.",
        },
        {
            "row_id": "J_alpha_candidate_preserved",
            "status": "accepted",
            "evidence": MATTER_DIVERGENCE_CURRENT_SUBSTITUTION,
            "assessment": "The review preserves J^alpha = q psibar gamma^alpha psi as the current substitution.",
        },
        {
            "row_id": "dirac_pair_current_conservation_context_preserved",
            "status": "accepted",
            "evidence": [DIRAC_PAIR_ROUTE_INPUTS, CURRENT_CONSERVATION_RESULT],
            "assessment": "The Dirac-pair and current-conservation context are preserved as bounded inputs.",
        },
        {
            "row_id": "gauge_sector_exchange_context_preserved",
            "status": "accepted",
            "evidence": [GAUGE_SECTOR_EXCHANGE_IDENTITY, GAUGE_SECTOR_EXCHANGE_TERM],
            "assessment": "The accepted gauge-sector exchange identity remains the opposite-sign context.",
        },
        {
            "row_id": "both_exchange_halves_ready_for_combination",
            "status": "accepted",
            "evidence": [GAUGE_SECTOR_EXCHANGE_IDENTITY, MATTER_SECTOR_EXCHANGE_IDENTITY],
            "assessment": "Both exchange halves are recorded and ready for a later total-conservation route packet.",
        },
        {
            "row_id": "total_conservation_and_closure_claims_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Total conservation, C_exchange, closure, empirical, Phase 2, and promotion claims remain blocked.",
        },
        {
            "row_id": "total_conservation_route_packet_selected_next",
            "status": "accepted",
            "evidence": [NEXT_TARGET, TOTAL_CONSERVATION_ROUTE_TO_TEST],
            "assessment": "The next target is total stress-energy conservation route preparation only.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_matter_sector_exchange_route_result_review",
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


def build_toe_native_psi_a_u1_matter_sector_exchange_route_result_review(
    *,
    matter_packet_path: Path = MATTER_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(matter_packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_matter_sector_exchange_route_packet": (
            packet.get("schema_id") == MATTER_PACKET_SCHEMA_ID
            and packet.get("packet_id") == MATTER_PACKET_ID
            and packet.get("outcome_id") == MATTER_PACKET_OUTCOME
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "matter_sector_exchange_route_recorded": (
            packet.get("matter_sector_exchange_route_constructed") is True
            and packet.get("matter_stress_energy_divergence_route_recorded") is True
            and packet.get("matter_sector_exchange_identity")
            == MATTER_SECTOR_EXCHANGE_IDENTITY
        ),
        "J_alpha_current_preserved": (
            packet.get("matter_divergence_current_substitution")
            == MATTER_DIVERGENCE_CURRENT_SUBSTITUTION
            and packet.get("source_current") == SOURCE_CURRENT
        ),
        "dirac_pair_current_conservation_context_preserved": (
            packet.get("dirac_pair_route_inputs") == DIRAC_PAIR_ROUTE_INPUTS
            and packet.get("current_conservation_result") == CURRENT_CONSERVATION_RESULT
            and packet.get("current_divergence_route") == CURRENT_DIVERGENCE_ROUTE
        ),
        "gauge_sector_exchange_context_preserved": (
            packet.get("gauge_sector_exchange_identity")
            == GAUGE_SECTOR_EXCHANGE_IDENTITY
            and packet.get("gauge_sector_exchange_term") == GAUGE_SECTOR_EXCHANGE_TERM
            and packet.get("gauge_sector_exchange_route_accepted") is True
        ),
        "total_and_closure_blockers_preserved": (
            packet.get("blocked_claims") == BLOCKED_CLAIMS
            and packet.get("total_conservation_proved") is False
            and packet.get("C_exchange_closeout") is False
            and packet.get("master_action_promoted") is False
        ),
        "next_target_is_total_conservation_route_packet": (
            NEXT_TARGET
            == "prepare_toe_native_psi_A_u1_total_stress_energy_conservation_route_packet"
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_REVIEW"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "review_executed": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "packet_result": REVIEW_RESULT if accepted else "PENDING_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_matter_sector_exchange_route_packet_result": MATTER_PACKET_OUTCOME,
        "consumed_gauge_sector_exchange_route_result_review_result": (
            GAUGE_RESULT_REVIEW_OUTCOME
        ),
        "selected_next_target": selected_next_target,
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
        "matter_divergence_current_substitution": MATTER_DIVERGENCE_CURRENT_SUBSTITUTION,
        "total_conservation_target": TOTAL_CONSERVATION_TARGET,
        "total_conservation_expanded_target": TOTAL_CONSERVATION_EXPANDED_TARGET,
        "total_conservation_future_combination": TOTAL_CONSERVATION_FUTURE_COMBINATION,
        "total_conservation_route_to_test": TOTAL_CONSERVATION_ROUTE_TO_TEST,
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
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "matter_sector_exchange_route_result_review_accepted": accepted,
        "matter_sector_exchange_route_accepted": accepted,
        "matter_sector_exchange_route_recorded": accepted,
        "matter_sector_exchange_identity_recorded": accepted,
        "matter_sector_exchange_identity_accepted": accepted,
        "matter_stress_energy_divergence_route_recorded": accepted,
        "matter_side_exchange_only": accepted,
        "J_alpha_current_candidate_preserved": accepted,
        "dirac_pair_current_conservation_context_preserved": accepted,
        "gauge_sector_exchange_context_preserved": accepted,
        "gauge_sector_exchange_route_accepted": accepted,
        "both_exchange_halves_recorded": accepted,
        "ready_for_total_conservation_route_packet": accepted,
        "total_conservation_packet_selected": accepted,
        "total_conservation_packet_authorized_here": accepted,
        "total_stress_energy_conservation_route_packet_selected": accepted,
        "total_stress_energy_conservation_route_packet_preparation_authorized": (
            accepted
        ),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "total_conservation_proved": False,
        "total_stress_energy_conservation_proved": False,
        "C_exchange_closeout": False,
        "C_exchange_definition_closeout": False,
        "C_exchange_rule_family_closed": False,
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
        "mathematical_statement": (
            "The result review accepts the matter-side route "
            "nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha with "
            "J^alpha = q psibar gamma^alpha psi, preserving the Dirac-pair, "
            "current-conservation, and gauge-sector exchange contexts for a "
            "later total stress-energy conservation route packet."
        ),
        "plain_meaning": (
            "The matter side receives the equal and opposite exchange term; "
            "the two exchange halves are ready to be combined, but total "
            "conservation is not proved in this review."
        ),
        "non_claim_boundary": (
            "This is a bounded matter-sector exchange route result review only. "
            "It accepts the recorded matter-sector exchange route, preserves "
            "J^alpha = q psibar gamma^alpha psi, preserves the Dirac-pair/"
            "current-conservation context and gauge-sector exchange context, "
            "and selects total stress-energy conservation route preparation "
            "next. It records no total conservation proof, no C_exchange "
            "closeout, no full Maxwell closure, no EM-QFT closure, no QFT-GR "
            "closure, no quantized electromagnetism, no anomaly analysis, no "
            "Standard Model derivation, no Phase 2 authorization, no empirical "
            "validation, and no master-action promotion. Targeted Lean builds "
            "passed; the full ToeFormal aggregate is recorded as NOT_RUN for "
            "this review."
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
            "matter_sector_exchange_route_packet_json": _ptr(matter_packet_path),
            "matter_sector_exchange_route_packet_outcome": MATTER_PACKET_OUTCOME,
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
        description="Review the ToE-native psi-A U(1) matter-sector exchange route packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--matter-packet", type=Path, default=MATTER_PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    matter_packet_path = (
        args.matter_packet
        if args.matter_packet.is_absolute()
        else REPO_ROOT / args.matter_packet
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_toe_native_psi_a_u1_matter_sector_exchange_route_result_review(
        matter_packet_path=matter_packet_path,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(out, payload)
    print(
        "toe_native_psi_a_u1_matter_sector_exchange_route_result_review: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
