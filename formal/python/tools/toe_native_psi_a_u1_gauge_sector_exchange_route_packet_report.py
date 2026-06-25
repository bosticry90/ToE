from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_stress_energy_definition_policy_result_review_report import (
    ACTION_BLOCK_STATEMENT,
    COVARIANT_DERIVATIVE_POLICY,
    C_EXCHANGE_CANDIDATE,
    C_EXCHANGE_EQUATION,
    CURRENT_CONSERVATION_RESULT,
    DEFAULT_OUT as STRESS_ENERGY_POLICY_RESULT_REVIEW_PATH,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_TARGET,
    GAUGE_STRESS_ENERGY_LOWER_INDEX_POLICY,
    GAUGE_STRESS_ENERGY_OBJECT,
    GAUGE_STRESS_ENERGY_POLICY,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    MATTER_SECTOR_EXCHANGE_TARGET,
    MATTER_STRESS_ENERGY_OBJECT,
    MATTER_STRESS_ENERGY_POLICY,
    MATTER_STRESS_ENERGY_POLICY_STATUS,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as STRESS_ENERGY_POLICY_RESULT_REVIEW_OUTCOME,
    PACKET_ID as STRESS_ENERGY_POLICY_RESULT_REVIEW_PACKET_ID,
    REVIEW_RESULT as STRESS_ENERGY_POLICY_RESULT_REVIEW_RESULT,
    SCHEMA_ID as STRESS_ENERGY_POLICY_RESULT_REVIEW_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_CONSERVATION_EXPANDED_TARGET,
    TOTAL_CONSERVATION_TARGET,
    TOTAL_STRESS_ENERGY_OBJECT,
    TOTAL_STRESS_ENERGY_POLICY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-25T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_PACKET_20260625_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_PACKET_v0"
OUTCOME_ID = (
    "TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_PACKET_PREPARED_"
    "GAUGE_SECTOR_EXCHANGE_ROUTE_CONSTRUCTED_NO_MATTER_EXCHANGE_OR_"
    "TOTAL_CONSERVATION_PROOF"
)
PACKET_RESULT = OUTCOME_ID
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_gauge_sector_exchange_route_packet_prepared_"
    "gauge_sector_exchange_route_constructed_no_matter_exchange_or_"
    "total_conservation_proof"
)

NEXT_TARGET = "review_toe_native_psi_A_u1_gauge_sector_exchange_route_packet_result"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_gauge_sector_exchange_route_packet_result_review"

GAUGE_SECTOR_EXCHANGE_IDENTITY = GAUGE_SECTOR_EXCHANGE_TARGET
GAUGE_SECTOR_EXCHANGE_TERM = "- F^nu{}_alpha J^alpha"
GAUGE_SECTOR_EXCHANGE_INTERPRETATION = (
    "The gauge field's energy-momentum is not separately conserved when "
    "matter current is present; the gauge sector exchanges energy-momentum "
    "with matter through -F^nu{}_alpha J^alpha."
)
GAUGE_DIVERGENCE_INTERMEDIATE = (
    "nabla_mu T_A^{mu nu} = - F^nu{}_alpha nabla_mu F^{mu alpha}"
)
GAUGE_DIVERGENCE_SOURCE_SUBSTITUTION = (
    "nabla_mu F^{mu alpha} = J^alpha"
)

ASSUMPTIONS = [
    "accepted gauge stress-energy convention for T_A^{mu nu}",
    "metric-compatible torsion-free covariant derivative on the selected domain",
    "F = dA so the Abelian Bianchi identity is available",
    "bounded sourced route nabla_mu F^{mu nu} = J^nu",
    "source current J^nu = q psibar gamma^nu psi",
]

BLOCKED_CLAIMS = [
    "matter-sector exchange proof",
    "total conservation proof",
    "C_exchange closeout",
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

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_PACKET_20260625_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1GaugeSectorExchangeRoutePacket.lean"
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


def _route_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "accepted_gauge_stress_energy_input",
            "status": "consumed_from_stress_energy_definition_policy_result_review",
            "statement": GAUGE_STRESS_ENERGY_POLICY,
        },
        {
            "step_id": "sourced_gauge_route_input",
            "status": "consumed_from_sourced_maxwell_route_packet",
            "statement": SOURCED_GAUGE_ROUTE,
        },
        {
            "step_id": "source_current_input",
            "status": "consumed_from_current_route",
            "statement": SOURCE_CURRENT,
        },
        {
            "step_id": "stress_energy_divergence_reduction",
            "status": "recorded_under_bianchi_and_metric_compatibility_assumptions",
            "statement": GAUGE_DIVERGENCE_INTERMEDIATE,
        },
        {
            "step_id": "sourced_route_substitution",
            "status": "recorded_from_nabla_mu_F_equals_J",
            "statement": GAUGE_DIVERGENCE_SOURCE_SUBSTITUTION,
        },
        {
            "step_id": "gauge_sector_exchange_identity",
            "status": "constructed_gauge_side_only",
            "statement": GAUGE_SECTOR_EXCHANGE_IDENTITY,
        },
    ]


def _review_criteria(result_review_packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "stress_energy_definition_policy_result_review_consumed",
            "status": "accepted",
            "evidence": result_review_packet.get("outcome_id"),
            "assessment": "The accepted stress-energy definition policy result review is consumed.",
        },
        {
            "row_id": "gauge_stress_energy_input_preserved",
            "status": "accepted",
            "evidence": GAUGE_STRESS_ENERGY_POLICY,
            "assessment": "The gauge stress-energy convention is the route input.",
        },
        {
            "row_id": "sourced_gauge_and_current_inputs_preserved",
            "status": "accepted",
            "evidence": [SOURCED_GAUGE_ROUTE, SOURCE_CURRENT],
            "assessment": "The sourced gauge route and psi-made current are preserved.",
        },
        {
            "row_id": "gauge_divergence_route_constructed",
            "status": "accepted",
            "evidence": [GAUGE_DIVERGENCE_INTERMEDIATE, GAUGE_SECTOR_EXCHANGE_IDENTITY],
            "assessment": "The gauge stress-energy divergence route reaches the gauge-side exchange identity.",
        },
        {
            "row_id": "gauge_side_only_scope_preserved",
            "status": "accepted",
            "evidence": [
                GAUGE_SECTOR_EXCHANGE_IDENTITY,
                MATTER_SECTOR_EXCHANGE_TARGET,
                TOTAL_CONSERVATION_EXPANDED_TARGET,
            ],
            "assessment": "Only the gauge-side exchange route is constructed here.",
        },
        {
            "row_id": "matter_total_and_closure_claims_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Matter exchange, total conservation, closure, validation, and promotion remain blocked.",
        },
        {
            "row_id": "next_target_is_result_review",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The packet rotates to result review before any matter-sector attempt.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_gauge_sector_exchange_route_packet",
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


def build_toe_native_psi_a_u1_gauge_sector_exchange_route_packet(
    *,
    stress_energy_policy_result_review_path: Path = STRESS_ENERGY_POLICY_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review_packet = _read_json(stress_energy_policy_result_review_path)
    route_steps = _route_steps()
    review_criteria = _review_criteria(result_review_packet)
    acceptance_criteria = {
        "consumes_expected_stress_energy_policy_result_review": (
            result_review_packet.get("schema_id")
            == STRESS_ENERGY_POLICY_RESULT_REVIEW_SCHEMA_ID
            and result_review_packet.get("packet_id")
            == STRESS_ENERGY_POLICY_RESULT_REVIEW_PACKET_ID
            and result_review_packet.get("outcome_id")
            == STRESS_ENERGY_POLICY_RESULT_REVIEW_OUTCOME
            and result_review_packet.get("review_result")
            == STRESS_ENERGY_POLICY_RESULT_REVIEW_RESULT
            and result_review_packet.get("selected_next_target") == CONSUMED_TARGET
            and result_review_packet.get("accepted") is True
        ),
        "route_inputs_preserved": (
            result_review_packet.get("gauge_stress_energy_policy")
            == GAUGE_STRESS_ENERGY_POLICY
            and result_review_packet.get("sourced_gauge_route") == SOURCED_GAUGE_ROUTE
            and result_review_packet.get("source_current") == SOURCE_CURRENT
            and result_review_packet.get("gauge_sector_exchange_target")
            == GAUGE_SECTOR_EXCHANGE_TARGET
        ),
        "gauge_sector_exchange_identity_constructed": (
            route_steps[-1]["statement"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
            and len(route_steps) == 6
        ),
        "matter_total_and_closure_blockers_preserved": (
            len(BLOCKED_CLAIMS) == 12
            and "matter-sector exchange proof" in BLOCKED_CLAIMS
            and "total conservation proof" in BLOCKED_CLAIMS
            and "master-action promotion" in BLOCKED_CLAIMS
        ),
        "next_target_is_result_review": NEXT_TARGET
        == "review_toe_native_psi_A_u1_gauge_sector_exchange_route_packet_result",
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_stress_energy_definition_policy_result_review_result": (
            STRESS_ENERGY_POLICY_RESULT_REVIEW_OUTCOME
        ),
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "action_block_statement": ACTION_BLOCK_STATEMENT,
        "covariant_derivative_policy": COVARIANT_DERIVATIVE_POLICY,
        "field_strength_policy": FIELD_STRENGTH_POLICY,
        "gauge_transformation_policy": GAUGE_TRANSFORMATION_POLICY,
        "source_current": SOURCE_CURRENT,
        "current_conservation_result": CURRENT_CONSERVATION_RESULT,
        "sourced_gauge_route": SOURCED_GAUGE_ROUTE,
        "gauge_stress_energy_object": GAUGE_STRESS_ENERGY_OBJECT,
        "gauge_stress_energy_policy": GAUGE_STRESS_ENERGY_POLICY,
        "gauge_stress_energy_lower_index_policy": GAUGE_STRESS_ENERGY_LOWER_INDEX_POLICY,
        "matter_stress_energy_object": MATTER_STRESS_ENERGY_OBJECT,
        "matter_stress_energy_policy": MATTER_STRESS_ENERGY_POLICY,
        "matter_stress_energy_policy_status": MATTER_STRESS_ENERGY_POLICY_STATUS,
        "total_stress_energy_object": TOTAL_STRESS_ENERGY_OBJECT,
        "total_stress_energy_policy": TOTAL_STRESS_ENERGY_POLICY,
        "gauge_sector_exchange_target": GAUGE_SECTOR_EXCHANGE_TARGET,
        "gauge_sector_exchange_identity": GAUGE_SECTOR_EXCHANGE_IDENTITY,
        "gauge_sector_exchange_term": GAUGE_SECTOR_EXCHANGE_TERM,
        "gauge_divergence_intermediate": GAUGE_DIVERGENCE_INTERMEDIATE,
        "gauge_divergence_source_substitution": GAUGE_DIVERGENCE_SOURCE_SUBSTITUTION,
        "matter_sector_exchange_target": MATTER_SECTOR_EXCHANGE_TARGET,
        "total_conservation_target": TOTAL_CONSERVATION_TARGET,
        "total_conservation_expanded_target": TOTAL_CONSERVATION_EXPANDED_TARGET,
        "C_exchange_candidate": C_EXCHANGE_CANDIDATE,
        "C_exchange_equation": C_EXCHANGE_EQUATION,
        "assumptions": ASSUMPTIONS,
        "assumption_count": len(ASSUMPTIONS),
        "route_steps": route_steps,
        "route_step_count": len(route_steps),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "gauge_sector_exchange_route_packet_prepared": accepted,
        "gauge_sector_exchange_route_constructed": accepted,
        "gauge_sector_exchange_route_recorded": accepted,
        "gauge_sector_exchange_identity_recorded": accepted,
        "gauge_sector_exchange_identity_constructed": accepted,
        "gauge_stress_energy_divergence_route_recorded": accepted,
        "gauge_sector_exchange_proved": accepted,
        "gauge_sector_exchange_proved_here": accepted,
        "gauge_side_exchange_only": accepted,
        "gauge_field_energy_momentum_not_separately_conserved_when_J_present": accepted,
        "matter_sector_exchange_packet_selected": False,
        "matter_sector_exchange_packet_authorized_here": False,
        "total_conservation_packet_selected": False,
        "total_conservation_packet_authorized_here": False,
        "gauge_sector_exchange_route_packet_result_review_selected": accepted,
        "gauge_sector_exchange_route_packet_result_review_authorized": accepted,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "stress_energy_derived_here": False,
        "stress_energy_metric_variation_derived": False,
        "stress_energy_tetrad_variation_derived": False,
        "psi_stress_energy_derived": False,
        "matter_stress_energy_derived": False,
        "matter_sector_exchange_proved": False,
        "matter_sector_exchange_route_constructed": False,
        "matter_sector_exchange_identity_recorded": False,
        "gauge_matter_exchange_identity_proved": False,
        "exchange_identity_proved": False,
        "gauge_matter_exchange_proved": False,
        "matter_gauge_exchange_proved": False,
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
        "critical_gate_fail_conditions": [
            "treat gauge-side exchange as matter-sector exchange",
            "prove matter-sector exchange in this packet",
            "prove total stress-energy conservation in this packet",
            "close C_exchange",
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
            "Starting from T_A^{mu nu} = - F^{mu}{}_{alpha} F^{nu alpha} "
            "+ 1/4 g^{mu nu} F_{alpha beta}F^{alpha beta}, the sourced "
            "route nabla_mu F^{mu nu} = J^nu, and "
            "J^nu = q psibar gamma^nu psi, this packet records the "
            "gauge-sector exchange identity "
            "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha."
        ),
        "plain_meaning": GAUGE_SECTOR_EXCHANGE_INTERPRETATION,
        "non_claim_boundary": (
            "This is a bounded gauge-sector exchange route packet only. It "
            "records nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha from the "
            "accepted gauge stress-energy convention and sourced route. It "
            "records no matter-sector exchange proof, no total conservation "
            "proof, no C_exchange closeout, no full Maxwell closure, no "
            "EM-QFT closure, no QFT-GR closure, no quantized electromagnetism, "
            "no anomaly analysis, no Standard Model derivation, no Phase 2 "
            "authorization, no empirical validation, and no master-action "
            "promotion. The full ToeFormal aggregate is recorded as NOT_RUN "
            "for this packet."
        ),
        "validation_policy": validation_policy,
        "lean_validation_policy": LEAN_VALIDATION_POLICY_ID,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "source_inputs": {
            "stress_energy_definition_policy_result_review_json": _ptr(
                stress_energy_policy_result_review_path
            ),
            "stress_energy_definition_policy_result_review_outcome": (
                STRESS_ENERGY_POLICY_RESULT_REVIEW_OUTCOME
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
        description="Prepare the ToE-native psi-A U(1) gauge-sector exchange route packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--stress-energy-policy-result-review",
        type=Path,
        default=STRESS_ENERGY_POLICY_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    result_review_path = (
        args.stress_energy_policy_result_review
        if args.stress_energy_policy_result_review.is_absolute()
        else REPO_ROOT / args.stress_energy_policy_result_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_toe_native_psi_a_u1_gauge_sector_exchange_route_packet(
        stress_energy_policy_result_review_path=result_review_path,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(out, payload)
    print(
        "toe_native_psi_a_u1_gauge_sector_exchange_route_packet: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
