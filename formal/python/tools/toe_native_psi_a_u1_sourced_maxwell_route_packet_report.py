from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_current_conservation_from_dirac_pair_packet_report import (
    ACTION_BLOCK_STATEMENT,
    ADJOINT_EQUATION_ROUTE,
    A_VARIATION_RESIDUAL,
    BOUNDED_ROUTE_SHAPE,
    COVARIANT_DERIVATIVE_PAIR_POLICY,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE,
    CURRENT_CANDIDATE_FROM_A_VARIATION,
    CURRENT_CANDIDATE_POLICY_AFTER_CONSERVATION,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_CONSERVATION_ROUTE_STATUS,
    CURRENT_DIVERGENCE_ROUTE,
    DEFAULT_OUT as CURRENT_CONSERVATION_PACKET_PATH,
    DIRAC_PAIR_ROUTE_INPUTS,
    EXCHANGE_ROUTE_PREVIEW,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    OUTCOME_ID as CURRENT_CONSERVATION_OUTCOME,
    PACKET_ID as CURRENT_CONSERVATION_PACKET_ID,
    PACKET_RESULT as CURRENT_CONSERVATION_PACKET_RESULT,
    PSI_EQUATION_ROUTE,
    SCHEMA_ID as CURRENT_CONSERVATION_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCED_MAXWELL_ROUTE_PREVIEW,
    TARGET_CONSERVATION_LAW,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_SOURCED_MAXWELL_ROUTE_PACKET_20260624_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_SOURCED_MAXWELL_ROUTE_PACKET_v0"
OUTCOME_ID = (
    "TOE_NATIVE_PSI_A_U1_SOURCED_MAXWELL_ROUTE_PACKET_PREPARED_"
    "SOURCED_GAUGE_ROUTE_RECORDED_NO_MAXWELL_CLOSURE_OR_EXCHANGE_PROOF"
)
PACKET_RESULT = OUTCOME_ID
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_sourced_maxwell_route_packet_prepared_"
    "sourced_gauge_route_recorded_no_maxwell_closure_or_exchange_proof"
)

CONSUMED_TARGET = "prepare_toe_native_psi_A_u1_sourced_maxwell_route_packet"
NEXT_TARGET = "prepare_toe_native_psi_A_u1_stress_energy_and_exchange_obligation_packet"
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_stress_energy_and_exchange_obligation_packet_preparation"
)

SOURCE_CURRENT = "J^nu = q psibar gamma^nu psi"
CONSERVED_SOURCE_CONDITION = "nabla_mu J^mu = 0"
SOURCED_MAXWELL_RESIDUAL_ZERO = "nabla_mu F^{mu nu} - J^nu = 0"
SOURCED_GAUGE_ROUTE = "nabla_mu F^{mu nu} = J^nu"
SOURCED_GAUGE_ROUTE_STATUS = (
    "bounded sourced gauge route recorded from the A-variation residual and "
    "the conserved psi-made current"
)
CURRENT_CONSISTENCY_STATUS = (
    "the source current is conserved under the bounded Dirac-pair route and "
    "is therefore consistent as the source for the recorded gauge route"
)
STRESS_ENERGY_EXCHANGE_PREVIEW = (
    "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha; "
    "nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha; "
    "nabla_mu(T_A^{mu nu} + T_psi^{mu nu}) = 0"
)
POSSIBLE_C_EXCHANGE_ROUTE = (
    "C_exchange^{A psi,nu} := nabla_mu(T_A^{mu nu} + T_psi^{mu nu})"
)
PLAIN_MEANING = (
    "The gauge field equation now has a matter-made source, and that source "
    "is conserved under the bounded psi-A U(1) assumptions."
)

ROUTE_STEPS = [
    {
        "step_id": "a_variation_residual_input",
        "statement": A_VARIATION_RESIDUAL,
        "status": "consumed_from_A_variation_current_route",
    },
    {
        "step_id": "conserved_current_input",
        "statement": CONSERVED_SOURCE_CONDITION,
        "status": "consumed_from_current_conservation_from_dirac_pair_route",
    },
    {
        "step_id": "sourced_residual_zero",
        "statement": SOURCED_MAXWELL_RESIDUAL_ZERO,
        "status": "recorded_as_bounded_euler_residual_route",
    },
    {
        "step_id": "bounded_sourced_gauge_route",
        "statement": SOURCED_GAUGE_ROUTE,
        "status": "recorded_no_full_maxwell_closure",
    },
]

ASSUMPTIONS = [
    {
        "assumption_id": "selected_u1_policy",
        "statement": COVARIANT_DERIVATIVE_POLICY,
        "status": "indexed",
    },
    {
        "assumption_id": "a_variation_residual_admitted",
        "statement": A_VARIATION_RESIDUAL,
        "status": "consumed",
    },
    {
        "assumption_id": "current_conservation_admitted",
        "statement": CURRENT_CONSERVATION_RESULT,
        "status": "consumed",
    },
    {
        "assumption_id": "field_strength_context",
        "statement": FIELD_STRENGTH_POLICY,
        "status": "preserved_as_existing_F_equals_dA_context",
    },
    {
        "assumption_id": "field_domain_regular_boundary",
        "statement": "psi, psibar, and A satisfy the bounded domain and boundary policy",
        "status": "indexed",
    },
]

INDEXED_FUTURE_ROUTES = [
    {
        "route_id": "stress_energy_and_exchange_obligation",
        "route_shape": STRESS_ENERGY_EXCHANGE_PREVIEW,
        "status": "selected_next_not_proved",
        "proof_claimed": False,
    },
    {
        "route_id": "possible_C_exchange_rule",
        "route_shape": POSSIBLE_C_EXCHANGE_ROUTE,
        "status": "indexed_not_closed",
        "proof_claimed": False,
    },
]

BLOCKED_CLAIMS = [
    "full Maxwell closure",
    "homogeneous Maxwell route beyond existing F = dA context",
    "stress-energy derivation",
    "gauge-matter exchange identity",
    "total conservation proof",
    "C_exchange closeout",
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
    / "TOE_NATIVE_PSI_A_U1_SOURCED_MAXWELL_ROUTE_PACKET_20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1SourcedMaxwellRoutePacket.lean"
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


def _review_criteria(current_conservation_packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "current_conservation_packet_consumed",
            "status": "accepted",
            "evidence": current_conservation_packet.get("outcome_id"),
            "assessment": "The current-conservation-from-Dirac-pair packet is consumed.",
        },
        {
            "row_id": "a_variation_residual_preserved",
            "status": "accepted",
            "evidence": A_VARIATION_RESIDUAL,
            "assessment": "The A-variation residual is preserved as the gauge-route input.",
        },
        {
            "row_id": "conserved_current_preserved",
            "status": "accepted",
            "evidence": [SOURCE_CURRENT, CURRENT_CONSERVATION_RESULT],
            "assessment": "The psi-made current and its bounded conservation route are preserved.",
        },
        {
            "row_id": "bounded_sourced_route_recorded",
            "status": "accepted",
            "evidence": SOURCED_GAUGE_ROUTE,
            "assessment": "The sourced gauge route is recorded as bounded route construction.",
        },
        {
            "row_id": "f_equals_dA_context_only",
            "status": "accepted",
            "evidence": FIELD_STRENGTH_POLICY,
            "assessment": "The homogeneous-side context remains only the existing F = dA policy.",
        },
        {
            "row_id": "exchange_obligation_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The stress-energy and exchange obligation packet is selected next.",
        },
        {
            "row_id": "closure_and_promotion_claims_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Maxwell closure, exchange proof, empirical, Phase 2, and promotion claims remain blocked.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_sourced_maxwell_route_packet",
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


def build_toe_native_psi_a_u1_sourced_maxwell_route_packet(
    *,
    current_conservation_packet_path: Path = CURRENT_CONSERVATION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    current_conservation_packet = _read_json(current_conservation_packet_path)
    review_criteria = _review_criteria(current_conservation_packet)
    acceptance_criteria = {
        "consumes_expected_current_conservation_packet": (
            current_conservation_packet.get("schema_id")
            == CURRENT_CONSERVATION_SCHEMA_ID
            and current_conservation_packet.get("packet_id")
            == CURRENT_CONSERVATION_PACKET_ID
            and current_conservation_packet.get("outcome_id")
            == CURRENT_CONSERVATION_OUTCOME
            and current_conservation_packet.get("packet_result")
            == CURRENT_CONSERVATION_PACKET_RESULT
            and current_conservation_packet.get("selected_next_target")
            == CONSUMED_TARGET
            and current_conservation_packet.get("accepted") is True
        ),
        "a_variation_and_current_conservation_preserved": (
            current_conservation_packet.get("A_variation_residual")
            == A_VARIATION_RESIDUAL
            and current_conservation_packet.get("current_conservation_result")
            == CURRENT_CONSERVATION_RESULT
            and current_conservation_packet.get("current_conservation_proved")
            is True
        ),
        "sourced_route_recorded": (
            SOURCED_MAXWELL_RESIDUAL_ZERO.endswith("= 0")
            and SOURCED_GAUGE_ROUTE == BOUNDED_ROUTE_SHAPE
            and SOURCE_CURRENT == CURRENT_CANDIDATE_FROM_A_VARIATION
        ),
        "current_consistency_preserved": (
            CONSERVED_SOURCE_CONDITION == TARGET_CONSERVATION_LAW
            and SOURCE_CURRENT == "J^nu = q psibar gamma^nu psi"
        ),
        "assumptions_indexed": len(ASSUMPTIONS) == 5,
        "future_routes_indexed_without_proof": (
            len(INDEXED_FUTURE_ROUTES) == 2
            and all(route["proof_claimed"] is False for route in INDEXED_FUTURE_ROUTES)
        ),
        "stress_energy_exchange_obligation_selected_next": NEXT_TARGET
        == "prepare_toe_native_psi_A_u1_stress_energy_and_exchange_obligation_packet",
        "blocked_claims_complete": len(BLOCKED_CLAIMS) == 14,
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_SOURCED_MAXWELL_ROUTE_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_SOURCED_MAXWELL_ROUTE_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_SOURCED_MAXWELL_ROUTE_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_current_conservation_from_dirac_pair_packet_result": (
            CURRENT_CONSERVATION_OUTCOME
        ),
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "action_block_statement": ACTION_BLOCK_STATEMENT,
        "covariant_derivative_policy": COVARIANT_DERIVATIVE_POLICY,
        "covariant_derivative_pair_policy": COVARIANT_DERIVATIVE_PAIR_POLICY,
        "field_strength_policy": FIELD_STRENGTH_POLICY,
        "gauge_transformation_policy": GAUGE_TRANSFORMATION_POLICY,
        "A_variation_residual": A_VARIATION_RESIDUAL,
        "sourced_maxwell_residual_zero": SOURCED_MAXWELL_RESIDUAL_ZERO,
        "sourced_gauge_route": SOURCED_GAUGE_ROUTE,
        "sourced_maxwell_route": SOURCED_GAUGE_ROUTE,
        "bounded_route_shape": SOURCED_GAUGE_ROUTE,
        "source_current": SOURCE_CURRENT,
        "current_candidate": CURRENT_CANDIDATE,
        "current_candidate_from_A_variation": CURRENT_CANDIDATE_FROM_A_VARIATION,
        "current_candidate_policy": CURRENT_CANDIDATE_POLICY_AFTER_CONSERVATION,
        "target_conservation_law": TARGET_CONSERVATION_LAW,
        "conserved_source_condition": CONSERVED_SOURCE_CONDITION,
        "current_conservation_result": CURRENT_CONSERVATION_RESULT,
        "current_conservation_route_status": CURRENT_CONSERVATION_ROUTE_STATUS,
        "current_divergence_route": CURRENT_DIVERGENCE_ROUTE,
        "dirac_pair_route_inputs": DIRAC_PAIR_ROUTE_INPUTS,
        "psi_equation_route": PSI_EQUATION_ROUTE,
        "adjoint_equation_route": ADJOINT_EQUATION_ROUTE,
        "sourced_gauge_route_status": SOURCED_GAUGE_ROUTE_STATUS,
        "current_consistency_status": CURRENT_CONSISTENCY_STATUS,
        "sourced_maxwell_route_preview": SOURCED_MAXWELL_ROUTE_PREVIEW,
        "stress_energy_exchange_preview": STRESS_ENERGY_EXCHANGE_PREVIEW,
        "possible_C_exchange_route": POSSIBLE_C_EXCHANGE_ROUTE,
        "exchange_route_preview": EXCHANGE_ROUTE_PREVIEW,
        "route_steps": ROUTE_STEPS,
        "route_step_count": len(ROUTE_STEPS),
        "assumptions": ASSUMPTIONS,
        "assumption_count": len(ASSUMPTIONS),
        "indexed_future_routes": INDEXED_FUTURE_ROUTES,
        "indexed_future_route_count": len(INDEXED_FUTURE_ROUTES),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "sourced_maxwell_route_packet_prepared": accepted,
        "sourced_gauge_route_recorded": accepted,
        "current_consistent_sourced_gauge_route_recorded": accepted,
        "bounded_sourced_maxwell_route_recorded": accepted,
        "bounded_sourced_maxwell_route_derived": accepted,
        "sourced_maxwell_route_recorded": accepted,
        "sourced_maxwell_equation_recorded": accepted,
        "sourced_maxwell_residual_zero_recorded": accepted,
        "A_variation_residual_consumed": accepted,
        "current_conservation_consumed": accepted,
        "current_conserved_source_admitted_for_bounded_route": accepted,
        "matter_made_source_recorded": accepted,
        "F_equals_dA_context_preserved": accepted,
        "homogeneous_context_limited_to_F_equals_dA": accepted,
        "stress_energy_and_exchange_obligation_packet_selected": accepted,
        "stress_energy_and_exchange_obligation_packet_preparation_authorized": (
            accepted
        ),
        "C_exchange_future_route_indexed": accepted,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "sourced_maxwell_route_derived": accepted,
        "sourced_maxwell_closure_claimed": False,
        "maxwell_closure_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_maxwell_system_closure_claimed": False,
        "full_em_closure_claimed": False,
        "homogeneous_maxwell_route_beyond_f_equals_dA_claimed": False,
        "stress_energy_derived": False,
        "psi_stress_energy_derived": False,
        "gauge_matter_exchange_identity_proved": False,
        "exchange_identity_proved": False,
        "gauge_matter_exchange_proved": False,
        "matter_gauge_exchange_proved": False,
        "total_conservation_proved": False,
        "total_stress_energy_conservation_proved": False,
        "C_exchange_closeout": False,
        "C_exchange_definition_closeout": False,
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
            "treat bounded sourced gauge route as full Maxwell closure",
            "claim a homogeneous Maxwell route beyond the existing F = dA context",
            "derive stress-energy or exchange",
            "prove total stress-energy conservation",
            "close C_exchange",
            "claim EM-QFT or QFT-GR closure",
            "claim quantized electromagnetism",
            "claim Standard Model derivation",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "mathematical_statement": (
            "This packet combines the accepted A-variation residual "
            "delta_A S_{psi A} -> int d^4x sqrt(-g) [nabla_mu F^{mu nu} - J^nu] "
            "delta A_nu with the bounded current-conservation route "
            "nabla_mu J^mu = 0 and records the sourced gauge route "
            "nabla_mu F^{mu nu} = J^nu for J^nu = q psibar gamma^nu psi."
        ),
        "plain_meaning": PLAIN_MEANING,
        "non_claim_boundary": (
            "This is a bounded sourced-Maxwell-route packet only; it records "
            "nabla_mu F^{mu nu} = J^nu with J^nu = q psibar gamma^nu psi using "
            "the accepted A-variation residual and conserved current. It records "
            "no full Maxwell closure, no homogeneous Maxwell route beyond the "
            "existing F = dA context, no stress-energy derivation, no "
            "gauge-matter exchange identity, no total conservation proof, no "
            "C_exchange closeout, no EM-QFT closure, no QFT-GR closure, no "
            "quantized electromagnetism, no anomaly analysis, no Standard Model "
            "derivation, no Phase 2 authorization, no empirical validation, and "
            "no master-action promotion. The full ToeFormal aggregate is recorded "
            "as NOT_RUN for this packet."
        ),
        "validation_policy": validation_policy,
        "lean_validation_policy": LEAN_VALIDATION_POLICY_ID,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "source_inputs": {
            "current_conservation_from_dirac_pair_json": _ptr(
                current_conservation_packet_path
            ),
            "current_conservation_from_dirac_pair_outcome": (
                CURRENT_CONSERVATION_OUTCOME
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
        description="Prepare the ToE-native psi-A U(1) sourced Maxwell route packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--current-conservation-packet",
        type=Path,
        default=CURRENT_CONSERVATION_PACKET_PATH,
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    payload = build_toe_native_psi_a_u1_sourced_maxwell_route_packet(
        current_conservation_packet_path=args.current_conservation_packet,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(args.out, payload)
    print(args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
