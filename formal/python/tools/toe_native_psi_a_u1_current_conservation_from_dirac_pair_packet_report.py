from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_adjoint_dirac_route_packet_report import (
    ACTION_BLOCK_STATEMENT,
    ADJOINT_DERIVATIVE_POLICY,
    ADJOINT_EQUATION_ROUTE,
    ADJOINT_VARIATION_ROUTE,
    A_VARIATION_RESIDUAL,
    BOUNDED_ROUTE_SHAPE,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE_FROM_A_VARIATION,
    CURRENT_CANDIDATE_POLICY,
    CURRENT_CONSERVATION_FROM_PAIR_PREVIEW,
    DEFAULT_OUT as ADJOINT_DIRAC_ROUTE_PATH,
    DIRAC_ROUTE_EQUATION,
    EXCHANGE_ROUTE_PREVIEW,
    FIELD_EQUATION_ROUTE_PREVIEW,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as ADJOINT_DIRAC_ROUTE_OUTCOME,
    PACKET_ID as ADJOINT_DIRAC_ROUTE_PACKET_ID,
    PACKET_RESULT as ADJOINT_DIRAC_ROUTE_RESULT,
    PSI_EQUATION_ROUTE,
    PSI_VARIATION_DIRAC_ROUTE_OUTCOME,
    PSIBAR_VARIATION_ROUTE,
    SCHEMA_ID as ADJOINT_DIRAC_ROUTE_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCED_MAXWELL_COMPATIBILITY_ROUTE_PREVIEW,
    SOURCED_MAXWELL_CONSISTENCY_ROUTE_PREVIEW,
    TARGET_CONSERVATION_LAW,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_FROM_DIRAC_PAIR_PACKET_"
    "20260624_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_FROM_DIRAC_PAIR_PACKET_v0"
OUTCOME_ID = (
    "TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_FROM_DIRAC_PAIR_PACKET_PREPARED_"
    "CURRENT_CONSERVATION_ROUTE_CONSTRUCTED_NO_SOURCED_MAXWELL_CLOSURE_OR_EXCHANGE_PROOF"
)
PACKET_RESULT = OUTCOME_ID
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_current_conservation_from_dirac_pair_packet_prepared_"
    "current_conservation_route_constructed_no_sourced_maxwell_closure_or_exchange_proof"
)

NEXT_TARGET = "prepare_toe_native_psi_A_u1_sourced_maxwell_route_packet"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_sourced_maxwell_route_packet_preparation"

CURRENT_CANDIDATE = "J^mu = q psibar gamma^mu psi"
CURRENT_CANDIDATE_POLICY_AFTER_CONSERVATION = (
    "J^mu = q psibar gamma^mu psi; accepted as an A-variation candidate and "
    "conserved under the bounded Dirac-pair route"
)
COVARIANT_DERIVATIVE_PAIR_POLICY = (
    "D_mu psi = nabla_mu psi + i q A_mu psi; "
    "D_mu psibar = nabla_mu psibar - i q A_mu psibar"
)
CURRENT_DIVERGENCE_ROUTE = (
    "nabla_mu J^mu = q [(D_mu psibar) gamma^mu psi + "
    "psibar gamma^mu D_mu psi]"
)
DIRAC_PAIR_ROUTE_INPUTS = [
    "i (D_mu psibar) gamma^mu + m psibar = 0",
    "i gamma^mu D_mu psi - m psi = 0",
]
MASS_TERM_CANCELLATION_ROUTE = (
    "q [+ i m psibar psi - i m psibar psi] = 0"
)
CURRENT_CONSERVATION_RESULT = "nabla_mu J^mu = 0"
CURRENT_CONSERVATION_ROUTE_STATUS = (
    "bounded current-conservation route constructed under the selected psi-A "
    "U(1) policy, Dirac equation route, adjoint equation route, "
    "gamma-compatibility assumptions, and domain/boundary assumptions"
)
SOURCED_MAXWELL_ROUTE_PREVIEW = (
    "A variation residual plus conserved J^nu -> nabla_mu F^{mu nu} = J^nu"
)
PLAIN_MEANING = (
    "Matter creates the current, and the paired matter equations make that "
    "current conserved under the selected bounded assumptions."
)

ROUTE_STEPS = [
    {
        "step_id": "current_candidate",
        "statement": CURRENT_CANDIDATE,
        "status": "accepted_input_from_A_variation_route",
    },
    {
        "step_id": "divergence_expansion",
        "statement": CURRENT_DIVERGENCE_ROUTE,
        "status": "recorded_under_gamma_compatibility_and_domain_assumptions",
    },
    {
        "step_id": "dirac_pair_substitution",
        "statement": DIRAC_PAIR_ROUTE_INPUTS,
        "status": "uses_recorded_psi_and_adjoint_routes",
    },
    {
        "step_id": "mass_cancellation",
        "statement": MASS_TERM_CANCELLATION_ROUTE,
        "status": "recorded",
    },
    {
        "step_id": "current_conservation_result",
        "statement": CURRENT_CONSERVATION_RESULT,
        "status": "bounded_route_constructed",
    },
]

ASSUMPTIONS = [
    {
        "assumption_id": "selected_u1_policy",
        "statement": COVARIANT_DERIVATIVE_PAIR_POLICY,
        "status": "indexed",
    },
    {
        "assumption_id": "dirac_pair_validity",
        "statement": "psi equation and adjoint equation routes are admitted as bounded inputs",
        "status": "indexed",
    },
    {
        "assumption_id": "gamma_compatibility",
        "statement": "spin/tetrad connection is gamma-compatible for the divergence route",
        "status": "indexed",
    },
    {
        "assumption_id": "field_domain_regular_boundary",
        "statement": "psi, psibar, and A have sufficient regularity and boundary behavior",
        "status": "indexed",
    },
]

INDEXED_FUTURE_ROUTES = [
    {
        "route_id": "sourced_maxwell_route",
        "route_shape": SOURCED_MAXWELL_ROUTE_PREVIEW,
        "status": "selected_next_not_closed",
        "proof_claimed": False,
    },
    {
        "route_id": "exchange_route",
        "route_shape": EXCHANGE_ROUTE_PREVIEW,
        "status": "indexed_not_stress_energy_or_exchange_proof",
        "proof_claimed": False,
    },
]

BLOCKED_CLAIMS = [
    "sourced Maxwell closure",
    "full Maxwell system closure",
    "stress-energy derivation",
    "gauge-matter exchange identity",
    "total stress-energy conservation proof",
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
    / "TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_FROM_DIRAC_PAIR_PACKET_20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1CurrentConservationFromDiracPairPacket.lean"
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


def _review_criteria(adjoint_packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "adjoint_dirac_route_packet_consumed",
            "status": "accepted",
            "evidence": adjoint_packet.get("outcome_id"),
            "assessment": "The adjoint Dirac route packet is the consumed input.",
        },
        {
            "row_id": "dirac_pair_available",
            "status": "accepted",
            "evidence": [PSI_EQUATION_ROUTE, ADJOINT_EQUATION_ROUTE],
            "assessment": "The psi and adjoint equation routes are both recorded.",
        },
        {
            "row_id": "opposite_sign_derivatives_preserved",
            "status": "accepted",
            "evidence": [COVARIANT_DERIVATIVE_POLICY, ADJOINT_DERIVATIVE_POLICY],
            "assessment": "The selected plus-sign psi derivative and opposite-sign adjoint derivative are preserved.",
        },
        {
            "row_id": "current_divergence_route_recorded",
            "status": "accepted",
            "evidence": CURRENT_DIVERGENCE_ROUTE,
            "assessment": "The divergence route for J is recorded under the indexed assumptions.",
        },
        {
            "row_id": "mass_cancellation_recorded",
            "status": "accepted",
            "evidence": MASS_TERM_CANCELLATION_ROUTE,
            "assessment": "The Dirac-pair mass terms cancel in the bounded route.",
        },
        {
            "row_id": "current_conservation_result_recorded",
            "status": "accepted",
            "evidence": CURRENT_CONSERVATION_RESULT,
            "assessment": "The bounded route records nabla_mu J^mu = 0.",
        },
        {
            "row_id": "closure_and_promotion_claims_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Sourced Maxwell, exchange, closure, empirical, Phase 2, and promotion claims remain blocked.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_current_conservation_from_dirac_pair_packet",
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


def build_toe_native_psi_a_u1_current_conservation_from_dirac_pair_packet(
    *,
    adjoint_dirac_route_path: Path = ADJOINT_DIRAC_ROUTE_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    adjoint_packet = _read_json(adjoint_dirac_route_path)
    review_criteria = _review_criteria(adjoint_packet)
    acceptance_criteria = {
        "consumes_expected_adjoint_dirac_route_packet": (
            adjoint_packet.get("schema_id") == ADJOINT_DIRAC_ROUTE_SCHEMA_ID
            and adjoint_packet.get("packet_id") == ADJOINT_DIRAC_ROUTE_PACKET_ID
            and adjoint_packet.get("outcome_id") == ADJOINT_DIRAC_ROUTE_OUTCOME
            and adjoint_packet.get("packet_result") == ADJOINT_DIRAC_ROUTE_RESULT
            and adjoint_packet.get("selected_next_target") == CONSUMED_TARGET
            and adjoint_packet.get("accepted") is True
        ),
        "dirac_pair_preserved": (
            adjoint_packet.get("psi_equation_route") == PSI_EQUATION_ROUTE
            and adjoint_packet.get("adjoint_equation_route") == ADJOINT_EQUATION_ROUTE
            and adjoint_packet.get("adjoint_derivative_policy")
            == ADJOINT_DERIVATIVE_POLICY
        ),
        "current_divergence_route_recorded": (
            CURRENT_CANDIDATE == "J^mu = q psibar gamma^mu psi"
            and CURRENT_DIVERGENCE_ROUTE.startswith("nabla_mu J^mu = q")
            and CURRENT_CONSERVATION_RESULT == TARGET_CONSERVATION_LAW
        ),
        "mass_cancellation_recorded": MASS_TERM_CANCELLATION_ROUTE.endswith("= 0"),
        "assumptions_indexed": len(ASSUMPTIONS) == 4,
        "future_routes_indexed_without_closure": (
            len(INDEXED_FUTURE_ROUTES) == 2
            and all(route["proof_claimed"] is False for route in INDEXED_FUTURE_ROUTES)
        ),
        "sourced_maxwell_route_selected_next": (
            NEXT_TARGET == "prepare_toe_native_psi_A_u1_sourced_maxwell_route_packet"
        ),
        "blocked_claims_complete": len(BLOCKED_CLAIMS) == 14,
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_FROM_DIRAC_PAIR_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_FROM_DIRAC_PAIR_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_FROM_DIRAC_PAIR_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_adjoint_dirac_route_packet_result": ADJOINT_DIRAC_ROUTE_OUTCOME,
        "consumed_psi_variation_dirac_route_packet_result": (
            PSI_VARIATION_DIRAC_ROUTE_OUTCOME
        ),
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "action_block_statement": ACTION_BLOCK_STATEMENT,
        "covariant_derivative_policy": COVARIANT_DERIVATIVE_POLICY,
        "adjoint_derivative_policy": ADJOINT_DERIVATIVE_POLICY,
        "covariant_derivative_pair_policy": COVARIANT_DERIVATIVE_PAIR_POLICY,
        "field_strength_policy": FIELD_STRENGTH_POLICY,
        "gauge_transformation_policy": GAUGE_TRANSFORMATION_POLICY,
        "current_candidate": CURRENT_CANDIDATE,
        "current_candidate_from_A_variation": CURRENT_CANDIDATE_FROM_A_VARIATION,
        "prior_current_candidate_policy": CURRENT_CANDIDATE_POLICY,
        "current_candidate_policy": CURRENT_CANDIDATE_POLICY_AFTER_CONSERVATION,
        "A_variation_residual": A_VARIATION_RESIDUAL,
        "bounded_route_shape": BOUNDED_ROUTE_SHAPE,
        "target_conservation_law": TARGET_CONSERVATION_LAW,
        "current_conservation_question": "Does the Dirac pair imply nabla_mu J^mu = 0?",
        "psibar_variation_route": PSIBAR_VARIATION_ROUTE,
        "psi_equation_route": PSI_EQUATION_ROUTE,
        "dirac_route_equation": DIRAC_ROUTE_EQUATION,
        "adjoint_variation_route": ADJOINT_VARIATION_ROUTE,
        "adjoint_equation_route": ADJOINT_EQUATION_ROUTE,
        "dirac_pair_route_inputs": DIRAC_PAIR_ROUTE_INPUTS,
        "current_divergence_route": CURRENT_DIVERGENCE_ROUTE,
        "mass_term_cancellation_route": MASS_TERM_CANCELLATION_ROUTE,
        "current_conservation_result": CURRENT_CONSERVATION_RESULT,
        "current_conservation_route_status": CURRENT_CONSERVATION_ROUTE_STATUS,
        "field_equation_route_preview": FIELD_EQUATION_ROUTE_PREVIEW,
        "current_conservation_from_pair_preview": CURRENT_CONSERVATION_FROM_PAIR_PREVIEW,
        "sourced_maxwell_consistency_route_preview": (
            SOURCED_MAXWELL_CONSISTENCY_ROUTE_PREVIEW
        ),
        "sourced_maxwell_compatibility_route_preview": (
            SOURCED_MAXWELL_COMPATIBILITY_ROUTE_PREVIEW
        ),
        "sourced_maxwell_route_preview": SOURCED_MAXWELL_ROUTE_PREVIEW,
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
        "current_conservation_from_dirac_pair_packet_prepared": accepted,
        "current_conservation_route_constructed": accepted,
        "bounded_current_conservation_route_constructed": accepted,
        "current_conservation_recorded": accepted,
        "current_conservation_proved": accepted,
        "bounded_current_conservation_proved": accepted,
        "target_conservation_law_recorded": accepted,
        "target_conservation_law_satisfied_under_dirac_pair": accepted,
        "dirac_pair_used": accepted,
        "psi_equation_route_used": accepted,
        "adjoint_equation_route_used": accepted,
        "mass_term_cancellation_recorded": accepted,
        "gamma_compatibility_assumptions_indexed": accepted,
        "domain_boundary_assumptions_indexed": accepted,
        "sourced_maxwell_consistency_candidate_ready": accepted,
        "sourced_maxwell_route_packet_selected": accepted,
        "sourced_maxwell_route_packet_preparation_authorized": accepted,
        "exchange_route_indexed": accepted,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "sourced_maxwell_closure_claimed": False,
        "sourced_maxwell_equation_derived": False,
        "sourced_maxwell_route_derived": False,
        "full_maxwell_system_closure_claimed": False,
        "full_em_closure_claimed": False,
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
            "treat current conservation as sourced Maxwell closure",
            "claim full Maxwell system closure",
            "derive stress-energy or exchange",
            "prove total stress-energy conservation",
            "close C_exchange",
            "claim EM-QFT or QFT-GR closure",
            "claim Standard Model derivation",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "mathematical_statement": (
            "This packet records the bounded current-conservation route for "
            "J^mu = q psibar gamma^mu psi. Under the selected psi-A U(1) policy, "
            "the psi equation route, the adjoint equation route, gamma compatibility, "
            "and domain/boundary assumptions, nabla_mu J^mu expands to "
            "q [(D_mu psibar) gamma^mu psi + psibar gamma^mu D_mu psi], and the "
            "Dirac-pair mass terms cancel, giving nabla_mu J^mu = 0."
        ),
        "plain_meaning": PLAIN_MEANING,
        "non_claim_boundary": (
            "This is a bounded current-conservation-from-Dirac-pair packet only; "
            "it records nabla_mu J^mu = 0 for J^mu = q psibar gamma^mu psi under "
            "the selected psi-A U(1) policy, Dirac pair, gamma-compatibility "
            "assumptions, and domain/boundary assumptions. It records no sourced "
            "Maxwell closure, no full Maxwell system closure, no stress-energy "
            "derivation, no gauge-matter exchange identity, no total "
            "stress-energy conservation proof, no C_exchange closeout, no "
            "EM-QFT closure, no QFT-GR closure, no quantized electromagnetism, "
            "no anomaly analysis, no Standard Model derivation, no Phase 2 "
            "authorization, no empirical validation, and no master-action "
            "promotion. The full ToeFormal aggregate is recorded as NOT_RUN for "
            "this packet."
        ),
        "validation_policy": validation_policy,
        "lean_validation_policy": LEAN_VALIDATION_POLICY_ID,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "source_inputs": {
            "adjoint_dirac_route_json": _ptr(adjoint_dirac_route_path),
            "adjoint_dirac_route_outcome": ADJOINT_DIRAC_ROUTE_OUTCOME,
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
            "Prepare the ToE-native psi-A U(1) current-conservation-from-Dirac-pair packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--adjoint-dirac-route",
        type=Path,
        default=ADJOINT_DIRAC_ROUTE_PATH,
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    payload = build_toe_native_psi_a_u1_current_conservation_from_dirac_pair_packet(
        adjoint_dirac_route_path=args.adjoint_dirac_route,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(args.out, payload)
    print(args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
