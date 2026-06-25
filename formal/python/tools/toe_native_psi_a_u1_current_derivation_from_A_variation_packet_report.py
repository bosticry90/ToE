from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_interaction_action_block_definition_result_review_report import (
    ACTION_BLOCK_DENSITY,
    ACTION_BLOCK_GAUGE_TERM,
    ACTION_BLOCK_ID,
    ACTION_BLOCK_MATTER_TERM,
    ACTION_BLOCK_STATEMENT,
    ADJOINT_POLICY,
    BACKGROUND_SCOPE_POLICY,
    BOUNDARY_VARIATION_POLICY,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE_PREVIEW,
    DEFAULT_OUT as ACTION_BLOCK_RESULT_REVIEW_PATH,
    FIELD_DOMAIN_POLICY,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAMMA_MATRIX_POLICY,
    GAUGE_COVARIANT_DERIVATIVE_TRANSFORM,
    GAUGE_FIELD_POLICY,
    GAUGE_GROUP_POLICY,
    GAUGE_TRANSFORMATION_POLICY,
    INTERACTION_TERM_SHAPE,
    LEAN_VALIDATION_POLICY_ID,
    MATTER_BLOCK_EXPANSION,
    MATTER_SURFACE_POLICY,
    MINIMAL_COUPLING_EXPANSION,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as ACTION_BLOCK_RESULT_REVIEW_OUTCOME,
    PACKET_ID as ACTION_BLOCK_RESULT_REVIEW_PACKET_ID,
    PACKET_CLASSIFICATION as ACTION_BLOCK_RESULT_REVIEW_CLASSIFICATION,
    SCHEMA_ID as ACTION_BLOCK_RESULT_REVIEW_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SPIN_CONNECTION_POLICY,
    STRESS_ENERGY_POLICY,
    TETRAD_POLICY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_PACKET_20260624_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_PACKET_v0"
CURRENT_DERIVATION_PACKET_RESULT = (
    "TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_PACKET_PREPARED_"
    "A_VARIATION_CURRENT_CANDIDATE_RECORDED_NO_SOURCED_MAXWELL_CLOSURE_OR_EXCHANGE_PROOF"
)
OUTCOME_ID = CURRENT_DERIVATION_PACKET_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_current_derivation_from_A_variation_packet_records_"
    "A_variation_current_candidate_no_sourced_maxwell_closure_or_exchange_proof"
)

NEXT_TARGET = "review_toe_native_psi_A_u1_current_derivation_from_A_variation_packet_result"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_current_derivation_from_A_variation_packet_result_review"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_PACKET_20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1CurrentDerivationFromAVariationPacket.lean"
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

VARIATION_VARIABLE = "A_mu"
MATTER_A_DEPENDENT_TERM = "- q psibar gamma^mu A_mu psi"
MATTER_A_VARIATION_TERM = "- q psibar gamma^nu psi delta A_nu"
GAUGE_A_VARIATION_TERM = "nabla_mu F^{mu nu} delta A_nu"
EULER_RESIDUAL_SHAPE = "nabla_mu F^{mu nu} - J^nu"
A_VARIATION_RESIDUAL = (
    "delta_A S_{psi A} -> int d^4x sqrt(-g) "
    "[nabla_mu F^{mu nu} - J^nu] delta A_nu"
)
CURRENT_CANDIDATE_FROM_A_VARIATION = "J^nu = q psibar gamma^nu psi"
BOUNDED_ROUTE_SHAPE = "nabla_mu F^{mu nu} = J^nu"
SOURCED_GAUGE_ROUTE_STATUS = (
    "bounded sourced-gauge route shape recorded; no sourced Maxwell closure"
)
CURRENT_SOURCE_STATEMENT = (
    "psi supplies the candidate U(1) source current for A in this bounded route"
)

BLOCKED_CLAIMS = [
    "current conservation proof",
    "psi variation / Dirac derivation",
    "stress-energy derivation",
    "exchange identity",
    "total conservation proof",
    "C_exchange closeout",
    "EM-QFT closure",
    "QFT-GR closure",
    "quantized electromagnetism",
    "Standard Model derivation",
    "Phase 2 authorization",
    "empirical validation",
    "master-action promotion",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _review_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "action_block_result_review_consumed",
            "status": "accepted",
            "evidence": review.get("outcome_id"),
            "assessment": "The accepted action-block result review is the consumed input.",
        },
        {
            "row_id": "action_block_and_plus_sign_convention_preserved",
            "status": "accepted",
            "evidence": [ACTION_BLOCK_STATEMENT, COVARIANT_DERIVATIVE_POLICY],
            "assessment": "The bounded action block and plus-sign D_mu convention are preserved.",
        },
        {
            "row_id": "matter_A_dependent_term_identified",
            "status": "accepted",
            "evidence": MATTER_A_DEPENDENT_TERM,
            "assessment": "The A_mu-dependent matter term is identified as the variation input.",
        },
        {
            "row_id": "matter_and_gauge_A_variation_terms_recorded",
            "status": "accepted",
            "evidence": [MATTER_A_VARIATION_TERM, GAUGE_A_VARIATION_TERM],
            "assessment": "The matter and gauge contributions to the A-variation route are recorded.",
        },
        {
            "row_id": "current_candidate_exposed_by_A_variation",
            "status": "accepted",
            "evidence": CURRENT_CANDIDATE_FROM_A_VARIATION,
            "assessment": "The candidate U(1) matter current is recorded under the selected convention.",
        },
        {
            "row_id": "bounded_residual_and_route_shape_recorded",
            "status": "accepted",
            "evidence": [A_VARIATION_RESIDUAL, BOUNDED_ROUTE_SHAPE],
            "assessment": "The packet records a bounded residual and route shape only.",
        },
        {
            "row_id": "conservation_exchange_closure_and_promotion_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "All conservation, exchange, closure, empirical, Phase 2, and promotion claims remain blocked.",
        },
        {
            "row_id": "result_review_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is the packet result review.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_current_derivation_from_A_variation_packet",
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


def build_toe_native_psi_a_u1_current_derivation_from_A_variation_packet(
    *,
    action_block_result_review_path: Path = ACTION_BLOCK_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(action_block_result_review_path)
    review_criteria = _review_criteria(review)
    acceptance_criteria = {
        "consumes_expected_action_block_result_review": (
            review.get("schema_id") == ACTION_BLOCK_RESULT_REVIEW_SCHEMA_ID
            and review.get("packet_id") == ACTION_BLOCK_RESULT_REVIEW_PACKET_ID
            and review.get("outcome_id") == ACTION_BLOCK_RESULT_REVIEW_OUTCOME
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "action_block_and_conventions_preserved": (
            review.get("action_block_statement") == ACTION_BLOCK_STATEMENT
            and review.get("action_block_density") == ACTION_BLOCK_DENSITY
            and review.get("action_block_matter_term") == ACTION_BLOCK_MATTER_TERM
            and review.get("action_block_gauge_term") == ACTION_BLOCK_GAUGE_TERM
            and review.get("covariant_derivative_policy") == COVARIANT_DERIVATIVE_POLICY
            and review.get("field_strength_policy") == FIELD_STRENGTH_POLICY
            and review.get("gauge_transformation_policy") == GAUGE_TRANSFORMATION_POLICY
            and review.get("gauge_covariant_derivative_transform")
            == GAUGE_COVARIANT_DERIVATIVE_TRANSFORM
        ),
        "matter_A_dependent_term_matches_expansion": (
            review.get("minimal_coupling_expansion") == MINIMAL_COUPLING_EXPANSION
            and review.get("matter_block_expansion") == MATTER_BLOCK_EXPANSION
            and review.get("interaction_term_shape") == INTERACTION_TERM_SHAPE
            and INTERACTION_TERM_SHAPE == MATTER_A_DEPENDENT_TERM
        ),
        "bounded_A_variation_terms_recorded": (
            MATTER_A_VARIATION_TERM.startswith("- q psibar")
            and GAUGE_A_VARIATION_TERM.startswith("nabla_mu F")
            and EULER_RESIDUAL_SHAPE in A_VARIATION_RESIDUAL
            and BOUNDED_ROUTE_SHAPE == "nabla_mu F^{mu nu} = J^nu"
        ),
        "current_candidate_recorded_under_selected_convention": (
            CURRENT_CANDIDATE_FROM_A_VARIATION == "J^nu = q psibar gamma^nu psi"
            and CURRENT_CANDIDATE_PREVIEW == "J^mu = q psibar gamma^mu psi"
        ),
        "blocked_claims_complete": len(BLOCKED_CLAIMS) == 13,
        "no_forbidden_closure_or_exchange_claims": all(
            review.get(key, False) is False
            for key in [
                "current_conservation_proved",
                "psi_variation_result_derived",
                "dirac_equation_derived",
                "psi_stress_energy_derived",
                "A_psi_exchange_identity_proved",
                "exchange_proof_claimed",
                "total_conservation_proved",
                "total_stress_energy_conservation_proved",
                "C_exchange_closeout",
                "C_exchange_definition_closeout",
                "em_qft_closure_claimed",
                "qft_gr_closure_claimed",
                "quantized_electromagnetism_claimed",
                "standard_model_derivation_claimed",
                "phase2_authorized",
                "empirical_validation_claimed",
                "master_action_promoted",
            ]
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "next_target_is_result_review": NEXT_TARGET
        == "review_toe_native_psi_A_u1_current_derivation_from_A_variation_packet_result",
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_PACKET_"
            "REQUIRES_REMEDIATION"
        ),
        "current_derivation_packet_result": CURRENT_DERIVATION_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "action_block_result_review_schema_id": ACTION_BLOCK_RESULT_REVIEW_SCHEMA_ID,
        "action_block_result_review_packet_id": ACTION_BLOCK_RESULT_REVIEW_PACKET_ID,
        "action_block_result_review_outcome": ACTION_BLOCK_RESULT_REVIEW_OUTCOME,
        "action_block_result_review_classification": ACTION_BLOCK_RESULT_REVIEW_CLASSIFICATION,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "matter_surface_policy": MATTER_SURFACE_POLICY,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "gauge_field_policy": GAUGE_FIELD_POLICY,
        "action_block_id": ACTION_BLOCK_ID,
        "action_block_statement": ACTION_BLOCK_STATEMENT,
        "action_block_density": ACTION_BLOCK_DENSITY,
        "action_block_matter_term": ACTION_BLOCK_MATTER_TERM,
        "action_block_gauge_term": ACTION_BLOCK_GAUGE_TERM,
        "covariant_derivative_policy": COVARIANT_DERIVATIVE_POLICY,
        "field_strength_policy": FIELD_STRENGTH_POLICY,
        "gauge_transformation_policy": GAUGE_TRANSFORMATION_POLICY,
        "gauge_covariant_derivative_transform": GAUGE_COVARIANT_DERIVATIVE_TRANSFORM,
        "minimal_coupling_expansion": MINIMAL_COUPLING_EXPANSION,
        "matter_block_expansion": MATTER_BLOCK_EXPANSION,
        "interaction_term_shape": INTERACTION_TERM_SHAPE,
        "current_candidate_preview": CURRENT_CANDIDATE_PREVIEW,
        "stress_energy_policy": STRESS_ENERGY_POLICY,
        "adjoint_policy": ADJOINT_POLICY,
        "gamma_matrix_policy": GAMMA_MATRIX_POLICY,
        "tetrad_policy": TETRAD_POLICY,
        "spin_connection_policy": SPIN_CONNECTION_POLICY,
        "field_domain_policy": FIELD_DOMAIN_POLICY,
        "boundary_variation_policy": BOUNDARY_VARIATION_POLICY,
        "background_scope_policy": BACKGROUND_SCOPE_POLICY,
        "variation_variable": VARIATION_VARIABLE,
        "matter_A_dependent_term": MATTER_A_DEPENDENT_TERM,
        "matter_A_variation_term": MATTER_A_VARIATION_TERM,
        "gauge_A_variation_term": GAUGE_A_VARIATION_TERM,
        "Euler_residual_shape": EULER_RESIDUAL_SHAPE,
        "A_variation_residual": A_VARIATION_RESIDUAL,
        "current_candidate_from_A_variation": CURRENT_CANDIDATE_FROM_A_VARIATION,
        "bounded_route_shape": BOUNDED_ROUTE_SHAPE,
        "sourced_gauge_route_status": SOURCED_GAUGE_ROUTE_STATUS,
        "current_source_statement": CURRENT_SOURCE_STATEMENT,
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "current_derivation_packet_prepared": accepted,
        "A_variation_current_derivation_packet_prepared": accepted,
        "A_variation_route_recorded": accepted,
        "A_variation_result_recorded": accepted,
        "A_variation_current_candidate_recorded": accepted,
        "bounded_A_variation_residual_recorded": accepted,
        "matter_A_dependent_term_identified": accepted,
        "matter_A_variation_term_recorded": accepted,
        "gauge_A_variation_term_recorded": accepted,
        "candidate_current_identified": accepted,
        "bounded_sourced_gauge_route_shape_recorded": accepted,
        "sourced_gauge_equation_route_shape_recorded": accepted,
        "psi_supplies_candidate_source_current": accepted,
        "selected_conventions_preserved": accepted,
        "result_review_preparation_authorized": accepted,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "A_variation_result_derived": False,
        "A_variation_current_derived": False,
        "A_variation_full_EL_derivation_closed": False,
        "psi_variation_result_derived": False,
        "psi_field_equation_derived": False,
        "J_nu_derived": False,
        "matter_current_J_nu_derived": False,
        "current_derived": False,
        "current_route_derived": False,
        "full_current_derivation_closed": False,
        "current_conservation_proved": False,
        "sourced_maxwell_equation_derived": False,
        "sourced_maxwell_route_derived": False,
        "sourced_maxwell_closure_claimed": False,
        "full_sourced_maxwell_derivation_claimed": False,
        "dirac_equation_derived": False,
        "stress_energy_derived": False,
        "psi_stress_energy_derived": False,
        "T_psi_derived": False,
        "A_psi_exchange_identity_proved": False,
        "exchange_identity_proved": False,
        "exchange_proof_claimed": False,
        "gauge_matter_exchange_proved": False,
        "matter_gauge_exchange_proved": False,
        "total_conservation_proved": False,
        "total_stress_energy_conservation_proved": False,
        "T_total_conservation_proved": False,
        "C_exchange_closeout": False,
        "C_exchange_definition_closeout": False,
        "c_exchange_functional_defined": False,
        "c_exchange_rule_family_decided": False,
        "c_exchange_rule_proved": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "standard_model_derivation_claimed": False,
        "quantized_electromagnetism_claimed": False,
        "anomaly_analysis_performed": False,
        "anomaly_cancellation_claimed": False,
        "empirical_validation_claimed": False,
        "phase2_authorized": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "critical_gate_fail_conditions": [
            "treat candidate current recording as current conservation proof",
            "treat bounded route shape as sourced Maxwell closure",
            "derive the psi equation or Dirac equation",
            "derive stress-energy or exchange",
            "prove total conservation",
            "close C_exchange",
            "claim EM-QFT or QFT-GR closure",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "mathematical_statement": (
            "This packet records the bounded A-variation route for the selected "
            "psi-A U(1) action block. With D_mu psi = (nabla_mu + i q A_mu) psi, "
            "the A_mu-dependent matter term is - q psibar gamma^mu A_mu psi. "
            "Together with the gauge variation, the recorded residual shape is "
            "nabla_mu F^{mu nu} - J^nu, with J^nu = q psibar gamma^nu psi as the "
            "candidate current."
        ),
        "plain_meaning": (
            "The matter field psi is now recorded as the candidate source of the "
            "U(1) gauge field A in a bounded classical route. Conservation, "
            "exchange, quantum, seam, empirical, and promotion claims remain blocked."
        ),
        "non_claim_boundary": (
            "This is a bounded A-variation current packet only; it records a "
            "candidate current and route shape, but it records no current "
            "conservation proof, no psi variation or Dirac derivation, no "
            "stress-energy derivation, no exchange identity, no total conservation "
            "proof, no C_exchange closeout, no sourced Maxwell closure, no EM-QFT "
            "closure, no QFT-GR closure, no quantized electromagnetism, no Standard "
            "Model derivation, no Phase 2 authorization, no empirical validation, "
            "and no master-action promotion. The full ToeFormal aggregate is "
            "recorded as NOT_RUN for this packet."
        ),
        "validation_policy": validation_policy,
        "lean_validation_policy": LEAN_VALIDATION_POLICY_ID,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "source_inputs": {
            "action_block_result_review_json": _ptr(action_block_result_review_path),
            "action_block_result_review_outcome": ACTION_BLOCK_RESULT_REVIEW_OUTCOME,
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
        description="Prepare the ToE-native psi-A U(1) A-variation current packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--action-block-result-review",
        type=Path,
        default=ACTION_BLOCK_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    payload = build_toe_native_psi_a_u1_current_derivation_from_A_variation_packet(
        action_block_result_review_path=args.action_block_result_review,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(args.out, payload)
    print(args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
