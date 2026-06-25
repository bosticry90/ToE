from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_current_derivation_from_A_variation_packet_report import (
    ACTION_BLOCK_DENSITY,
    ACTION_BLOCK_GAUGE_TERM,
    ACTION_BLOCK_ID,
    ACTION_BLOCK_MATTER_TERM,
    ACTION_BLOCK_STATEMENT,
    A_VARIATION_RESIDUAL,
    BACKGROUND_SCOPE_POLICY,
    BLOCKED_CLAIMS as CURRENT_PACKET_BLOCKED_CLAIMS,
    BOUNDED_ROUTE_SHAPE,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE_FROM_A_VARIATION,
    CURRENT_DERIVATION_PACKET_RESULT,
    CURRENT_SOURCE_STATEMENT,
    DEFAULT_OUT as CURRENT_PACKET_PATH,
    EULER_RESIDUAL_SHAPE,
    FIELD_DOMAIN_POLICY,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_A_VARIATION_TERM,
    GAUGE_COVARIANT_DERIVATIVE_TRANSFORM,
    GAUGE_FIELD_POLICY,
    GAUGE_GROUP_POLICY,
    GAUGE_TRANSFORMATION_POLICY,
    INTERACTION_TERM_SHAPE,
    LEAN_VALIDATION_POLICY_ID,
    MATTER_A_DEPENDENT_TERM,
    MATTER_A_VARIATION_TERM,
    MATTER_BLOCK_EXPANSION,
    MATTER_SURFACE_POLICY,
    MINIMAL_COUPLING_EXPANSION,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as CURRENT_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as CURRENT_PACKET_CLASSIFICATION,
    PACKET_ID as CURRENT_PACKET_ID,
    SCHEMA_ID as CURRENT_PACKET_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCED_GAUGE_ROUTE_STATUS,
    STRESS_ENERGY_POLICY,
    VARIATION_VARIABLE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_RESULT_REVIEW_20260624_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_RESULT_REVIEW_"
    "ACCEPTS_A_VARIATION_CURRENT_CANDIDATE_NO_CURRENT_CONSERVATION_OR_EXCHANGE_PROOF"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_current_derivation_from_A_variation_result_review_accepts_"
    "A_variation_current_candidate_no_current_conservation_or_exchange_proof"
)

NEXT_TARGET = "prepare_toe_native_psi_A_u1_current_conservation_obligation_packet"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_current_conservation_obligation_packet_preparation"
ALTERNATE_NEXT_TARGET = "prepare_toe_native_psi_A_u1_current_conservation_route_packet"
CURRENT_CONSERVATION_QUESTION = "Does the candidate current satisfy nabla_mu J^mu = 0?"
GAUGE_SYMMETRY_ROUTE_PREVIEW = "gauge invariance -> current conservation"
FIELD_EQUATION_ROUTE_PREVIEW = "psi equation + psibar equation -> current conservation"
NEXT_OBLIGATION_PACKET_EXPECTED_OUTCOME = (
    "TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_OBLIGATION_PACKET_PREPARED_"
    "CURRENT_CONSERVATION_REQUIREMENTS_INDEXED_NO_CONSERVATION_PROOF_OR_EM_QFT_CLOSURE"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_RESULT_REVIEW_"
    "20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1CurrentDerivationFromAVariationResultReview.lean"
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

ACCEPTED_REVIEW_FINDINGS = [
    "A-variation route shape recorded",
    "current candidate indexed",
    "J^nu = q psibar gamma^nu psi",
    "sourced-gauge residual shape recorded",
    "selected plus-sign D_mu convention preserved",
]

BLOCKED_CLAIMS = [
    "current conservation proof",
    "psi variation / Dirac derivation",
    "stress-energy derivation",
    "exchange identity",
    "total conservation proof",
    "C_exchange closeout",
    "sourced Maxwell closure",
    "EM-QFT closure",
    "QFT-GR closure",
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


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "A_variation_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("outcome_id"),
            "assessment": "The bounded A-variation current packet is the consumed input.",
        },
        {
            "row_id": "A_variation_route_shape_recorded",
            "status": "accepted",
            "evidence": [A_VARIATION_RESIDUAL, BOUNDED_ROUTE_SHAPE],
            "assessment": "The A-variation route shape and sourced-gauge route shape are recorded.",
        },
        {
            "row_id": "current_candidate_indexed",
            "status": "accepted",
            "evidence": CURRENT_CANDIDATE_FROM_A_VARIATION,
            "assessment": "The candidate current is indexed under the selected convention.",
        },
        {
            "row_id": "sourced_gauge_residual_shape_recorded",
            "status": "accepted",
            "evidence": EULER_RESIDUAL_SHAPE,
            "assessment": "The residual shape nabla_mu F^{mu nu} - J^nu is recorded.",
        },
        {
            "row_id": "plus_sign_D_mu_convention_preserved",
            "status": "accepted",
            "evidence": [COVARIANT_DERIVATIVE_POLICY, GAUGE_TRANSFORMATION_POLICY],
            "assessment": "The selected plus-sign D_mu and matched gauge transform are preserved.",
        },
        {
            "row_id": "current_conservation_obligation_selected_next",
            "status": "accepted",
            "evidence": [CURRENT_CONSERVATION_QUESTION, NEXT_TARGET],
            "assessment": "The next target is the cautious current-conservation obligation packet.",
        },
        {
            "row_id": "route_choices_indexed_without_proof",
            "status": "accepted",
            "evidence": [GAUGE_SYMMETRY_ROUTE_PREVIEW, FIELD_EQUATION_ROUTE_PREVIEW],
            "assessment": "Possible conservation routes are indexed but not proved.",
        },
        {
            "row_id": "conservation_exchange_closure_and_promotion_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "All conservation, exchange, closure, empirical, Phase 2, and promotion claims remain blocked.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_current_derivation_from_A_variation_result_review",
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


def build_toe_native_psi_a_u1_current_derivation_from_A_variation_result_review(
    *,
    current_packet_path: Path = CURRENT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(current_packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_current_packet": (
            packet.get("schema_id") == CURRENT_PACKET_SCHEMA_ID
            and packet.get("packet_id") == CURRENT_PACKET_ID
            and packet.get("outcome_id") == CURRENT_PACKET_OUTCOME
            and packet.get("current_derivation_packet_result")
            == CURRENT_DERIVATION_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "A_variation_route_shape_recorded": (
            packet.get("A_variation_residual") == A_VARIATION_RESIDUAL
            and packet.get("bounded_route_shape") == BOUNDED_ROUTE_SHAPE
            and packet.get("A_variation_route_recorded") is True
            and packet.get("bounded_A_variation_residual_recorded") is True
        ),
        "current_candidate_indexed": (
            packet.get("current_candidate_from_A_variation")
            == CURRENT_CANDIDATE_FROM_A_VARIATION
            and packet.get("A_variation_current_candidate_recorded") is True
            and packet.get("candidate_current_identified") is True
        ),
        "sourced_gauge_residual_shape_recorded": (
            packet.get("Euler_residual_shape") == EULER_RESIDUAL_SHAPE
            and packet.get("sourced_gauge_equation_route_shape_recorded") is True
            and packet.get("sourced_gauge_route_status") == SOURCED_GAUGE_ROUTE_STATUS
        ),
        "selected_plus_sign_convention_preserved": (
            packet.get("covariant_derivative_policy") == COVARIANT_DERIVATIVE_POLICY
            and packet.get("gauge_transformation_policy") == GAUGE_TRANSFORMATION_POLICY
            and packet.get("gauge_covariant_derivative_transform")
            == GAUGE_COVARIANT_DERIVATIVE_TRANSFORM
            and packet.get("selected_conventions_preserved") is True
        ),
        "blocked_claims_complete": (
            len(BLOCKED_CLAIMS) == 12 and len(CURRENT_PACKET_BLOCKED_CLAIMS) == 13
        ),
        "no_forbidden_conservation_exchange_or_closure_claims": all(
            packet.get(key, False) is False
            for key in [
                "A_variation_result_derived",
                "A_variation_current_derived",
                "J_nu_derived",
                "current_conservation_proved",
                "psi_variation_result_derived",
                "dirac_equation_derived",
                "stress_energy_derived",
                "psi_stress_energy_derived",
                "exchange_identity_proved",
                "A_psi_exchange_identity_proved",
                "total_conservation_proved",
                "total_stress_energy_conservation_proved",
                "C_exchange_closeout",
                "C_exchange_definition_closeout",
                "sourced_maxwell_closure_claimed",
                "em_qft_closure_claimed",
                "qft_gr_closure_claimed",
                "phase2_authorized",
                "empirical_validation_claimed",
                "master_action_promoted",
            ]
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "next_target_is_current_conservation_obligation_packet": NEXT_TARGET
        == "prepare_toe_native_psi_A_u1_current_conservation_obligation_packet",
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_RESULT_REVIEW"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_RESULT_REVIEW_"
            "REQUIRES_REMEDIATION"
        ),
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "alternate_next_target": ALTERNATE_NEXT_TARGET,
        "current_conservation_question": CURRENT_CONSERVATION_QUESTION,
        "gauge_symmetry_route_preview": GAUGE_SYMMETRY_ROUTE_PREVIEW,
        "field_equation_route_preview": FIELD_EQUATION_ROUTE_PREVIEW,
        "next_obligation_packet_expected_outcome": NEXT_OBLIGATION_PACKET_EXPECTED_OUTCOME,
        "current_packet_schema_id": CURRENT_PACKET_SCHEMA_ID,
        "current_packet_id": CURRENT_PACKET_ID,
        "current_packet_outcome": CURRENT_PACKET_OUTCOME,
        "current_packet_classification": CURRENT_PACKET_CLASSIFICATION,
        "current_derivation_packet_result": CURRENT_DERIVATION_PACKET_RESULT,
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
        "stress_energy_policy": STRESS_ENERGY_POLICY,
        "field_domain_policy": FIELD_DOMAIN_POLICY,
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
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
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
        "A_variation_route_shape_accepted": accepted,
        "A_variation_route_shape_recorded": accepted,
        "current_candidate_accepted": accepted,
        "current_candidate_indexed": accepted,
        "candidate_current_from_A_variation_accepted": accepted,
        "sourced_gauge_residual_shape_accepted": accepted,
        "sourced_gauge_residual_shape_recorded": accepted,
        "bounded_current_route_accepted": accepted,
        "bounded_sourced_gauge_route_shape_accepted": accepted,
        "plus_sign_D_mu_convention_preserved": accepted,
        "selected_conventions_preserved": accepted,
        "current_conservation_obligation_packet_selected": accepted,
        "current_conservation_obligation_packet_preparation_authorized": accepted,
        "current_conservation_route_packet_selected": False,
        "gauge_symmetry_route_indexed": accepted,
        "field_equation_route_indexed": accepted,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "A_variation_result_derived": False,
        "A_variation_current_derived": False,
        "J_nu_derived": False,
        "current_conservation_proved": False,
        "psi_variation_result_derived": False,
        "psi_field_equation_derived": False,
        "dirac_equation_derived": False,
        "stress_energy_derived": False,
        "psi_stress_energy_derived": False,
        "T_psi_derived": False,
        "exchange_identity_proved": False,
        "A_psi_exchange_identity_proved": False,
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
        "sourced_maxwell_closure_claimed": False,
        "sourced_maxwell_equation_derived": False,
        "full_sourced_maxwell_derivation_claimed": False,
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
            "treat result review as current conservation proof",
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
            "This review accepts the bounded A-variation current packet only. "
            "It accepts that the packet records delta_A S_{psi A} with residual "
            "shape nabla_mu F^{mu nu} - J^nu and current candidate "
            "J^nu = q psibar gamma^nu psi under the selected plus-sign D_mu convention."
        ),
        "plain_meaning": (
            "The matter field psi is now positioned as the candidate source for "
            "the U(1) gauge field A. The next question is whether that candidate "
            "current is conserved."
        ),
        "non_claim_boundary": (
            "This is an A-variation current result review only; it accepts the "
            "candidate current and bounded route shape, but it records no current "
            "conservation proof, no psi variation or Dirac derivation, no "
            "stress-energy derivation, no exchange identity, no total conservation "
            "proof, no C_exchange closeout, no sourced Maxwell closure, no EM-QFT "
            "closure, no QFT-GR closure, no Phase 2 authorization, no empirical "
            "validation, and no master-action promotion. The full ToeFormal "
            "aggregate is recorded as NOT_RUN for this review."
        ),
        "validation_policy": validation_policy,
        "lean_validation_policy": LEAN_VALIDATION_POLICY_ID,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "source_inputs": {
            "current_packet_json": _ptr(current_packet_path),
            "current_packet_outcome": CURRENT_PACKET_OUTCOME,
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
        description="Review the ToE-native psi-A U(1) A-variation current packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--current-packet", type=Path, default=CURRENT_PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    payload = build_toe_native_psi_a_u1_current_derivation_from_A_variation_result_review(
        current_packet_path=args.current_packet,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(args.out, payload)
    print(args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
