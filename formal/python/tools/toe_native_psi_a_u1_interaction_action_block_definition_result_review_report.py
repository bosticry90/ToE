from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_current_and_exchange_derivation_obligation_packet_report import (
    ADJOINT_POLICY,
    BACKGROUND_SCOPE_POLICY,
    BOUNDARY_VARIATION_POLICY,
    FIELD_DOMAIN_POLICY,
    GAMMA_MATRIX_POLICY,
    SPIN_CONNECTION_POLICY,
    TETRAD_POLICY,
)
from formal.python.tools.toe_native_psi_a_u1_interaction_action_block_definition_packet_report import (
    ACTION_BLOCK_DENSITY,
    ACTION_BLOCK_DEFINITION_PACKET_RESULT,
    ACTION_BLOCK_GAUGE_TERM,
    ACTION_BLOCK_ID,
    ACTION_BLOCK_MATTER_TERM,
    ACTION_BLOCK_STATEMENT,
    BLOCKED_CLAIMS as ACTION_BLOCK_BLOCKED_CLAIMS,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE_POLICY,
    CURRENT_CANDIDATE_PREVIEW,
    DEFAULT_OUT as ACTION_BLOCK_PACKET_PATH,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_COVARIANT_DERIVATIVE_TRANSFORM,
    GAUGE_FIELD_POLICY,
    GAUGE_GROUP_POLICY,
    GAUGE_TRANSFORMATION_POLICY,
    INTERACTION_TERM_SHAPE,
    LEAN_VALIDATION_POLICY_ID,
    MINIMAL_COUPLING_EXPANSION,
    MATTER_SURFACE_POLICY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as ACTION_BLOCK_PACKET_OUTCOME,
    PACKET_ID as ACTION_BLOCK_PACKET_ID,
    SCHEMA_ID as ACTION_BLOCK_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    STRESS_ENERGY_POLICY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_RESULT_REVIEW_20260624_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_RESULT_REVIEW_"
    "ACCEPTS_ACTION_BLOCK_DEFINITION_NO_CURRENT_OR_EXCHANGE_DERIVATION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_interaction_action_block_definition_result_review_accepts_"
    "action_block_definition_no_current_or_exchange_derivation"
)

NEXT_TARGET = "prepare_toe_native_psi_A_u1_current_derivation_from_A_variation_packet"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_current_derivation_from_A_variation_packet_preparation"
ALTERNATE_NEXT_TARGET = "prepare_toe_native_psi_A_u1_action_variation_policy_packet"
FUTURE_ROUTE_QUESTION = (
    "Does varying A_mu in this bounded psi-A action produce the expected current route?"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_RESULT_REVIEW_"
    "20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1InteractionActionBlockDefinitionResultReview.lean"
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

MATTER_BLOCK_EXPANSION = (
    "psibar i gamma^mu nabla_mu psi - q psibar gamma^mu A_mu psi - m psibar psi"
)

BLOCKED_CLAIMS = [
    "A-variation result",
    "psi variation result",
    "J^nu derivation",
    "current conservation proof",
    "sourced Maxwell derivation",
    "Dirac derivation",
    "psi stress-energy derivation",
    "exchange proof",
    "total conservation proof",
    "C_exchange closeout",
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
            "row_id": "action_block_packet_accepted",
            "status": "accepted",
            "evidence": packet.get("outcome_id"),
            "assessment": "The action-block definition packet is accepted as the review input.",
        },
        {
            "row_id": "action_block_defined",
            "status": "accepted",
            "evidence": ACTION_BLOCK_STATEMENT,
            "assessment": "The bounded psi-A U(1) action block is defined.",
        },
        {
            "row_id": "plus_sign_D_mu_convention_preserved",
            "status": "accepted",
            "evidence": COVARIANT_DERIVATIVE_POLICY,
            "assessment": "The plus-sign covariant derivative convention is preserved.",
        },
        {
            "row_id": "matched_gauge_transform_policy_preserved",
            "status": "accepted",
            "evidence": [
                GAUGE_TRANSFORMATION_POLICY,
                GAUGE_COVARIANT_DERIVATIVE_TRANSFORM,
            ],
            "assessment": "The matching plus-sign U(1) gauge transformation policy is preserved.",
        },
        {
            "row_id": "F_equals_dA_preserved",
            "status": "accepted",
            "evidence": FIELD_STRENGTH_POLICY,
            "assessment": "The U(1) field-strength policy remains F = dA.",
        },
        {
            "row_id": "psibar_and_spin_geometry_indexed",
            "status": "accepted",
            "evidence": [
                ADJOINT_POLICY,
                GAMMA_MATRIX_POLICY,
                TETRAD_POLICY,
                SPIN_CONNECTION_POLICY,
            ],
            "assessment": "The psibar convention and spin-geometry placeholders remain indexed.",
        },
        {
            "row_id": "domain_and_boundary_policy_preserved",
            "status": "accepted",
            "evidence": [FIELD_DOMAIN_POLICY, BOUNDARY_VARIATION_POLICY],
            "assessment": "The field-domain and boundary-variation policies remain preserved.",
        },
        {
            "row_id": "current_stress_exchange_indexed_only",
            "status": "accepted",
            "evidence": [CURRENT_CANDIDATE_POLICY, STRESS_ENERGY_POLICY],
            "assessment": "Current, stress-energy, and exchange remain indexed policy objects only.",
        },
        {
            "row_id": "matter_block_expansion_recorded_without_current_derivation",
            "status": "accepted",
            "evidence": [MATTER_BLOCK_EXPANSION, CURRENT_CANDIDATE_PREVIEW],
            "assessment": "The interaction term is recorded as future A-variation input only.",
        },
        {
            "row_id": "no_current_exchange_closure_or_promotion",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "All current, exchange, closure, empirical, Phase 2, and promotion claims remain blocked.",
        },
        {
            "row_id": "direct_current_derivation_packet_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is the bounded A-variation current-derivation packet.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_interaction_action_block_definition_result_review",
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


def build_toe_native_psi_a_u1_interaction_action_block_definition_result_review(
    *,
    action_block_packet_path: Path = ACTION_BLOCK_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(action_block_packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_action_block_result_review_target": (
            packet.get("schema_id") == ACTION_BLOCK_SCHEMA_ID
            and packet.get("packet_id") == ACTION_BLOCK_PACKET_ID
            and packet.get("outcome_id") == ACTION_BLOCK_PACKET_OUTCOME
            and packet.get("action_block_definition_packet_result")
            == ACTION_BLOCK_DEFINITION_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "action_block_definition_preserved": (
            packet.get("action_block_id") == ACTION_BLOCK_ID
            and packet.get("action_block_statement") == ACTION_BLOCK_STATEMENT
            and packet.get("action_block_density") == ACTION_BLOCK_DENSITY
            and packet.get("action_block_matter_term") == ACTION_BLOCK_MATTER_TERM
            and packet.get("action_block_gauge_term") == ACTION_BLOCK_GAUGE_TERM
            and packet.get("interaction_action_block_defined") is True
        ),
        "selected_conventions_preserved": (
            packet.get("covariant_derivative_policy") == COVARIANT_DERIVATIVE_POLICY
            and packet.get("field_strength_policy") == FIELD_STRENGTH_POLICY
            and packet.get("gauge_transformation_policy") == GAUGE_TRANSFORMATION_POLICY
            and packet.get("gauge_covariant_derivative_transform")
            == GAUGE_COVARIANT_DERIVATIVE_TRANSFORM
        ),
        "interaction_shape_recorded_without_derivation": (
            packet.get("minimal_coupling_expansion") == MINIMAL_COUPLING_EXPANSION
            and packet.get("interaction_term_shape") == INTERACTION_TERM_SHAPE
            and packet.get("current_candidate_preview") == CURRENT_CANDIDATE_PREVIEW
            and packet.get("current_derived") is False
            and packet.get("J_nu_derived") is False
        ),
        "indexed_policy_objects_preserved": (
            ADJOINT_POLICY.startswith("psibar =")
            and "gamma" in GAMMA_MATRIX_POLICY
            and "tetrad" in TETRAD_POLICY
            and "spin connection" in SPIN_CONNECTION_POLICY
            and packet.get("field_domain_policy") == FIELD_DOMAIN_POLICY
            and packet.get("boundary_variation_policy") == BOUNDARY_VARIATION_POLICY
            and packet.get("current_candidate_policy") == CURRENT_CANDIDATE_POLICY
            and packet.get("stress_energy_policy") == STRESS_ENERGY_POLICY
        ),
        "blocked_claims_complete": (
            len(BLOCKED_CLAIMS) == 15
            and len(ACTION_BLOCK_BLOCKED_CLAIMS) == 15
        ),
        "no_forbidden_derivations_or_promotions": all(
            packet.get(key, False) is False
            for key in [
                "A_variation_result_derived",
                "A_variation_current_derived",
                "psi_variation_result_derived",
                "psi_field_equation_derived",
                "J_nu_derived",
                "matter_current_J_nu_derived",
                "current_derived",
                "current_conservation_proved",
                "sourced_maxwell_equation_derived",
                "dirac_equation_derived",
                "psi_stress_energy_derived",
                "A_psi_exchange_identity_proved",
                "gauge_matter_exchange_proved",
                "matter_gauge_exchange_proved",
                "total_stress_energy_conservation_proved",
                "C_exchange_definition_closeout",
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
        "next_target_is_direct_A_variation_current_derivation": NEXT_TARGET
        == "prepare_toe_native_psi_A_u1_current_derivation_from_A_variation_packet",
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_REVIEW"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_RESULT_REVIEW_"
            "REQUIRES_REMEDIATION"
        ),
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "alternate_next_target": ALTERNATE_NEXT_TARGET,
        "future_route_question": FUTURE_ROUTE_QUESTION,
        "action_block_schema_id": ACTION_BLOCK_SCHEMA_ID,
        "action_block_packet_id": ACTION_BLOCK_PACKET_ID,
        "action_block_packet_outcome": ACTION_BLOCK_PACKET_OUTCOME,
        "action_block_definition_packet_result": ACTION_BLOCK_DEFINITION_PACKET_RESULT,
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
        "current_candidate_policy": CURRENT_CANDIDATE_POLICY,
        "stress_energy_policy": STRESS_ENERGY_POLICY,
        "adjoint_policy": ADJOINT_POLICY,
        "gamma_matrix_policy": GAMMA_MATRIX_POLICY,
        "tetrad_policy": TETRAD_POLICY,
        "spin_connection_policy": SPIN_CONNECTION_POLICY,
        "field_domain_policy": FIELD_DOMAIN_POLICY,
        "boundary_variation_policy": BOUNDARY_VARIATION_POLICY,
        "background_scope_policy": BACKGROUND_SCOPE_POLICY,
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
        "action_block_definition_accepted": accepted,
        "action_block_defined_confirmed": accepted,
        "plus_sign_D_mu_convention_preserved": accepted,
        "matched_gauge_transform_policy_preserved": accepted,
        "F_equals_dA_preserved": accepted,
        "psibar_convention_indexed": accepted,
        "spin_geometry_placeholders_preserved": accepted,
        "domain_and_boundary_policy_preserved": accepted,
        "current_candidate_indexed_only": accepted,
        "stress_energy_names_indexed_only": accepted,
        "exchange_policy_indexed_only": accepted,
        "interaction_term_recorded_as_future_variation_input": accepted,
        "direct_A_variation_current_derivation_packet_selected": accepted,
        "current_derivation_packet_preparation_authorized": accepted,
        "action_variation_policy_packet_selected": False,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "A_variation_result_derived": False,
        "A_variation_current_derived": False,
        "psi_variation_result_derived": False,
        "psi_field_equation_derived": False,
        "J_nu_derived": False,
        "matter_current_J_nu_derived": False,
        "current_derived": False,
        "current_route_derived": False,
        "current_conservation_proved": False,
        "sourced_maxwell_equation_derived": False,
        "sourced_maxwell_route_derived": False,
        "dirac_equation_derived": False,
        "psi_stress_energy_derived": False,
        "T_psi_derived": False,
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
            "treat result review as A-variation result",
            "treat result review as psi variation result",
            "claim J^nu derivation",
            "claim current conservation",
            "derive sourced Maxwell",
            "derive the Dirac equation",
            "derive psi stress-energy",
            "prove exchange",
            "prove total conservation",
            "close C_exchange",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "mathematical_statement": (
            "This result review accepts that the bounded psi-A U(1) action block "
            "now exists with D_mu psi = (nabla_mu + i q A_mu) psi and "
            "F_{mu nu} = partial_mu A_nu - partial_nu A_mu. It records the "
            "schematic matter-block expansion and treats the interaction term as "
            "future input for a bounded A-variation current-derivation attempt, "
            "without deriving the current."
        ),
        "non_claim_boundary": (
            "This is an action-block definition result review only. It accepts "
            "the bounded minimal U(1) Dirac-gauge action block and selects a "
            "future A-variation current-derivation packet, but it records no "
            "A-variation result, no psi variation result, no J^nu derivation, "
            "no current conservation proof, no sourced Maxwell derivation, no "
            "Dirac derivation, no psi stress-energy derivation, no exchange "
            "proof, no total conservation proof, no C_exchange closeout, no "
            "EM-QFT closure, no QFT-GR closure, no Phase 2 authorization, no "
            "empirical validation, and no master-action promotion. The full "
            "ToeFormal aggregate is recorded as NOT_RUN for this review."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "action_block_packet_file": _ptr(ACTION_BLOCK_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePsiAU1InteractionActionBlockDefinitionResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "lane_level_lean_target_files": [
            _ptr(LEAN_PACKET_PATH),
            _ptr(QFTGR_AGGREGATE_PATH),
            _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            _ptr(RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH),
        ],
        "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        "validation_policy": validation_policy,
        **validation_policy,
    }


def write_toe_native_psi_a_u1_interaction_action_block_definition_result_review(
    *,
    action_block_packet_path: Path = ACTION_BLOCK_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_toe_native_psi_a_u1_interaction_action_block_definition_result_review(
        action_block_packet_path=action_block_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the ToE-native psi-A U(1) interaction action-block result review."
        )
    )
    parser.add_argument("--action-block-packet", type=Path, default=ACTION_BLOCK_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    action_block_packet_path = (
        args.action_block_packet
        if args.action_block_packet.is_absolute()
        else REPO_ROOT / args.action_block_packet
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = write_toe_native_psi_a_u1_interaction_action_block_definition_result_review(
        action_block_packet_path=action_block_packet_path,
        out=out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "toe_native_psi_a_u1_interaction_action_block_definition_result_review: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
