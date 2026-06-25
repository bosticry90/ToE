from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_current_and_exchange_derivation_obligation_packet_report import (
    BACKGROUND_SCOPE_POLICY,
    BOUNDARY_VARIATION_POLICY,
    COVARIANT_DERIVATIVE_POLICY,
    C_EXCHANGE_EQUATION_PREVIEW,
    C_EXCHANGE_POLICY_PREVIEW,
    CURRENT_CANDIDATE_POLICY,
    DEFAULT_OUT as OBLIGATION_PACKET_PATH,
    FIELD_DOMAIN_POLICY,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_EXCHANGE_PREVIEW,
    GAUGE_FIELD_POLICY,
    GAUGE_GROUP_POLICY,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    MATTER_EXCHANGE_PREVIEW,
    MATTER_SURFACE_POLICY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as OBLIGATION_PACKET_OUTCOME,
    PACKET_ID as OBLIGATION_PACKET_ID,
    SCHEMA_ID as OBLIGATION_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCED_GAUGE_EQUATION_PREVIEW,
    STRESS_ENERGY_POLICY,
    TOTAL_EXCHANGE_PREVIEW,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_PACKET_20260624_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_PACKET_v0"
ACTION_BLOCK_DEFINITION_PACKET_RESULT = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_PACKET_PREPARED_"
    "ACTION_BLOCK_DEFINED_CURRENT_AND_EXCHANGE_DERIVATION_STILL_BLOCKED"
)
OUTCOME_ID = ACTION_BLOCK_DEFINITION_PACKET_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_interaction_action_block_definition_packet_defines_"
    "minimal_u1_dirac_gauge_action_block_current_and_exchange_derivation_still_blocked"
)

NEXT_TARGET = "review_toe_native_psi_A_u1_interaction_action_block_definition_packet_result"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_interaction_action_block_definition_packet_result_review"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_PACKET_20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1InteractionActionBlockDefinitionPacket.lean"
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

ACTION_BLOCK_ID = "S_{psi A}"
ACTION_BLOCK_STATEMENT = (
    "S_{psi A} = int d^4x sqrt(-g) [ psibar (i gamma^mu D_mu - m) psi "
    "- 1/4 F_{mu nu}F^{mu nu} ]"
)
ACTION_BLOCK_DENSITY = (
    "sqrt(-g) [ psibar (i gamma^mu D_mu - m) psi "
    "- 1/4 F_{mu nu}F^{mu nu} ]"
)
ACTION_BLOCK_MATTER_TERM = "psibar (i gamma^mu D_mu - m) psi"
ACTION_BLOCK_GAUGE_TERM = "- 1/4 F_{mu nu}F^{mu nu}"
GAUGE_COVARIANT_DERIVATIVE_TRANSFORM = "D_mu psi -> exp(-i q chi) D_mu psi"
MINIMAL_COUPLING_EXPANSION = (
    "i gamma^mu D_mu psi = i gamma^mu nabla_mu psi - q gamma^mu A_mu psi"
)
INTERACTION_TERM_SHAPE = "- q psibar gamma^mu A_mu psi"
CURRENT_CANDIDATE_PREVIEW = "J^mu = q psibar gamma^mu psi"

BLOCKED_CLAIMS = [
    "A-variation result",
    "psi variation result",
    "J^nu derivation",
    "current conservation proof",
    "sourced Maxwell derivation",
    "Dirac derivation",
    "psi stress-energy derivation",
    "A/psi exchange identity",
    "total stress-energy conservation proof",
    "C_exchange definition closeout",
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


def _review_criteria(obligation: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_expected_obligation_packet_target",
            "status": "accepted",
            "evidence": obligation.get("selected_next_target"),
            "assessment": "The obligation packet authorized the action-block definition packet.",
        },
        {
            "row_id": "selected_route_and_plus_sign_convention_preserved",
            "status": "accepted",
            "evidence": [
                SELECTED_INTERACTION_ROUTE,
                COVARIANT_DERIVATIVE_POLICY,
                GAUGE_TRANSFORMATION_POLICY,
                GAUGE_COVARIANT_DERIVATIVE_TRANSFORM,
            ],
            "assessment": "The packet preserves the selected psi-A U(1) plus-sign convention.",
        },
        {
            "row_id": "bounded_action_block_defined",
            "status": "accepted",
            "evidence": ACTION_BLOCK_STATEMENT,
            "assessment": "The packet defines only the minimal U(1) Dirac-gauge action block.",
        },
        {
            "row_id": "minimal_coupling_expansion_recorded_without_current_derivation",
            "status": "accepted",
            "evidence": [MINIMAL_COUPLING_EXPANSION, INTERACTION_TERM_SHAPE],
            "assessment": "The packet records the interaction-term shape as future variation input.",
        },
        {
            "row_id": "current_exchange_and_closure_derivations_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "All variation, current, exchange, closure, empirical, Phase 2, and promotion claims remain blocked.",
        },
        {
            "row_id": "next_target_is_action_block_result_review",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is a review of this definition packet result.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_interaction_action_block_definition_packet",
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


def build_toe_native_psi_a_u1_interaction_action_block_definition_packet(
    *,
    obligation_packet_path: Path = OBLIGATION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    obligation = _read_json(obligation_packet_path)
    review_criteria = _review_criteria(obligation)
    acceptance_criteria = {
        "consumes_expected_obligation_packet": (
            obligation.get("schema_id") == OBLIGATION_SCHEMA_ID
            and obligation.get("packet_id") == OBLIGATION_PACKET_ID
            and obligation.get("outcome_id") == OBLIGATION_PACKET_OUTCOME
            and obligation.get("selected_next_target") == CONSUMED_TARGET
            and obligation.get("accepted") is True
        ),
        "selected_route_preserved": (
            obligation.get("selected_interaction_route") == SELECTED_INTERACTION_ROUTE
            and obligation.get("covariant_derivative_policy") == COVARIANT_DERIVATIVE_POLICY
            and obligation.get("gauge_transformation_policy") == GAUGE_TRANSFORMATION_POLICY
        ),
        "action_block_statement_complete": (
            ACTION_BLOCK_ID in ACTION_BLOCK_STATEMENT
            and ACTION_BLOCK_MATTER_TERM in ACTION_BLOCK_STATEMENT
            and ACTION_BLOCK_GAUGE_TERM in ACTION_BLOCK_STATEMENT
            and "sqrt(-g)" in ACTION_BLOCK_STATEMENT
        ),
        "gauge_transform_convention_complete": (
            "exp(-i q chi)" in GAUGE_TRANSFORMATION_POLICY
            and "A_mu -> A_mu + partial_mu chi" in GAUGE_TRANSFORMATION_POLICY
            and "exp(-i q chi)" in GAUGE_COVARIANT_DERIVATIVE_TRANSFORM
        ),
        "minimal_coupling_expansion_recorded": (
            MINIMAL_COUPLING_EXPANSION.endswith("- q gamma^mu A_mu psi")
            and INTERACTION_TERM_SHAPE.startswith("- q")
        ),
        "blocked_claims_complete": len(BLOCKED_CLAIMS) == 15,
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "next_target_is_result_review": NEXT_TARGET
        == "review_toe_native_psi_A_u1_interaction_action_block_definition_packet_result",
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else (
            "TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_PACKET_REQUIRES_"
            "REMEDIATION"
        ),
        "action_block_definition_packet_result": ACTION_BLOCK_DEFINITION_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "obligation_schema_id": OBLIGATION_SCHEMA_ID,
        "obligation_packet_id": OBLIGATION_PACKET_ID,
        "obligation_packet_outcome": OBLIGATION_PACKET_OUTCOME,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "matter_surface_policy": MATTER_SURFACE_POLICY,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "gauge_field_policy": GAUGE_FIELD_POLICY,
        "field_strength_policy": FIELD_STRENGTH_POLICY,
        "covariant_derivative_policy": COVARIANT_DERIVATIVE_POLICY,
        "gauge_transformation_policy": GAUGE_TRANSFORMATION_POLICY,
        "gauge_covariant_derivative_transform": GAUGE_COVARIANT_DERIVATIVE_TRANSFORM,
        "background_scope_policy": BACKGROUND_SCOPE_POLICY,
        "field_domain_policy": FIELD_DOMAIN_POLICY,
        "boundary_variation_policy": BOUNDARY_VARIATION_POLICY,
        "current_candidate_policy": CURRENT_CANDIDATE_POLICY,
        "stress_energy_policy": STRESS_ENERGY_POLICY,
        "action_block_id": ACTION_BLOCK_ID,
        "action_block_statement": ACTION_BLOCK_STATEMENT,
        "action_block_density": ACTION_BLOCK_DENSITY,
        "action_block_matter_term": ACTION_BLOCK_MATTER_TERM,
        "action_block_gauge_term": ACTION_BLOCK_GAUGE_TERM,
        "minimal_coupling_expansion": MINIMAL_COUPLING_EXPANSION,
        "interaction_term_shape": INTERACTION_TERM_SHAPE,
        "current_candidate_preview": CURRENT_CANDIDATE_PREVIEW,
        "sourced_gauge_equation_preview": SOURCED_GAUGE_EQUATION_PREVIEW,
        "gauge_exchange_preview": GAUGE_EXCHANGE_PREVIEW,
        "matter_exchange_preview": MATTER_EXCHANGE_PREVIEW,
        "total_exchange_preview": TOTAL_EXCHANGE_PREVIEW,
        "c_exchange_policy_preview": C_EXCHANGE_POLICY_PREVIEW,
        "c_exchange_equation_preview": C_EXCHANGE_EQUATION_PREVIEW,
        "action_block_definition_packet_prepared": prepared,
        "interaction_action_block_defined": prepared,
        "minimal_u1_dirac_gauge_action_block_recorded": prepared,
        "plus_sign_covariant_derivative_preserved": prepared,
        "field_strength_definition_preserved": prepared,
        "gauge_transformation_policy_preserved": prepared,
        "gauge_covariant_derivative_transform_recorded": prepared,
        "minimal_coupling_expansion_recorded": prepared,
        "interaction_term_shape_recorded": prepared,
        "current_candidate_preview_retained": prepared,
        "action_variation_future_packet_enabled": prepared,
        "result_review_preparation_authorized": prepared,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": prepared,
        "action_block_definition_packet_only": True,
        "derivation_packet": False,
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
        "gauge_matter_exchange_proved": False,
        "matter_gauge_exchange_proved": False,
        "total_stress_energy_conservation_proved": False,
        "T_total_conservation_proved": False,
        "C_exchange_definition_closeout": False,
        "C_exchange_closeout": False,
        "c_exchange_rule_family_decided": False,
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
            "treat action-block definition as A-variation result",
            "treat action-block definition as psi variation result",
            "claim J^nu derivation",
            "claim current conservation",
            "derive sourced Maxwell",
            "derive the Dirac equation",
            "derive psi stress-energy",
            "prove A/psi exchange",
            "prove total stress-energy conservation",
            "close C_exchange",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "mathematical_statement": (
            "This packet defines the bounded psi-A U(1) action block "
            "S_{psi A} = int d^4x sqrt(-g) [ psibar (i gamma^mu D_mu - m) psi "
            "- 1/4 F_{mu nu}F^{mu nu} ], preserves D_mu psi = (nabla_mu + i q "
            "A_mu) psi and F_{mu nu} = partial_mu A_nu - partial_nu A_mu, and "
            "records that the plus-sign gauge convention sends psi -> exp(-i q chi) "
            "psi, A_mu -> A_mu + partial_mu chi, and D_mu psi -> exp(-i q chi) "
            "D_mu psi. It records the interaction-term shape only and performs no "
            "variation."
        ),
        "non_claim_boundary": (
            "This is an action-block definition packet only; no A-variation result; "
            "no psi variation result; no J^nu derivation; no current conservation "
            "proof; no sourced Maxwell derivation; no Dirac derivation; no psi "
            "stress-energy derivation; no A/psi exchange identity; no total "
            "stress-energy conservation proof; no C_exchange definition closeout; "
            "no EM-QFT closure; no QFT-GR closure; no Phase 2 authorization; no "
            "empirical validation; no master-action promotion; full ToeFormal "
            "aggregate is recorded as NOT_RUN."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "obligation_packet_file": _ptr(OBLIGATION_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePsiAU1InteractionActionBlockDefinitionPacket",
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


def write_toe_native_psi_a_u1_interaction_action_block_definition_packet(
    *,
    obligation_packet_path: Path = OBLIGATION_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_toe_native_psi_a_u1_interaction_action_block_definition_packet(
        obligation_packet_path=obligation_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the ToE-native psi-A U(1) interaction action-block packet."
    )
    parser.add_argument("--obligation-packet", type=Path, default=OBLIGATION_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    obligation_packet_path = (
        args.obligation_packet
        if args.obligation_packet.is_absolute()
        else REPO_ROOT / args.obligation_packet
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = write_toe_native_psi_a_u1_interaction_action_block_definition_packet(
        obligation_packet_path=obligation_packet_path,
        out=out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "toe_native_psi_a_u1_interaction_action_block_definition_packet_report: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
