from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_current_and_exchange_route_policy_packet_report import (
    ADJOINT_POLICY,
    BACKGROUND_SCOPE_POLICY,
    BOUNDARY_VARIATION_POLICY,
    COVARIANT_DERIVATIVE_POLICY,
    C_EXCHANGE_EQUATION_PREVIEW,
    C_EXCHANGE_POLICY_PREVIEW,
    CURRENT_CANDIDATE_POLICY,
    DEFAULT_OUT as POLICY_PACKET_PATH,
    FIELD_DOMAIN_POLICY,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAMMA_MATRIX_POLICY,
    GAUGE_EXCHANGE_PREVIEW,
    GAUGE_FIELD_POLICY,
    GAUGE_GROUP_POLICY,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    MATTER_EQUATION_SHAPE_POLICY,
    MATTER_EXCHANGE_PREVIEW,
    MATTER_SURFACE_POLICY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as POLICY_PACKET_OUTCOME,
    PACKET_ID as POLICY_PACKET_ID,
    SCHEMA_ID as POLICY_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCED_GAUGE_EQUATION_PREVIEW,
    SPIN_CONNECTION_POLICY,
    STRESS_ENERGY_POLICY,
    TETRAD_POLICY,
    TOTAL_EXCHANGE_PREVIEW,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_DERIVATION_OBLIGATION_PACKET_"
    "20260624_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_DERIVATION_OBLIGATION_PACKET_v0"
)
OBLIGATION_PACKET_RESULT = (
    "TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_DERIVATION_OBLIGATION_PACKET_"
    "PREPARED_CURRENT_DERIVATION_AND_EXCHANGE_PROOF_OBLIGATIONS_INDEXED_"
    "NO_DERIVATION_OR_EM_QFT_CLOSURE"
)
OUTCOME_ID = OBLIGATION_PACKET_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_current_and_exchange_derivation_obligation_packet_"
    "indexes_current_derivation_and_exchange_proof_obligations_no_derivation_or_"
    "em_qft_closure"
)

NEXT_TARGET = "prepare_toe_native_psi_A_u1_interaction_action_block_definition_packet"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_interaction_action_block_definition_packet_preparation"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_DERIVATION_OBLIGATION_PACKET_"
    "20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1CurrentAndExchangeDerivationObligationPacket.lean"
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

INTERACTION_ACTION_BLOCK_OBLIGATION = (
    "Define the psi-A interaction action or action block."
)
GAUGE_COVARIANCE_OBLIGATION = (
    "Prove the selected D_mu convention is gauge-covariant."
)
PSIBAR_VARIATION_OBLIGATION = (
    "Derive the psi field equation from variation with respect to psibar."
)
A_VARIATION_CURRENT_OBLIGATION = (
    "Derive the current J^mu from variation with respect to A_mu."
)
CURRENT_CONSERVATION_OBLIGATION = (
    "Prove or state the current-conservation obligation: nabla_mu J^mu = 0."
)
SOURCED_MAXWELL_OBLIGATION = (
    "Derive or block the sourced Maxwell route: nabla_mu F^{mu nu} = J^nu."
)
STRESS_ENERGY_DEFINITION_OBLIGATION = (
    "Define T_psi^{mu nu}, T_A^{mu nu}, and T_total^{mu nu}."
)
EXCHANGE_IDENTITY_OBLIGATION = (
    "Prove or block the exchange identities for T_A and T_psi."
)
TOTAL_CONSERVATION_OBLIGATION = (
    "Prove or block total conservation: nabla_mu(T_A^{mu nu} + T_psi^{mu nu}) = 0."
)
C_EXCHANGE_DECISION_OBLIGATION = (
    "Decide whether this creates a new C_exchange rule family."
)

ACTION_BLOCK_PREVIEW = (
    "S_{psi A} candidate block with psibar(i gamma^mu D_mu - m)psi and "
    "-1/4 F_{mu nu}F^{mu nu}; not defined by this packet"
)
CURRENT_CONSERVATION_PREVIEW = "nabla_mu J^mu = 0"
T_PSI_PREVIEW = "T_psi^{mu nu}"
T_A_PREVIEW = "T_A^{mu nu}"
T_TOTAL_PREVIEW = "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}"

BLOCKED_CLAIMS = [
    "current derivation",
    "current conservation proof",
    "sourced Maxwell derivation",
    "Dirac derivation",
    "psi stress-energy derivation",
    "gauge-matter exchange proof",
    "total stress-energy conservation proof",
    "C_exchange closeout",
    "EM-QFT closure",
    "QFT-GR closure",
    "Standard Model derivation",
    "quantized electromagnetism",
    "anomaly analysis",
    "empirical validation",
    "Phase 2 authorization",
    "master-action promotion",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _obligation_rows() -> list[dict[str, Any]]:
    return [
        {
            "obligation_id": "O1",
            "status": "indexed_pending_future_packet",
            "description": INTERACTION_ACTION_BLOCK_OBLIGATION,
            "route_shape": ACTION_BLOCK_PREVIEW,
            "acceptance_requirement": (
                "A future packet must state the exact interaction action block before "
                "variation is accepted."
            ),
            "claim_status": "not_derived",
        },
        {
            "obligation_id": "O2",
            "status": "indexed_pending_future_packet",
            "description": GAUGE_COVARIANCE_OBLIGATION,
            "route_shape": COVARIANT_DERIVATIVE_POLICY,
            "acceptance_requirement": (
                "A future proof must show the selected plus-sign D_mu convention "
                "transforms covariantly under the pinned U(1) gauge rule."
            ),
            "claim_status": "not_proved",
        },
        {
            "obligation_id": "O3",
            "status": "indexed_pending_future_packet",
            "description": PSIBAR_VARIATION_OBLIGATION,
            "route_shape": MATTER_EQUATION_SHAPE_POLICY,
            "acceptance_requirement": (
                "A future variation with respect to psibar must derive the matter "
                "field equation under the chosen boundary policy."
            ),
            "claim_status": "not_derived",
        },
        {
            "obligation_id": "O4",
            "status": "indexed_pending_future_packet",
            "description": A_VARIATION_CURRENT_OBLIGATION,
            "route_shape": CURRENT_CANDIDATE_POLICY,
            "acceptance_requirement": (
                "A future variation with respect to A_mu must produce the current "
                "and fix signs and factors."
            ),
            "claim_status": "not_derived",
        },
        {
            "obligation_id": "O5",
            "status": "indexed_pending_future_packet",
            "description": CURRENT_CONSERVATION_OBLIGATION,
            "route_shape": CURRENT_CONSERVATION_PREVIEW,
            "acceptance_requirement": (
                "A future packet must prove conservation or explicitly state the "
                "remaining obstruction."
            ),
            "claim_status": "not_proved",
        },
        {
            "obligation_id": "O6",
            "status": "indexed_pending_future_packet",
            "description": SOURCED_MAXWELL_OBLIGATION,
            "route_shape": SOURCED_GAUGE_EQUATION_PREVIEW,
            "acceptance_requirement": (
                "A future packet must derive the sourced gauge equation or retain a "
                "blocked route."
            ),
            "claim_status": "not_derived",
        },
        {
            "obligation_id": "O7",
            "status": "indexed_pending_future_packet",
            "description": STRESS_ENERGY_DEFINITION_OBLIGATION,
            "route_shape": [T_PSI_PREVIEW, T_A_PREVIEW, T_TOTAL_PREVIEW],
            "acceptance_requirement": (
                "A future packet must define the matter, gauge, and total stress-"
                "energy objects under the selected convention."
            ),
            "claim_status": "not_defined",
        },
        {
            "obligation_id": "O8",
            "status": "indexed_pending_future_packet",
            "description": EXCHANGE_IDENTITY_OBLIGATION,
            "route_shape": [GAUGE_EXCHANGE_PREVIEW, MATTER_EXCHANGE_PREVIEW],
            "acceptance_requirement": (
                "A future packet must prove or block the opposite-sign exchange "
                "identities for gauge and matter sectors."
            ),
            "claim_status": "not_proved",
        },
        {
            "obligation_id": "O9",
            "status": "indexed_pending_future_packet",
            "description": TOTAL_CONSERVATION_OBLIGATION,
            "route_shape": TOTAL_EXCHANGE_PREVIEW,
            "acceptance_requirement": (
                "A future packet must prove or block total stress-energy "
                "conservation for the interacting system."
            ),
            "claim_status": "not_proved",
        },
        {
            "obligation_id": "O10",
            "status": "indexed_pending_future_packet",
            "description": C_EXCHANGE_DECISION_OBLIGATION,
            "route_shape": [C_EXCHANGE_POLICY_PREVIEW, C_EXCHANGE_EQUATION_PREVIEW],
            "acceptance_requirement": (
                "A future decision must determine whether C_exchange becomes a new "
                "rule family and what closes it."
            ),
            "claim_status": "not_decided",
        },
    ]


def _review_criteria(policy: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_expected_policy_packet_target",
            "status": "accepted",
            "evidence": policy.get("selected_next_target"),
            "assessment": "The policy packet authorized the derivation-obligation packet.",
        },
        {
            "row_id": "selected_route_and_d_mu_convention_preserved",
            "status": "accepted",
            "evidence": [
                SELECTED_INTERACTION_ROUTE,
                COVARIANT_DERIVATIVE_POLICY,
                GAUGE_TRANSFORMATION_POLICY,
            ],
            "assessment": "The obligation index preserves the selected psi-A U(1) policy.",
        },
        {
            "row_id": "ten_derivation_obligations_indexed",
            "status": "accepted",
            "evidence": [row["obligation_id"] for row in _obligation_rows()],
            "assessment": "O1-O10 are recorded as future obligations only.",
        },
        {
            "row_id": "current_derivation_and_exchange_proof_still_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "The packet does not derive current, equations, exchange, or closure.",
        },
        {
            "row_id": "next_target_is_action_block_definition_packet",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "O1 is selected as the next prerequisite before variation.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_psi_A_u1_current_and_exchange_derivation_obligation_packet"
        ),
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


def build_toe_native_psi_a_u1_current_and_exchange_derivation_obligation_packet(
    *,
    policy_packet_path: Path = POLICY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    policy = _read_json(policy_packet_path)
    obligation_rows = _obligation_rows()
    review_criteria = _review_criteria(policy)
    acceptance_criteria = {
        "consumes_expected_policy_packet": (
            policy.get("schema_id") == POLICY_SCHEMA_ID
            and policy.get("packet_id") == POLICY_PACKET_ID
            and policy.get("outcome_id") == POLICY_PACKET_OUTCOME
            and policy.get("selected_next_target") == CONSUMED_TARGET
            and policy.get("accepted") is True
        ),
        "selected_route_preserved": (
            policy.get("selected_interaction_route") == SELECTED_INTERACTION_ROUTE
            and policy.get("covariant_derivative_policy") == COVARIANT_DERIVATIVE_POLICY
            and policy.get("gauge_transformation_policy") == GAUGE_TRANSFORMATION_POLICY
        ),
        "obligations_complete": len(obligation_rows) == 10,
        "blocked_claims_complete": len(BLOCKED_CLAIMS) == 16,
        "all_obligations_pending": all(
            row["status"] == "indexed_pending_future_packet"
            for row in obligation_rows
        ),
        "next_target_is_action_block_definition": NEXT_TARGET
        == "prepare_toe_native_psi_A_u1_interaction_action_block_definition_packet",
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_DERIVATION_OBLIGATION_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_DERIVATION_"
            "OBLIGATION_PACKET"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else (
            "TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_DERIVATION_OBLIGATION_"
            "PACKET_REQUIRES_REMEDIATION"
        ),
        "obligation_packet_result": OBLIGATION_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "policy_schema_id": POLICY_SCHEMA_ID,
        "policy_packet_id": POLICY_PACKET_ID,
        "policy_packet_outcome": POLICY_PACKET_OUTCOME,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "matter_surface_policy": MATTER_SURFACE_POLICY,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "gauge_field_policy": GAUGE_FIELD_POLICY,
        "field_strength_policy": FIELD_STRENGTH_POLICY,
        "covariant_derivative_policy": COVARIANT_DERIVATIVE_POLICY,
        "gauge_transformation_policy": GAUGE_TRANSFORMATION_POLICY,
        "gamma_matrix_policy": GAMMA_MATRIX_POLICY,
        "tetrad_policy": TETRAD_POLICY,
        "spin_connection_policy": SPIN_CONNECTION_POLICY,
        "adjoint_policy": ADJOINT_POLICY,
        "field_domain_policy": FIELD_DOMAIN_POLICY,
        "boundary_variation_policy": BOUNDARY_VARIATION_POLICY,
        "background_scope_policy": BACKGROUND_SCOPE_POLICY,
        "current_candidate_policy": CURRENT_CANDIDATE_POLICY,
        "stress_energy_policy": STRESS_ENERGY_POLICY,
        "action_block_preview": ACTION_BLOCK_PREVIEW,
        "matter_equation_shape_preview": MATTER_EQUATION_SHAPE_POLICY,
        "current_conservation_preview": CURRENT_CONSERVATION_PREVIEW,
        "sourced_gauge_equation_preview": SOURCED_GAUGE_EQUATION_PREVIEW,
        "gauge_exchange_preview": GAUGE_EXCHANGE_PREVIEW,
        "matter_exchange_preview": MATTER_EXCHANGE_PREVIEW,
        "total_exchange_preview": TOTAL_EXCHANGE_PREVIEW,
        "t_psi_preview": T_PSI_PREVIEW,
        "t_a_preview": T_A_PREVIEW,
        "t_total_preview": T_TOTAL_PREVIEW,
        "c_exchange_policy_preview": C_EXCHANGE_POLICY_PREVIEW,
        "c_exchange_equation_preview": C_EXCHANGE_EQUATION_PREVIEW,
        "derivation_obligations": obligation_rows,
        "derivation_obligation_count": len(obligation_rows),
        "obligation_ids": [row["obligation_id"] for row in obligation_rows],
        "obligation_packet_prepared": prepared,
        "current_derivation_obligations_indexed": prepared,
        "exchange_proof_obligations_indexed": prepared,
        "c_exchange_decision_obligation_indexed": prepared,
        "action_block_definition_obligation_indexed": prepared,
        "gauge_covariance_obligation_indexed": prepared,
        "psi_variation_obligation_indexed": prepared,
        "A_variation_current_obligation_indexed": prepared,
        "current_conservation_obligation_indexed": prepared,
        "sourced_maxwell_obligation_indexed": prepared,
        "stress_energy_definition_obligation_indexed": prepared,
        "exchange_identity_obligation_indexed": prepared,
        "total_conservation_obligation_indexed": prepared,
        "action_block_definition_packet_preparation_authorized": prepared,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": prepared,
        "obligation_packet_only": True,
        "derivation_packet": False,
        "interaction_action_block_defined": False,
        "gauge_covariance_proved": False,
        "psi_field_equation_derived": False,
        "A_variation_current_derived": False,
        "current_derived": False,
        "current_route_derived": False,
        "matter_current_J_nu_derived": False,
        "J_nu_derived": False,
        "current_conservation_proved": False,
        "sourced_maxwell_equation_derived": False,
        "sourced_maxwell_route_derived": False,
        "dirac_equation_derived": False,
        "psi_stress_energy_derived": False,
        "T_psi_derived": False,
        "gauge_matter_exchange_proved": False,
        "matter_gauge_exchange_proved": False,
        "total_stress_energy_conservation_proved": False,
        "T_total_conservation_proved": False,
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
            "treat obligation indexing as current derivation",
            "claim current conservation",
            "derive sourced Maxwell",
            "derive the Dirac equation",
            "derive psi stress-energy",
            "prove matter-gauge exchange",
            "prove total stress-energy conservation",
            "close C_exchange",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "authorize Phase 2",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "mathematical_statement": (
            "This obligation packet records O1-O10 for the psi-A U(1) current "
            "and exchange route. It preserves D_mu psi = (nabla_mu + i q A_mu) "
            "psi, indexes future variation, current, sourced Maxwell, stress-"
            "energy, exchange, total conservation, and C_exchange decision "
            "obligations, and performs no derivation."
        ),
        "non_claim_boundary": (
            "This obligation packet indexes proof obligations only. It does not "
            "derive J^nu, does not prove current conservation, does not derive "
            "sourced Maxwell, does not derive the Dirac equation, does not derive "
            "psi stress-energy, does not prove gauge-matter exchange, does not "
            "prove total stress-energy conservation, does not close C_exchange, "
            "does not close EM-QFT, does not close QFT-GR, does not derive the "
            "Standard Model, does not quantize electromagnetism, does not perform "
            "anomaly analysis, does not claim empirical validation, does not "
            "authorize Phase 2, records no Phase 2 authorization, and does not "
            "promote the master action. The full ToeFormal aggregate is recorded "
            "as NOT_RUN for this packet."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "policy_packet_file": _ptr(POLICY_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePsiAU1CurrentAndExchangeDerivationObligationPacket",
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


def write_toe_native_psi_a_u1_current_and_exchange_derivation_obligation_packet(
    *,
    policy_packet_path: Path = POLICY_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = (
        build_toe_native_psi_a_u1_current_and_exchange_derivation_obligation_packet(
            policy_packet_path=policy_packet_path,
            captured_at_utc=captured_at_utc,
        )
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the ToE-native psi-A U(1) current and exchange derivation "
            "obligation packet."
        )
    )
    parser.add_argument("--policy-packet", type=Path, default=POLICY_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    policy_packet_path = (
        args.policy_packet
        if args.policy_packet.is_absolute()
        else REPO_ROOT / args.policy_packet
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        write_toe_native_psi_a_u1_current_and_exchange_derivation_obligation_packet(
            policy_packet_path=policy_packet_path,
            out=out,
            captured_at_utc=args.captured_at_utc,
        )
    )
    print(
        "toe_native_psi_a_u1_current_and_exchange_derivation_obligation_packet_report: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
