from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_stress_energy_route_under_selected_u1_policy_packet_report import (
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY as PRIOR_GAUGE_STRESS_ENERGY_ROUTE,
)
from formal.python.tools.toe_native_psi_a_u1_sourced_maxwell_route_packet_report import (
    ACTION_BLOCK_STATEMENT,
    A_VARIATION_RESIDUAL,
    CONSERVED_SOURCE_CONDITION,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE,
    CURRENT_CANDIDATE_FROM_A_VARIATION,
    CURRENT_CONSERVATION_RESULT,
    DEFAULT_OUT as SOURCED_MAXWELL_PACKET_PATH,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    OUTCOME_ID as SOURCED_MAXWELL_OUTCOME,
    PACKET_ID as SOURCED_MAXWELL_PACKET_ID,
    PACKET_RESULT as SOURCED_MAXWELL_PACKET_RESULT,
    SCHEMA_ID as SOURCED_MAXWELL_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    SOURCED_MAXWELL_RESIDUAL_ZERO,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_AND_EXCHANGE_OBLIGATION_PACKET_"
    "20260624_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_AND_EXCHANGE_OBLIGATION_PACKET_v0"
)
OUTCOME_ID = (
    "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_AND_EXCHANGE_OBLIGATION_PACKET_"
    "PREPARED_STRESS_ENERGY_AND_EXCHANGE_REQUIREMENTS_INDEXED_"
    "NO_EXCHANGE_PROOF_OR_EM_QFT_CLOSURE"
)
PACKET_RESULT = OUTCOME_ID
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_stress_energy_and_exchange_obligation_packet_prepared_"
    "stress_energy_and_exchange_requirements_indexed_no_exchange_proof_or_"
    "em_qft_closure"
)

CONSUMED_TARGET = "prepare_toe_native_psi_A_u1_stress_energy_and_exchange_obligation_packet"
NEXT_TARGET = "prepare_toe_native_psi_A_u1_stress_energy_definition_policy_packet"
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_stress_energy_definition_policy_packet_preparation"
)

GAUGE_STRESS_ENERGY_OBJECT = "T_A^{mu nu}"
MATTER_STRESS_ENERGY_OBJECT = "T_psi^{mu nu}"
TOTAL_STRESS_ENERGY_OBJECT = "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}"
GAUGE_SECTOR_EXCHANGE_TARGET = (
    "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha"
)
MATTER_SECTOR_EXCHANGE_TARGET = (
    "nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha"
)
TOTAL_CONSERVATION_TARGET = "nabla_mu T_total^{mu nu} = 0"
TOTAL_CONSERVATION_EXPANDED_TARGET = (
    "nabla_mu(T_A^{mu nu} + T_psi^{mu nu}) = 0"
)
C_EXCHANGE_CANDIDATE = (
    "C_exchange^{Apsi,nu} := nabla_mu(T_A^{mu nu} + T_psi^{mu nu})"
)
C_EXCHANGE_EQUATION = "C_exchange^{Apsi,nu} = 0"
EXCHANGE_PLAIN_MEANING = (
    "Matter and the gauge field may trade energy and momentum, but the total "
    "must balance."
)

BLOCKED_CLAIMS = [
    "stress-energy derivation",
    "gauge-sector exchange proof",
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
    / "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_AND_EXCHANGE_OBLIGATION_PACKET_"
    "20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1StressEnergyAndExchangeObligationPacket.lean"
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


def _obligation_rows() -> list[dict[str, Any]]:
    return [
        {
            "obligation_id": "O1",
            "status": "indexed_pending_future_packet",
            "description": "Recall or index the gauge stress-energy object T_A^{mu nu}.",
            "route_shape": GAUGE_STRESS_ENERGY_OBJECT,
            "prior_route_context": PRIOR_GAUGE_STRESS_ENERGY_ROUTE,
            "claim_status": "indexed_not_derived_here",
        },
        {
            "obligation_id": "O2",
            "status": "indexed_pending_future_packet",
            "description": "Define or index the required matter stress-energy object T_psi^{mu nu}.",
            "route_shape": MATTER_STRESS_ENERGY_OBJECT,
            "claim_status": "not_defined_or_derived_here",
        },
        {
            "obligation_id": "O3",
            "status": "indexed_pending_future_packet",
            "description": "Define total stress-energy.",
            "route_shape": TOTAL_STRESS_ENERGY_OBJECT,
            "claim_status": "definition_target_only",
        },
        {
            "obligation_id": "O4",
            "status": "indexed_pending_future_packet",
            "description": "Index the gauge-sector exchange target.",
            "route_shape": GAUGE_SECTOR_EXCHANGE_TARGET,
            "claim_status": "not_proved",
        },
        {
            "obligation_id": "O5",
            "status": "indexed_pending_future_packet",
            "description": "Index the matter-sector exchange target.",
            "route_shape": MATTER_SECTOR_EXCHANGE_TARGET,
            "claim_status": "not_proved",
        },
        {
            "obligation_id": "O6",
            "status": "indexed_pending_future_packet",
            "description": "Index total conservation target.",
            "route_shape": [
                TOTAL_CONSERVATION_TARGET,
                TOTAL_CONSERVATION_EXPANDED_TARGET,
            ],
            "claim_status": "not_proved",
        },
        {
            "obligation_id": "O7",
            "status": "indexed_pending_future_packet",
            "description": "Decide whether this creates a candidate C_exchange family.",
            "route_shape": [C_EXCHANGE_CANDIDATE, C_EXCHANGE_EQUATION],
            "claim_status": "candidate_indexed_not_closed",
        },
    ]


def _review_criteria(sourced_maxwell_packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "sourced_maxwell_packet_consumed",
            "status": "accepted",
            "evidence": sourced_maxwell_packet.get("outcome_id"),
            "assessment": "The bounded sourced-Maxwell route packet is consumed.",
        },
        {
            "row_id": "current_and_sourced_route_preserved",
            "status": "accepted",
            "evidence": [SOURCE_CURRENT, CURRENT_CONSERVATION_RESULT, SOURCED_GAUGE_ROUTE],
            "assessment": "The matter-made conserved source route is preserved as input.",
        },
        {
            "row_id": "stress_energy_exchange_obligations_indexed",
            "status": "accepted",
            "evidence": [row["obligation_id"] for row in _obligation_rows()],
            "assessment": "O1-O7 are indexed as stress-energy and exchange obligations only.",
        },
        {
            "row_id": "candidate_c_exchange_indexed_without_closeout",
            "status": "accepted",
            "evidence": [C_EXCHANGE_CANDIDATE, C_EXCHANGE_EQUATION],
            "assessment": "The candidate C_exchange family is indexed but not closed.",
        },
        {
            "row_id": "next_target_is_stress_energy_definition_policy",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target defines the stress-energy policy before exchange proof.",
        },
        {
            "row_id": "exchange_and_closure_claims_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Stress-energy derivation, exchange proof, closure, validation, and promotion remain blocked.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_psi_A_u1_stress_energy_and_exchange_obligation_packet"
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


def build_toe_native_psi_a_u1_stress_energy_and_exchange_obligation_packet(
    *,
    sourced_maxwell_packet_path: Path = SOURCED_MAXWELL_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    sourced_maxwell_packet = _read_json(sourced_maxwell_packet_path)
    obligation_rows = _obligation_rows()
    review_criteria = _review_criteria(sourced_maxwell_packet)
    acceptance_criteria = {
        "consumes_expected_sourced_maxwell_packet": (
            sourced_maxwell_packet.get("schema_id") == SOURCED_MAXWELL_SCHEMA_ID
            and sourced_maxwell_packet.get("packet_id") == SOURCED_MAXWELL_PACKET_ID
            and sourced_maxwell_packet.get("outcome_id") == SOURCED_MAXWELL_OUTCOME
            and sourced_maxwell_packet.get("packet_result") == SOURCED_MAXWELL_PACKET_RESULT
            and sourced_maxwell_packet.get("selected_next_target") == CONSUMED_TARGET
            and sourced_maxwell_packet.get("accepted") is True
        ),
        "sourced_inputs_preserved": (
            sourced_maxwell_packet.get("source_current") == SOURCE_CURRENT
            and sourced_maxwell_packet.get("current_conservation_result")
            == CURRENT_CONSERVATION_RESULT
            and sourced_maxwell_packet.get("sourced_gauge_route") == SOURCED_GAUGE_ROUTE
            and sourced_maxwell_packet.get("sourced_maxwell_route_derived") is True
        ),
        "stress_energy_obligations_complete": len(obligation_rows) == 7,
        "blocked_claims_complete": len(BLOCKED_CLAIMS) == 14,
        "all_obligations_pending": all(
            row["status"] == "indexed_pending_future_packet"
            for row in obligation_rows
        ),
        "next_target_is_definition_policy": NEXT_TARGET
        == "prepare_toe_native_psi_A_u1_stress_energy_definition_policy_packet",
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_AND_EXCHANGE_OBLIGATION_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_AND_EXCHANGE_"
            "OBLIGATION_PACKET"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_AND_EXCHANGE_OBLIGATION_"
            "PACKET_REQUIRES_REMEDIATION"
        ),
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_sourced_maxwell_route_packet_result": SOURCED_MAXWELL_OUTCOME,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "action_block_statement": ACTION_BLOCK_STATEMENT,
        "covariant_derivative_policy": COVARIANT_DERIVATIVE_POLICY,
        "field_strength_policy": FIELD_STRENGTH_POLICY,
        "gauge_transformation_policy": GAUGE_TRANSFORMATION_POLICY,
        "A_variation_residual": A_VARIATION_RESIDUAL,
        "sourced_maxwell_residual_zero": SOURCED_MAXWELL_RESIDUAL_ZERO,
        "sourced_gauge_route": SOURCED_GAUGE_ROUTE,
        "sourced_maxwell_route": SOURCED_GAUGE_ROUTE,
        "source_current": SOURCE_CURRENT,
        "current_candidate": CURRENT_CANDIDATE,
        "current_candidate_from_A_variation": CURRENT_CANDIDATE_FROM_A_VARIATION,
        "conserved_source_condition": CONSERVED_SOURCE_CONDITION,
        "current_conservation_result": CURRENT_CONSERVATION_RESULT,
        "prior_gauge_stress_energy_route": PRIOR_GAUGE_STRESS_ENERGY_ROUTE,
        "gauge_stress_energy_object": GAUGE_STRESS_ENERGY_OBJECT,
        "matter_stress_energy_object": MATTER_STRESS_ENERGY_OBJECT,
        "total_stress_energy_object": TOTAL_STRESS_ENERGY_OBJECT,
        "gauge_sector_exchange_target": GAUGE_SECTOR_EXCHANGE_TARGET,
        "matter_sector_exchange_target": MATTER_SECTOR_EXCHANGE_TARGET,
        "total_conservation_target": TOTAL_CONSERVATION_TARGET,
        "total_conservation_expanded_target": TOTAL_CONSERVATION_EXPANDED_TARGET,
        "C_exchange_candidate": C_EXCHANGE_CANDIDATE,
        "C_exchange_equation": C_EXCHANGE_EQUATION,
        "stress_energy_exchange_obligations": obligation_rows,
        "stress_energy_exchange_obligation_count": len(obligation_rows),
        "obligation_ids": [row["obligation_id"] for row in obligation_rows],
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "stress_energy_and_exchange_obligation_packet_prepared": accepted,
        "stress_energy_and_exchange_requirements_indexed": accepted,
        "gauge_stress_energy_object_indexed": accepted,
        "matter_stress_energy_object_required": accepted,
        "total_stress_energy_target_indexed": accepted,
        "gauge_sector_exchange_target_indexed": accepted,
        "matter_sector_exchange_target_indexed": accepted,
        "total_conservation_target_indexed": accepted,
        "C_exchange_candidate_family_indexed": accepted,
        "stress_energy_definition_policy_packet_selected": accepted,
        "stress_energy_definition_policy_packet_preparation_authorized": accepted,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "stress_energy_derived": False,
        "psi_stress_energy_derived": False,
        "matter_stress_energy_derived": False,
        "gauge_stress_energy_derived_here": False,
        "gauge_sector_exchange_proved": False,
        "matter_sector_exchange_proved": False,
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
            "treat stress-energy obligation indexing as stress-energy derivation",
            "prove gauge-sector exchange in this packet",
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
            "This obligation packet consumes the bounded psi-A U(1) sourced "
            "gauge route nabla_mu F^{mu nu} = J^nu with J^nu = q psibar "
            "gamma^nu psi and nabla_mu J^mu = 0, then indexes the stress-"
            "energy and exchange obligations for T_A^{mu nu}, T_psi^{mu nu}, "
            "T_total^{mu nu}, opposite-sector exchange targets, total "
            "conservation, and candidate C_exchange."
        ),
        "plain_meaning": EXCHANGE_PLAIN_MEANING,
        "non_claim_boundary": (
            "This is a stress-energy and exchange obligation packet only. It "
            "indexes T_A^{mu nu}, the required T_psi^{mu nu}, T_total^{mu nu} "
            "= T_A^{mu nu} + T_psi^{mu nu}, the exchange targets nabla_mu "
            "T_A^{mu nu} = - F^nu{}_alpha J^alpha and nabla_mu T_psi^{mu nu} "
            "= + F^nu{}_alpha J^alpha, the total target "
            "nabla_mu(T_A^{mu nu} + T_psi^{mu nu}) = 0, and the candidate "
            "C_exchange^{Apsi,nu}. It records no stress-energy derivation, no "
            "gauge-sector exchange proof, no matter-sector exchange proof, no "
            "total conservation proof, no C_exchange closeout, no full Maxwell "
            "closure, no EM-QFT closure, no QFT-GR closure, no quantized "
            "electromagnetism, no anomaly analysis, no Standard Model "
            "derivation, no Phase 2 authorization, no empirical validation, "
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
            "sourced_maxwell_route_json": _ptr(sourced_maxwell_packet_path),
            "sourced_maxwell_route_outcome": SOURCED_MAXWELL_OUTCOME,
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
            "Prepare the ToE-native psi-A U(1) stress-energy and exchange "
            "obligation packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--sourced-maxwell-packet",
        type=Path,
        default=SOURCED_MAXWELL_PACKET_PATH,
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    payload = build_toe_native_psi_a_u1_stress_energy_and_exchange_obligation_packet(
        sourced_maxwell_packet_path=args.sourced_maxwell_packet,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(args.out, payload)
    print(args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
