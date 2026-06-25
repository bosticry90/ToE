from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_stress_energy_and_exchange_obligation_packet_report import (
    ACTION_BLOCK_STATEMENT,
    COVARIANT_DERIVATIVE_POLICY,
    C_EXCHANGE_CANDIDATE,
    C_EXCHANGE_EQUATION,
    CURRENT_CONSERVATION_RESULT,
    DEFAULT_OUT as STRESS_ENERGY_OBLIGATION_PACKET_PATH,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_TARGET,
    GAUGE_STRESS_ENERGY_OBJECT,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    MATTER_SECTOR_EXCHANGE_TARGET,
    MATTER_STRESS_ENERGY_OBJECT,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as STRESS_ENERGY_OBLIGATION_OUTCOME,
    PACKET_ID as STRESS_ENERGY_OBLIGATION_PACKET_ID,
    PACKET_RESULT as STRESS_ENERGY_OBLIGATION_PACKET_RESULT,
    PRIOR_GAUGE_STRESS_ENERGY_ROUTE,
    SCHEMA_ID as STRESS_ENERGY_OBLIGATION_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_CONSERVATION_EXPANDED_TARGET,
    TOTAL_CONSERVATION_TARGET,
    TOTAL_STRESS_ENERGY_OBJECT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_PACKET_20260624_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_PACKET_v0"
OUTCOME_ID = (
    "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_PACKET_PREPARED_"
    "STRESS_ENERGY_POLICY_INDEXED_NO_EXCHANGE_PROOF_OR_EM_QFT_CLOSURE"
)
PACKET_RESULT = OUTCOME_ID
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_stress_energy_definition_policy_packet_prepared_"
    "stress_energy_policy_indexed_no_exchange_proof_or_em_qft_closure"
)

NEXT_TARGET = "review_toe_native_psi_A_u1_stress_energy_definition_policy_packet_result"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_stress_energy_definition_policy_packet_result_review"

GAUGE_STRESS_ENERGY_POLICY = (
    "T_A^{mu nu} = - F^{mu}{}_{alpha} F^{nu alpha} + "
    "1/4 g^{mu nu} F_{alpha beta}F^{alpha beta}"
)
GAUGE_STRESS_ENERGY_LOWER_INDEX_POLICY = PRIOR_GAUGE_STRESS_ENERGY_ROUTE
MATTER_STRESS_ENERGY_POLICY = (
    "T_psi^{mu nu} = (i/4) [ psibar gamma^mu D^nu psi + "
    "psibar gamma^nu D^mu psi - (D^nu psibar) gamma^mu psi - "
    "(D^mu psibar) gamma^nu psi ]"
)
MATTER_STRESS_ENERGY_POLICY_STATUS = (
    "bounded symmetric Dirac stress-energy definition policy selected as a "
    "candidate route, not derived by metric or tetrad variation here"
)
TOTAL_STRESS_ENERGY_POLICY = TOTAL_STRESS_ENERGY_OBJECT
EXCHANGE_ROUTE_PREVIEW = (
    f"{GAUGE_SECTOR_EXCHANGE_TARGET}; {MATTER_SECTOR_EXCHANGE_TARGET}; "
    f"{TOTAL_CONSERVATION_EXPANDED_TARGET}"
)
PLAIN_MEANING = (
    "The packet names the gauge, matter, and total stress-energy objects that "
    "a future exchange proof must test."
)

BLOCKED_CLAIMS = [
    "stress-energy derivation from metric/tetrad variation",
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
    / "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_PACKET_20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1StressEnergyDefinitionPolicyPacket.lean"
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


def _definition_policy_rows() -> list[dict[str, Any]]:
    return [
        {
            "policy_id": "P1",
            "status": "selected_policy_not_derived",
            "object": GAUGE_STRESS_ENERGY_OBJECT,
            "definition": GAUGE_STRESS_ENERGY_POLICY,
            "equivalent_lower_index_definition": GAUGE_STRESS_ENERGY_LOWER_INDEX_POLICY,
            "claim_status": "reused_from_A_convention_not_rederived_here",
        },
        {
            "policy_id": "P2",
            "status": "selected_policy_not_derived",
            "object": MATTER_STRESS_ENERGY_OBJECT,
            "definition": MATTER_STRESS_ENERGY_POLICY,
            "claim_status": "candidate_definition_policy_not_metric_or_tetrad_derivation",
        },
        {
            "policy_id": "P3",
            "status": "selected_policy_not_derived",
            "object": "T_total^{mu nu}",
            "definition": TOTAL_STRESS_ENERGY_POLICY,
            "claim_status": "definition_policy_not_total_conservation_proof",
        },
    ]


def _review_criteria(obligation_packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "stress_energy_exchange_obligation_packet_consumed",
            "status": "accepted",
            "evidence": obligation_packet.get("outcome_id"),
            "assessment": "The stress-energy and exchange obligation packet is consumed.",
        },
        {
            "row_id": "gauge_stress_energy_policy_selected",
            "status": "accepted",
            "evidence": [GAUGE_STRESS_ENERGY_POLICY, GAUGE_STRESS_ENERGY_LOWER_INDEX_POLICY],
            "assessment": "The gauge stress-energy convention is pinned.",
        },
        {
            "row_id": "matter_stress_energy_policy_selected",
            "status": "accepted",
            "evidence": MATTER_STRESS_ENERGY_POLICY,
            "assessment": "The bounded symmetric Dirac stress-energy candidate is indexed.",
        },
        {
            "row_id": "total_stress_energy_policy_selected",
            "status": "accepted",
            "evidence": TOTAL_STRESS_ENERGY_POLICY,
            "assessment": "The total stress-energy definition policy is indexed.",
        },
        {
            "row_id": "exchange_targets_remain_future_work",
            "status": "accepted",
            "evidence": EXCHANGE_ROUTE_PREVIEW,
            "assessment": "Gauge-sector, matter-sector, and total exchange routes remain future proof obligations.",
        },
        {
            "row_id": "next_target_is_result_review",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The policy packet rotates to result review before any exchange proof.",
        },
        {
            "row_id": "derivation_exchange_closure_and_promotion_claims_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Stress-energy derivation, exchange proof, closure, validation, and promotion remain blocked.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_stress_energy_definition_policy_packet",
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


def build_toe_native_psi_a_u1_stress_energy_definition_policy_packet(
    *,
    obligation_packet_path: Path = STRESS_ENERGY_OBLIGATION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    obligation_packet = _read_json(obligation_packet_path)
    definition_policy_rows = _definition_policy_rows()
    review_criteria = _review_criteria(obligation_packet)
    acceptance_criteria = {
        "consumes_expected_obligation_packet": (
            obligation_packet.get("schema_id") == STRESS_ENERGY_OBLIGATION_SCHEMA_ID
            and obligation_packet.get("packet_id") == STRESS_ENERGY_OBLIGATION_PACKET_ID
            and obligation_packet.get("outcome_id") == STRESS_ENERGY_OBLIGATION_OUTCOME
            and obligation_packet.get("packet_result") == STRESS_ENERGY_OBLIGATION_PACKET_RESULT
            and obligation_packet.get("selected_next_target") == CONSUMED_TARGET
            and obligation_packet.get("accepted") is True
        ),
        "obligation_targets_preserved": (
            obligation_packet.get("gauge_sector_exchange_target")
            == GAUGE_SECTOR_EXCHANGE_TARGET
            and obligation_packet.get("matter_sector_exchange_target")
            == MATTER_SECTOR_EXCHANGE_TARGET
            and obligation_packet.get("total_conservation_expanded_target")
            == TOTAL_CONSERVATION_EXPANDED_TARGET
        ),
        "definition_policies_complete": len(definition_policy_rows) == 3,
        "blocked_claims_complete": len(BLOCKED_CLAIMS) == 14,
        "all_definition_policies_selected_not_derived": all(
            row["status"] == "selected_policy_not_derived"
            for row in definition_policy_rows
        ),
        "next_target_is_result_review": NEXT_TARGET
        == "review_toe_native_psi_A_u1_stress_energy_definition_policy_packet_result",
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_PACKET_"
            "REQUIRES_REMEDIATION"
        ),
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_stress_energy_and_exchange_obligation_packet_result": (
            STRESS_ENERGY_OBLIGATION_OUTCOME
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
        "matter_sector_exchange_target": MATTER_SECTOR_EXCHANGE_TARGET,
        "total_conservation_target": TOTAL_CONSERVATION_TARGET,
        "total_conservation_expanded_target": TOTAL_CONSERVATION_EXPANDED_TARGET,
        "C_exchange_candidate": C_EXCHANGE_CANDIDATE,
        "C_exchange_equation": C_EXCHANGE_EQUATION,
        "exchange_route_preview": EXCHANGE_ROUTE_PREVIEW,
        "stress_energy_definition_policies": definition_policy_rows,
        "stress_energy_definition_policy_count": len(definition_policy_rows),
        "stress_energy_policy_ids": [row["policy_id"] for row in definition_policy_rows],
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "stress_energy_definition_policy_packet_prepared": accepted,
        "stress_energy_policy_indexed": accepted,
        "stress_energy_definitions_selected": accepted,
        "gauge_stress_energy_definition_selected": accepted,
        "matter_stress_energy_definition_selected": accepted,
        "total_stress_energy_definition_selected": accepted,
        "symmetric_dirac_stress_energy_policy_selected": accepted,
        "exchange_targets_preserved": accepted,
        "stress_energy_definition_policy_packet_result_review_selected": accepted,
        "stress_energy_definition_policy_packet_result_review_authorized": accepted,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "stress_energy_derived": False,
        "stress_energy_metric_variation_derived": False,
        "stress_energy_tetrad_variation_derived": False,
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
            "treat stress-energy policy indexing as metric or tetrad variation",
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
            "This policy packet selects T_A^{mu nu} = - F^{mu}{}_{alpha} "
            "F^{nu alpha} + 1/4 g^{mu nu} F_{alpha beta}F^{alpha beta}, "
            "selects a bounded symmetric Dirac stress-energy candidate "
            "T_psi^{mu nu} = (i/4)[...], and defines "
            "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}. It performs no "
            "metric/tetrad variation and proves no exchange identity."
        ),
        "plain_meaning": PLAIN_MEANING,
        "non_claim_boundary": (
            "This is a stress-energy definition policy packet only. It selects "
            "the gauge stress-energy policy, the bounded symmetric Dirac "
            "matter stress-energy candidate policy, and the total stress-"
            "energy definition T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}. "
            "It records no stress-energy derivation from "
            "metric/tetrad variation, no gauge-sector exchange proof, no "
            "matter-sector exchange proof, no total conservation proof, no "
            "C_exchange closeout, no full Maxwell closure, no EM-QFT closure, "
            "no QFT-GR closure, no quantized electromagnetism, no anomaly "
            "analysis, no Standard Model derivation, no Phase 2 authorization, "
            "no empirical validation, and no master-action promotion. The full "
            "ToeFormal aggregate is recorded as NOT_RUN for this packet."
        ),
        "validation_policy": validation_policy,
        "lean_validation_policy": LEAN_VALIDATION_POLICY_ID,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "source_inputs": {
            "stress_energy_exchange_obligation_json": _ptr(obligation_packet_path),
            "stress_energy_exchange_obligation_outcome": (
                STRESS_ENERGY_OBLIGATION_OUTCOME
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
        description=(
            "Prepare the ToE-native psi-A U(1) stress-energy definition policy "
            "packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--obligation-packet",
        type=Path,
        default=STRESS_ENERGY_OBLIGATION_PACKET_PATH,
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    payload = build_toe_native_psi_a_u1_stress_energy_definition_policy_packet(
        obligation_packet_path=args.obligation_packet,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(args.out, payload)
    print(args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
