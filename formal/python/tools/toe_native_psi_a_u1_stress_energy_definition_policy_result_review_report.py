from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_stress_energy_definition_policy_packet_report import (
    ACTION_BLOCK_STATEMENT,
    BLOCKED_CLAIMS as POLICY_BLOCKED_CLAIMS,
    C_EXCHANGE_CANDIDATE,
    C_EXCHANGE_EQUATION,
    CONSUMED_TARGET as POLICY_PACKET_CONSUMED_TARGET,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CONSERVATION_RESULT,
    DEFAULT_OUT as STRESS_ENERGY_POLICY_PACKET_PATH,
    EXCHANGE_ROUTE_PREVIEW,
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
    OUTCOME_ID as STRESS_ENERGY_POLICY_OUTCOME,
    PACKET_CLASSIFICATION as STRESS_ENERGY_POLICY_CLASSIFICATION,
    PACKET_ID as STRESS_ENERGY_POLICY_PACKET_ID,
    PACKET_RESULT as STRESS_ENERGY_POLICY_PACKET_RESULT,
    SCHEMA_ID as STRESS_ENERGY_POLICY_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_CONSERVATION_EXPANDED_TARGET,
    TOTAL_CONSERVATION_TARGET,
    TOTAL_STRESS_ENERGY_OBJECT,
    TOTAL_STRESS_ENERGY_POLICY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_20260624_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_"
    "ACCEPTS_STRESS_ENERGY_POLICY_NO_EXCHANGE_PROOF_OR_EM_QFT_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_stress_energy_definition_policy_result_review_accepts_"
    "stress_energy_policy_no_exchange_proof_or_em_qft_closure"
)

NEXT_TARGET = "prepare_toe_native_psi_A_u1_gauge_sector_exchange_route_packet"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_gauge_sector_exchange_route_packet_preparation"
FUTURE_ROUTE_QUESTION = (
    "Does the gauge field lose exactly the energy-momentum that matter gains?"
)
GAUGE_SECTOR_EXCHANGE_ROUTE_TO_TEST = GAUGE_SECTOR_EXCHANGE_TARGET
GAUGE_SECTOR_EXCHANGE_INPUTS = [
    SOURCED_GAUGE_ROUTE,
    SOURCE_CURRENT,
    GAUGE_STRESS_ENERGY_POLICY,
]
SIGN_CHECK_POLICY = (
    "The gauge-sector exchange sign must be checked against the selected "
    "T_A convention and metric convention before any exchange closeout."
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_"
    "20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1StressEnergyDefinitionPolicyResultReview.lean"
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
    "T_A indexed under the existing gauge convention",
    "T_psi indexed as bounded symmetric Dirac stress-energy policy",
    "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}",
    "stress-energy definitions selected for future exchange testing",
]

BLOCKED_CLAIMS = POLICY_BLOCKED_CLAIMS


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "stress_energy_definition_policy_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("outcome_id"),
            "assessment": "The stress-energy definition policy packet is the consumed review input.",
        },
        {
            "row_id": "gauge_stress_energy_policy_accepted",
            "status": "accepted",
            "evidence": [
                GAUGE_STRESS_ENERGY_POLICY,
                GAUGE_STRESS_ENERGY_LOWER_INDEX_POLICY,
            ],
            "assessment": "T_A is indexed under the existing gauge convention.",
        },
        {
            "row_id": "matter_stress_energy_policy_accepted",
            "status": "accepted",
            "evidence": MATTER_STRESS_ENERGY_POLICY,
            "assessment": "T_psi is indexed as the bounded symmetric Dirac stress-energy policy.",
        },
        {
            "row_id": "total_stress_energy_policy_accepted",
            "status": "accepted",
            "evidence": TOTAL_STRESS_ENERGY_POLICY,
            "assessment": "The total stress-energy policy is the sum of gauge and matter sectors.",
        },
        {
            "row_id": "future_exchange_testing_ready",
            "status": "accepted",
            "evidence": [
                GAUGE_SECTOR_EXCHANGE_TARGET,
                MATTER_SECTOR_EXCHANGE_TARGET,
                TOTAL_CONSERVATION_EXPANDED_TARGET,
            ],
            "assessment": "The definitions are ready for future exchange testing only.",
        },
        {
            "row_id": "gauge_sector_exchange_packet_selected_next",
            "status": "accepted",
            "evidence": [NEXT_TARGET, GAUGE_SECTOR_EXCHANGE_ROUTE_TO_TEST],
            "assessment": "The next target is the bounded gauge-sector exchange route packet.",
        },
        {
            "row_id": "sign_check_preserved_for_future_route",
            "status": "accepted",
            "evidence": SIGN_CHECK_POLICY,
            "assessment": "The gauge-sector exchange sign remains a future route check.",
        },
        {
            "row_id": "stress_derivation_exchange_closure_and_promotion_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Stress-energy derivation, exchange proof, closure, validation, and promotion remain blocked.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_stress_energy_definition_policy_result_review",
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


def build_toe_native_psi_a_u1_stress_energy_definition_policy_result_review(
    *,
    stress_energy_policy_packet_path: Path = STRESS_ENERGY_POLICY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(stress_energy_policy_packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_stress_energy_definition_policy_packet": (
            packet.get("schema_id") == STRESS_ENERGY_POLICY_SCHEMA_ID
            and packet.get("packet_id") == STRESS_ENERGY_POLICY_PACKET_ID
            and packet.get("outcome_id") == STRESS_ENERGY_POLICY_OUTCOME
            and packet.get("packet_result") == STRESS_ENERGY_POLICY_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "stress_energy_definitions_selected": (
            packet.get("gauge_stress_energy_policy") == GAUGE_STRESS_ENERGY_POLICY
            and packet.get("matter_stress_energy_policy") == MATTER_STRESS_ENERGY_POLICY
            and packet.get("total_stress_energy_policy") == TOTAL_STRESS_ENERGY_POLICY
            and packet.get("stress_energy_definitions_selected") is True
        ),
        "exchange_targets_preserved_without_proof": (
            packet.get("gauge_sector_exchange_target") == GAUGE_SECTOR_EXCHANGE_TARGET
            and packet.get("matter_sector_exchange_target") == MATTER_SECTOR_EXCHANGE_TARGET
            and packet.get("total_conservation_expanded_target")
            == TOTAL_CONSERVATION_EXPANDED_TARGET
            and packet.get("exchange_targets_preserved") is True
            and packet.get("gauge_sector_exchange_proved") is False
            and packet.get("matter_sector_exchange_proved") is False
        ),
        "blocked_claims_preserved": (
            packet.get("blocked_claims") == BLOCKED_CLAIMS
            and packet.get("stress_energy_metric_variation_derived") is False
            and packet.get("stress_energy_tetrad_variation_derived") is False
            and packet.get("total_stress_energy_conservation_proved") is False
            and packet.get("C_exchange_definition_closeout") is False
            and packet.get("em_qft_closure_claimed") is False
            and packet.get("qft_gr_closure_claimed") is False
            and packet.get("master_action_promoted") is False
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "next_target_is_gauge_sector_exchange_route_packet": NEXT_TARGET
        == "prepare_toe_native_psi_A_u1_gauge_sector_exchange_route_packet",
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_"
            "REQUIRES_REMEDIATION"
        ),
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "future_route_question": FUTURE_ROUTE_QUESTION,
        "gauge_sector_exchange_route_to_test": GAUGE_SECTOR_EXCHANGE_ROUTE_TO_TEST,
        "gauge_sector_exchange_inputs": GAUGE_SECTOR_EXCHANGE_INPUTS,
        "sign_check_policy": SIGN_CHECK_POLICY,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
        "stress_energy_policy_schema_id": STRESS_ENERGY_POLICY_SCHEMA_ID,
        "stress_energy_policy_packet_id": STRESS_ENERGY_POLICY_PACKET_ID,
        "stress_energy_policy_packet_outcome": STRESS_ENERGY_POLICY_OUTCOME,
        "stress_energy_policy_packet_result": STRESS_ENERGY_POLICY_PACKET_RESULT,
        "stress_energy_policy_packet_classification": STRESS_ENERGY_POLICY_CLASSIFICATION,
        "stress_energy_policy_packet_consumed_target": POLICY_PACKET_CONSUMED_TARGET,
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
        "stress_energy_definition_policy_accepted": accepted,
        "T_A_policy_accepted": accepted,
        "T_psi_policy_accepted": accepted,
        "T_total_policy_accepted": accepted,
        "gauge_stress_energy_policy_accepted": accepted,
        "matter_stress_energy_policy_accepted": accepted,
        "total_stress_energy_policy_accepted": accepted,
        "stress_energy_definitions_selected_for_future_exchange_testing": accepted,
        "gauge_sector_exchange_route_packet_selected": accepted,
        "gauge_sector_exchange_route_packet_preparation_authorized": accepted,
        "gauge_sector_exchange_sign_check_required": accepted,
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
            "treat stress-energy policy review as metric or tetrad variation",
            "prove gauge-sector exchange in this review",
            "prove matter-sector exchange in this review",
            "prove total stress-energy conservation in this review",
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
            "This result review accepts the selected stress-energy policies: "
            "T_A under the existing gauge convention, bounded symmetric Dirac "
            "T_psi, and T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}. It "
            "selects a future gauge-sector exchange packet to test "
            "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha using "
            "nabla_mu F^{mu nu} = J^nu and J^nu = q psibar gamma^nu psi."
        ),
        "plain_meaning": (
            "The stress-energy objects are accepted as policy definitions so a "
            "future packet can test whether the gauge field transfers "
            "energy-momentum to matter with the expected sign."
        ),
        "non_claim_boundary": (
            "This is a stress-energy definition policy result review only. It "
            "accepts T_A under the existing gauge convention, T_psi as a "
            "bounded symmetric Dirac stress-energy policy, and "
            "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}. It records no "
            "stress-energy derivation from metric/tetrad variation, no "
            "gauge-sector exchange proof, no matter-sector exchange proof, no "
            "total conservation proof, no C_exchange closeout, no full Maxwell "
            "closure, no EM-QFT closure, no QFT-GR closure, no quantized "
            "electromagnetism, no anomaly analysis, no Standard Model "
            "derivation, no Phase 2 authorization, no empirical validation, "
            "and no master-action promotion. The full ToeFormal aggregate is "
            "recorded as NOT_RUN for this review."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "stress_energy_policy_packet_file": _ptr(STRESS_ENERGY_POLICY_PACKET_PATH),
        "lean_validation_policy": LEAN_VALIDATION_POLICY_ID,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePsiAU1StressEnergyDefinitionPolicyResultReview",
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


def write_toe_native_psi_a_u1_stress_energy_definition_policy_result_review(
    *,
    stress_energy_policy_packet_path: Path = STRESS_ENERGY_POLICY_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_toe_native_psi_a_u1_stress_energy_definition_policy_result_review(
        stress_energy_policy_packet_path=stress_energy_policy_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the ToE-native psi-A U(1) stress-energy definition policy "
            "result review."
        )
    )
    parser.add_argument(
        "--stress-energy-policy-packet",
        type=Path,
        default=STRESS_ENERGY_POLICY_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    stress_energy_policy_packet_path = (
        args.stress_energy_policy_packet
        if args.stress_energy_policy_packet.is_absolute()
        else REPO_ROOT / args.stress_energy_policy_packet
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = write_toe_native_psi_a_u1_stress_energy_definition_policy_result_review(
        stress_energy_policy_packet_path=stress_energy_policy_packet_path,
        out=out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "toe_native_psi_a_u1_stress_energy_definition_policy_result_review: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
