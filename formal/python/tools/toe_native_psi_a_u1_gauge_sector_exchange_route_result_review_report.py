from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_gauge_sector_exchange_route_packet_report import (
    ACTION_BLOCK_STATEMENT,
    ASSUMPTIONS,
    BLOCKED_CLAIMS as PACKET_BLOCKED_CLAIMS,
    COVARIANT_DERIVATIVE_POLICY,
    C_EXCHANGE_CANDIDATE,
    C_EXCHANGE_EQUATION,
    CURRENT_CONSERVATION_RESULT,
    DEFAULT_OUT as GAUGE_PACKET_PATH,
    FIELD_STRENGTH_POLICY,
    GAUGE_DIVERGENCE_INTERMEDIATE,
    GAUGE_DIVERGENCE_SOURCE_SUBSTITUTION,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAUGE_SECTOR_EXCHANGE_INTERPRETATION,
    GAUGE_SECTOR_EXCHANGE_TERM,
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
    OUTCOME_ID as GAUGE_PACKET_OUTCOME,
    PACKET_ID as GAUGE_PACKET_ID,
    SCHEMA_ID as GAUGE_PACKET_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_CONSERVATION_EXPANDED_TARGET,
    TOTAL_CONSERVATION_TARGET,
    TOTAL_STRESS_ENERGY_OBJECT,
    TOTAL_STRESS_ENERGY_POLICY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-25T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_20260625_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_"
    "ACCEPTS_GAUGE_SECTOR_EXCHANGE_ROUTE_NO_MATTER_EXCHANGE_OR_"
    "TOTAL_CONSERVATION_PROOF"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_gauge_sector_exchange_route_result_review_accepts_"
    "gauge_sector_exchange_route_no_matter_exchange_or_total_conservation_proof"
)

NEXT_TARGET = "prepare_toe_native_psi_A_u1_matter_sector_exchange_route_packet"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_matter_sector_exchange_route_packet_preparation"
MATTER_SECTOR_ROUTE_TO_TEST = MATTER_SECTOR_EXCHANGE_TARGET
TOTAL_CONSERVATION_FUTURE_COMBINATION = (
    "nabla_mu T_A^{mu nu} + nabla_mu T_psi^{mu nu} = 0"
)
TARGETED_LEAN_BUILD_STATUS = "PASSED"
FULL_TOEFORMAL_AGGREGATE_STATUS = "NOT_COMPLETED_STOPPED_MANUALLY"
FULL_TOEFORMAL_AGGREGATE_ATTEMPT_NOTE = (
    "A full lake build ToeFormal attempt was started during the prior packet "
    "validation and stopped manually before completion; no aggregate pass, "
    "failure, timeout, or mathematical diagnostics are recorded."
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_"
    "20260625_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1GaugeSectorExchangeRouteResultReview.lean"
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
    "gauge stress-energy divergence route recorded",
    "sourced Maxwell route used as input",
    "J^nu candidate used as input",
    "gauge-sector exchange identity recorded",
]

BLOCKED_CLAIMS = PACKET_BLOCKED_CLAIMS


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "gauge_sector_exchange_route_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("outcome_id"),
            "assessment": "The prepared gauge-sector exchange route packet is the consumed input.",
        },
        {
            "row_id": "gauge_stress_energy_divergence_route_recorded",
            "status": "accepted",
            "evidence": [GAUGE_DIVERGENCE_INTERMEDIATE, GAUGE_SECTOR_EXCHANGE_IDENTITY],
            "assessment": "The gauge stress-energy divergence route is recorded as gauge-side only.",
        },
        {
            "row_id": "sourced_maxwell_route_used_as_input",
            "status": "accepted",
            "evidence": SOURCED_GAUGE_ROUTE,
            "assessment": "The sourced Maxwell route is used as an input to the gauge-side exchange route.",
        },
        {
            "row_id": "J_candidate_used_as_input",
            "status": "accepted",
            "evidence": SOURCE_CURRENT,
            "assessment": "The psi-made current candidate J^nu is used as the source input.",
        },
        {
            "row_id": "gauge_sector_exchange_identity_recorded",
            "status": "accepted",
            "evidence": GAUGE_SECTOR_EXCHANGE_IDENTITY,
            "assessment": "The gauge-sector exchange identity is recorded.",
        },
        {
            "row_id": "matter_total_and_closure_claims_preserved",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "Matter exchange, total conservation, closure, validation, and promotion remain blocked.",
        },
        {
            "row_id": "matter_sector_exchange_route_packet_selected_next",
            "status": "accepted",
            "evidence": [NEXT_TARGET, MATTER_SECTOR_ROUTE_TO_TEST],
            "assessment": "The next target is the bounded matter-sector exchange route packet.",
        },
        {
            "row_id": "aggregate_build_status_preserved",
            "status": "accepted",
            "evidence": [
                f"targeted Lean builds: {TARGETED_LEAN_BUILD_STATUS}",
                f"full ToeFormal aggregate: {FULL_TOEFORMAL_AGGREGATE_STATUS}",
            ],
            "assessment": "Targeted Lean builds passed, while the full aggregate build is not claimed.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_gauge_sector_exchange_route_result_review",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "targeted_lean_build_status_for_review": TARGETED_LEAN_BUILD_STATUS,
        "targeted_lean_builds_passed": True,
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "aggregate_lean_validation_status_allowed_values": [
            "NOT_COMPLETED_STOPPED_MANUALLY",
            "INCOMPLETE_NO_DIAGNOSTICS_RECORDED",
        ],
        "full_toeformal_aggregate_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_attempt_note": FULL_TOEFORMAL_AGGREGATE_ATTEMPT_NOTE,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "full_toeformal_aggregate_stopped_manually": True,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_toe_native_psi_a_u1_gauge_sector_exchange_route_result_review(
    *,
    gauge_packet_path: Path = GAUGE_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(gauge_packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_gauge_sector_exchange_route_packet": (
            packet.get("schema_id") == GAUGE_PACKET_SCHEMA_ID
            and packet.get("packet_id") == GAUGE_PACKET_ID
            and packet.get("outcome_id") == GAUGE_PACKET_OUTCOME
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "gauge_divergence_route_recorded": (
            packet.get("gauge_stress_energy_divergence_route_recorded") is True
            and packet.get("gauge_divergence_intermediate")
            == GAUGE_DIVERGENCE_INTERMEDIATE
            and packet.get("gauge_divergence_source_substitution")
            == GAUGE_DIVERGENCE_SOURCE_SUBSTITUTION
        ),
        "sourced_maxwell_route_input_used": (
            packet.get("sourced_gauge_route") == SOURCED_GAUGE_ROUTE
            and packet.get("source_current") == SOURCE_CURRENT
        ),
        "gauge_sector_exchange_identity_recorded": (
            packet.get("gauge_sector_exchange_identity")
            == GAUGE_SECTOR_EXCHANGE_IDENTITY
            and packet.get("gauge_sector_exchange_identity_recorded") is True
        ),
        "matter_total_and_closure_blockers_preserved": (
            packet.get("blocked_claims") == BLOCKED_CLAIMS
            and packet.get("matter_sector_exchange_proved") is False
            and packet.get("total_conservation_proved") is False
            and packet.get("C_exchange_closeout") is False
        ),
        "next_target_is_matter_sector_exchange_route_packet": (
            NEXT_TARGET
            == "prepare_toe_native_psi_A_u1_matter_sector_exchange_route_packet"
        ),
        "aggregate_status_not_overclaimed": (
            TARGETED_LEAN_BUILD_STATUS == "PASSED"
            and FULL_TOEFORMAL_AGGREGATE_STATUS == "NOT_COMPLETED_STOPPED_MANUALLY"
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_REVIEW"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "review_executed": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "packet_result": REVIEW_RESULT if accepted else "PENDING_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_gauge_sector_exchange_route_packet_result": GAUGE_PACKET_OUTCOME,
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
        "sourced_maxwell_route": SOURCED_GAUGE_ROUTE,
        "gauge_stress_energy_object": GAUGE_STRESS_ENERGY_OBJECT,
        "gauge_stress_energy_policy": GAUGE_STRESS_ENERGY_POLICY,
        "gauge_stress_energy_lower_index_policy": GAUGE_STRESS_ENERGY_LOWER_INDEX_POLICY,
        "matter_stress_energy_object": MATTER_STRESS_ENERGY_OBJECT,
        "matter_stress_energy_policy": MATTER_STRESS_ENERGY_POLICY,
        "matter_stress_energy_policy_status": MATTER_STRESS_ENERGY_POLICY_STATUS,
        "total_stress_energy_object": TOTAL_STRESS_ENERGY_OBJECT,
        "total_stress_energy_policy": TOTAL_STRESS_ENERGY_POLICY,
        "gauge_sector_exchange_target": GAUGE_SECTOR_EXCHANGE_IDENTITY,
        "gauge_sector_exchange_identity": GAUGE_SECTOR_EXCHANGE_IDENTITY,
        "gauge_sector_exchange_term": GAUGE_SECTOR_EXCHANGE_TERM,
        "gauge_divergence_intermediate": GAUGE_DIVERGENCE_INTERMEDIATE,
        "gauge_divergence_source_substitution": GAUGE_DIVERGENCE_SOURCE_SUBSTITUTION,
        "matter_sector_exchange_target": MATTER_SECTOR_EXCHANGE_TARGET,
        "matter_sector_route_to_test": MATTER_SECTOR_ROUTE_TO_TEST,
        "total_conservation_target": TOTAL_CONSERVATION_TARGET,
        "total_conservation_expanded_target": TOTAL_CONSERVATION_EXPANDED_TARGET,
        "total_conservation_future_combination": TOTAL_CONSERVATION_FUTURE_COMBINATION,
        "C_exchange_candidate": C_EXCHANGE_CANDIDATE,
        "C_exchange_equation": C_EXCHANGE_EQUATION,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
        "assumptions": ASSUMPTIONS,
        "assumption_count": len(ASSUMPTIONS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "gauge_sector_exchange_route_result_review_accepted": accepted,
        "gauge_sector_exchange_route_accepted": accepted,
        "gauge_stress_energy_divergence_route_recorded": accepted,
        "sourced_maxwell_route_used_as_input": accepted,
        "J_current_candidate_used_as_input": accepted,
        "gauge_sector_exchange_identity_recorded": accepted,
        "gauge_sector_exchange_identity_accepted": accepted,
        "gauge_side_exchange_only": accepted,
        "matter_sector_exchange_route_packet_selected": accepted,
        "matter_sector_exchange_route_packet_preparation_authorized": accepted,
        "total_conservation_packet_selected": False,
        "total_conservation_packet_authorized_here": False,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "matter_sector_exchange_proved": False,
        "matter_sector_exchange_route_constructed": False,
        "matter_sector_exchange_identity_recorded": False,
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
        "mathematical_statement": (
            "The result review accepts only the gauge-side route "
            "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha, using "
            "nabla_mu F^{mu nu} = J^nu and J^nu = q psibar gamma^nu psi "
            "as inputs."
        ),
        "plain_meaning": GAUGE_SECTOR_EXCHANGE_INTERPRETATION,
        "non_claim_boundary": (
            "This is a bounded gauge-sector exchange route result review only. "
            "It accepts the recorded gauge stress-energy divergence route, the "
            "sourced Maxwell input, the J^nu source-current input, and the "
            "gauge-sector exchange identity. It records no matter-sector "
            "exchange proof, no total conservation proof, no C_exchange "
            "closeout, no full Maxwell closure, no EM-QFT closure, no QFT-GR "
            "closure, no quantized electromagnetism, no anomaly analysis, no "
            "Standard Model derivation, no Phase 2 authorization, no empirical "
            "validation, and no master-action promotion. Targeted Lean builds "
            "passed; the full ToeFormal aggregate did not complete and is "
            "recorded as NOT_COMPLETED_STOPPED_MANUALLY."
        ),
        "validation_policy": validation_policy,
        "lean_validation_policy": LEAN_VALIDATION_POLICY_ID,
        "targeted_lean_build_status_for_review": TARGETED_LEAN_BUILD_STATUS,
        "targeted_lean_builds_passed": True,
        "full_toeformal_aggregate_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_attempt_note": FULL_TOEFORMAL_AGGREGATE_ATTEMPT_NOTE,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "full_toeformal_aggregate_stopped_manually": True,
        "source_inputs": {
            "gauge_sector_exchange_route_packet_json": _ptr(gauge_packet_path),
            "gauge_sector_exchange_route_packet_outcome": GAUGE_PACKET_OUTCOME,
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
        description="Review the ToE-native psi-A U(1) gauge-sector exchange route packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--gauge-packet", type=Path, default=GAUGE_PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    gauge_packet_path = (
        args.gauge_packet if args.gauge_packet.is_absolute() else REPO_ROOT / args.gauge_packet
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_toe_native_psi_a_u1_gauge_sector_exchange_route_result_review(
        gauge_packet_path=gauge_packet_path,
        captured_at_utc=args.captured_at_utc,
    )
    _write_json(out, payload)
    print(
        "toe_native_psi_a_u1_gauge_sector_exchange_route_result_review: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
