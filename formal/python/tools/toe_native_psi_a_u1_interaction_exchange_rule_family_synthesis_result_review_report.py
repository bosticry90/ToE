from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_packet_report import (
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as SYNTHESIS_PACKET_PATH,
    EXCHANGE_TERM_CANCELLATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as SYNTHESIS_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as SYNTHESIS_PACKET_OUTCOME,
    PACKET_ID as SYNTHESIS_PACKET_ID,
    PACKET_RESULT as SYNTHESIS_PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RULE_CLASSIFICATION,
    RULE_EPISTEMIC_STATUS,
    RULE_FAMILY_CLASSIFICATION,
    RULE_FAMILY_EPISTEMIC_STATUS,
    RULE_FAMILY_ID,
    SCHEMA_ID as SYNTHESIS_PACKET_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_"
    "20260626_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_"
    "ACCEPTS_CURRENT_SOURCE_EXCHANGE_AND_TOTAL_CONSERVATION_SYNTHESIS_"
    "NO_EM_QFT_OR_CK_ACTION_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_interaction_exchange_rule_family_synthesis_result_review_"
    "accepts_current_source_exchange_and_total_conservation_synthesis_"
    "no_em_qft_or_ck_action_closure"
)
NEXT_TARGET = "prepare_toe_native_psi_A_u1_interaction_exchange_rule_family_closeout"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_interaction_exchange_rule_family_closeout_preparation"
CLOSEOUT_OUTCOME_HINT = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSED_AS_BOUNDED_"
    "CURRENT_SOURCE_AND_EXCHANGE_ADMISSIBILITY_FAMILY_NO_EM_QFT_OR_CK_ACTION_CLOSURE"
)

ACCEPTED_REVIEW_FINDINGS = [
    "psi-A current route synthesized",
    "current conservation route synthesized",
    "sourced Maxwell route synthesized",
    "gauge-sector exchange route synthesized",
    "matter-sector exchange route synthesized",
    "total stress-energy conservation route synthesized",
    "C_exchange admissibility rule included",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_"
        "20260626_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1InteractionExchangeRuleFamilySynthesisResultReview.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "functional_action_embedding_claimed": False,
        "C_exchange_functional_embedding_claimed": False,
        "C_k_action_embedding_claimed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "multiplier_action_route_selected": False,
        "penalty_route_selected": False,
        "candidate_varied": False,
        "direct_dynamical_law_interpretation_selected": False,
        "direct_force_law_claimed": False,
        "new_force_law_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "quantized_electromagnetism_claimed": False,
        "anomaly_analysis_performed": False,
        "standard_model_derivation_claimed": False,
        "phase2_authorized": False,
        "empirical_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "master_action_promotion": False,
    }


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "synthesis_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("packet_result"),
            "assessment": "The prepared interaction exchange synthesis packet is consumed.",
        },
        {
            "row_id": "psi_A_current_route_synthesized",
            "status": "accepted",
            "evidence": CURRENT_CANDIDATE,
            "assessment": "The A-variation current candidate route is accepted as synthesized.",
        },
        {
            "row_id": "current_conservation_route_synthesized",
            "status": "accepted",
            "evidence": CURRENT_CONSERVATION_RESULT,
            "assessment": "The current-conservation route is accepted as synthesized.",
        },
        {
            "row_id": "sourced_maxwell_route_synthesized",
            "status": "accepted",
            "evidence": [SOURCE_CURRENT, SOURCED_GAUGE_ROUTE],
            "assessment": "The sourced Maxwell route is accepted as bounded synthesis context.",
        },
        {
            "row_id": "gauge_sector_exchange_route_synthesized",
            "status": "accepted",
            "evidence": GAUGE_SECTOR_EXCHANGE_IDENTITY,
            "assessment": "The gauge-sector exchange route is accepted as synthesized.",
        },
        {
            "row_id": "matter_sector_exchange_route_synthesized",
            "status": "accepted",
            "evidence": MATTER_SECTOR_EXCHANGE_IDENTITY,
            "assessment": "The matter-sector equal-and-opposite exchange route is accepted as synthesized.",
        },
        {
            "row_id": "total_stress_energy_conservation_route_synthesized",
            "status": "accepted",
            "evidence": [
                TOTAL_STRESS_ENERGY_OBJECT,
                EXCHANGE_TERM_CANCELLATION,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            ],
            "assessment": "The total stress-energy conservation route is accepted as synthesized.",
        },
        {
            "row_id": "C_exchange_admissibility_rule_included",
            "status": "accepted",
            "evidence": [
                C_EXCHANGE_CONSTRAINT_FORM,
                C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
                C_EXCHANGE_ADMISSIBILITY_CONDITION,
            ],
            "assessment": "C_exchange is included only as an admissibility rule.",
        },
        {
            "row_id": "no_forbidden_closure_or_action_claims",
            "status": "accepted",
            "evidence": [
                "C_k_action_embedding_claimed=false",
                "C_k_action_variation_executed=false",
                "multiplier_action_route_selected=false",
                "penalty_route_selected=false",
                "em_qft_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No action embedding, closure, empirical, Phase 2, or promotion claim is accepted.",
        },
        {
            "row_id": "interaction_exchange_rule_family_closeout_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is the bounded interaction exchange rule-family closeout.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_psi_A_u1_interaction_exchange_rule_family_synthesis_result_review"
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
        "aggregate_lean_validation_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "aggregate_lean_validation_status_allowed_values": ["NOT_RUN"],
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_toeformal_aggregate_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_result_review(
    *,
    synthesis_packet_path: Path = SYNTHESIS_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(synthesis_packet_path)
    review_criteria = _review_criteria(packet)
    expected_route_ids = [
        "A_variation_current_candidate",
        "current_conservation",
        "sourced_maxwell_route",
        "gauge_sector_exchange",
        "matter_sector_exchange",
        "total_stress_energy_conservation",
        "C_exchange_rule",
    ]
    route_ids = [row.get("route_id") for row in packet.get("route_family_chain", [])]
    acceptance_criteria = {
        "consumes_expected_synthesis_packet": (
            packet.get("schema_id") == SYNTHESIS_PACKET_SCHEMA_ID
            and packet.get("packet_id") == SYNTHESIS_PACKET_ID
            and packet.get("outcome_id") == SYNTHESIS_PACKET_OUTCOME
            and packet.get("packet_result") == SYNTHESIS_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "route_family_chain_complete": route_ids == expected_route_ids,
        "required_routes_synthesized": (
            packet.get("current_candidate") == CURRENT_CANDIDATE
            and packet.get("current_conservation_result") == CURRENT_CONSERVATION_RESULT
            and packet.get("sourced_gauge_route") == SOURCED_GAUGE_ROUTE
            and packet.get("gauge_sector_exchange_identity")
            == GAUGE_SECTOR_EXCHANGE_IDENTITY
            and packet.get("matter_sector_exchange_identity")
            == MATTER_SECTOR_EXCHANGE_IDENTITY
            and packet.get("total_stress_energy_conservation_identity")
            == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_rule_included_as_admissibility_only": (
            packet.get("C_exchange_constraint_id") == C_EXCHANGE_CONSTRAINT_ID
            and packet.get("C_exchange_constraint_form") == C_EXCHANGE_CONSTRAINT_FORM
            and packet.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
            and packet.get("C_exchange_rule_epistemic_status")
            == RULE_EPISTEMIC_STATUS
        ),
        "no_forbidden_claims": all(
            packet.get(key) is False
            for key in _false_boundary_flags()
            if key in packet
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_"
            "SYNTHESIS_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_"
            "RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "review_result": OUTCOME_ID if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_"
            "SYNTHESIS_RESULT_REVIEW"
        ),
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "closeout_outcome_hint": CLOSEOUT_OUTCOME_HINT,
        "synthesis_packet_schema_id": SYNTHESIS_PACKET_SCHEMA_ID,
        "synthesis_packet_id": SYNTHESIS_PACKET_ID,
        "synthesis_packet_outcome": SYNTHESIS_PACKET_OUTCOME,
        "synthesis_packet_result": SYNTHESIS_PACKET_RESULT,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "rule_family_id": RULE_FAMILY_ID,
        "rule_family_classification": RULE_FAMILY_CLASSIFICATION,
        "rule_family_epistemic_status": RULE_FAMILY_EPISTEMIC_STATUS,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
        "route_family_chain": packet.get("route_family_chain", []),
        "route_family_chain_count": len(packet.get("route_family_chain", [])),
        "current_candidate": CURRENT_CANDIDATE,
        "source_current": SOURCE_CURRENT,
        "current_conservation_result": CURRENT_CONSERVATION_RESULT,
        "sourced_gauge_route": SOURCED_GAUGE_ROUTE,
        "gauge_sector_exchange_identity": GAUGE_SECTOR_EXCHANGE_IDENTITY,
        "matter_sector_exchange_identity": MATTER_SECTOR_EXCHANGE_IDENTITY,
        "exchange_term_cancellation": EXCHANGE_TERM_CANCELLATION,
        "total_stress_energy_object": TOTAL_STRESS_ENERGY_OBJECT,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_constraint_id": C_EXCHANGE_CONSTRAINT_ID,
        "C_exchange_constraint_form": C_EXCHANGE_CONSTRAINT_FORM,
        "C_exchange_total_stress_energy_form": C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
        "C_exchange_admissibility_condition": C_EXCHANGE_ADMISSIBILITY_CONDITION,
        "C_exchange_candidate_scope": C_EXCHANGE_CANDIDATE_SCOPE,
        "C_exchange_plain_meaning": C_EXCHANGE_PLAIN_MEANING,
        "C_exchange_rule_classification": RULE_CLASSIFICATION,
        "C_exchange_rule_epistemic_status": RULE_EPISTEMIC_STATUS,
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
        "synthesis_packet_accepted": accepted,
        "psi_A_current_route_synthesized": accepted,
        "current_conservation_route_synthesized": accepted,
        "sourced_maxwell_route_synthesized": accepted,
        "gauge_sector_exchange_route_synthesized": accepted,
        "matter_sector_exchange_route_synthesized": accepted,
        "total_stress_energy_conservation_route_synthesized": accepted,
        "C_exchange_admissibility_rule_included": accepted,
        "C_exchange_remains_admissibility_only": accepted,
        "current_source_exchange_and_total_conservation_synthesis_accepted": accepted,
        "interaction_exchange_rule_family_closeout_authorized": accepted,
        "interaction_exchange_rule_family_closeout_prepared": False,
        "mathematical_statement": (
            "The result review accepts the bounded psi-A U(1) interaction "
            "exchange synthesis: "
            f"{CURRENT_CANDIDATE}; {CURRENT_CONSERVATION_RESULT}; "
            f"{SOURCED_GAUGE_ROUTE}; {GAUGE_SECTOR_EXCHANGE_IDENTITY}; "
            f"{MATTER_SECTOR_EXCHANGE_IDENTITY}; "
            f"{TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY}; "
            f"{C_EXCHANGE_ADMISSIBILITY_CONDITION}."
        ),
        "plain_meaning": (
            "The review accepts that the packet has synthesized matter current, "
            "conserved current, sourced gauge route, equal-and-opposite exchange, "
            "total balance, and C_exchange as the admissibility rule for that balance."
        ),
        "non_claim_boundary": (
            "This result review accepts only the psi-A current route, current "
            "conservation route, sourced Maxwell route, gauge-sector exchange "
            "route, matter-sector exchange route, total stress-energy "
            "conservation route, and C_exchange admissibility rule inclusion. "
            "It records no C_k action embedding, no C_k action variation, no "
            "multiplier/action route, no penalty route, no direct dynamical-law "
            "interpretation, no full Maxwell closure, no EM-QFT closure, no "
            "QFT-GR closure, no quantized electromagnetism, no anomaly analysis, "
            "no Standard Model derivation, no Phase 2 authorization, no empirical "
            "validation, and no master-action promotion. The master action remains "
            "a working-form, noncanonical organizing surface."
        ),
        "critical_gate_fail_conditions": [
            "drop any required route from the accepted synthesis",
            "remove C_exchange admissibility-only status",
            "claim C_k action embedding",
            "execute C_k action variation",
            "select multiplier/action or penalty route",
            "interpret C_exchange as a new force law",
            "claim full Maxwell closure",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "claim quantized electromagnetism",
            "perform anomaly analysis",
            "derive the Standard Model",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_status_for_review": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePsiAU1InteractionExchangeRuleFamilySynthesisResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "synthesis_packet_file": _ptr(synthesis_packet_path),
            "synthesis_packet_lean_file": _ptr(SYNTHESIS_LEAN_PACKET_PATH),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }
    payload.update(_false_boundary_flags())
    return payload


def write_review(review: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(review, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Review the ToE-native psi-A U(1) interaction exchange rule-family "
            "synthesis packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--synthesis-packet", type=Path, default=SYNTHESIS_PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    synthesis_packet_path = (
        args.synthesis_packet
        if args.synthesis_packet.is_absolute()
        else REPO_ROOT / args.synthesis_packet
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_result_review(
        synthesis_packet_path=synthesis_packet_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
