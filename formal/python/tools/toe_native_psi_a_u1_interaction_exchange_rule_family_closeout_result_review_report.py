from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_report import (
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CLOSEOUT_RESULT,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as CLOSEOUT_PATH,
    EXCHANGE_TERM_CANCELLATION,
    FAMILY_CLASSIFICATION,
    FAMILY_EPISTEMIC_STATUS,
    FAMILY_SCOPE,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as CLOSEOUT_OUTCOME,
    PACKET_ID as CLOSEOUT_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RULE_CLASSIFICATION,
    RULE_EPISTEMIC_STATUS,
    RULE_FAMILY_CLASSIFICATION,
    RULE_FAMILY_EPISTEMIC_STATUS,
    RULE_FAMILY_ID,
    SCHEMA_ID as CLOSEOUT_SCHEMA_ID,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_RESULT_REVIEW_"
    "20260626_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_RESULT_REVIEW_"
    "ACCEPTS_BOUNDED_CURRENT_SOURCE_AND_EXCHANGE_ADMISSIBILITY_FAMILY_"
    "NO_EM_QFT_OR_CK_ACTION_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_interaction_exchange_rule_family_closeout_result_review_"
    "accepts_bounded_current_source_and_exchange_admissibility_family_"
    "no_em_qft_or_ck_action_closure"
)
NEXT_TARGET = "prepare_master_action_ck_family_status_synthesis_after_phi_A_and_psi_A"
NEXT_TARGET_KIND = "master_action_ck_family_status_synthesis_after_phi_A_and_psi_A_preparation"
SYNTHESIS_OUTCOME_HINT = (
    "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_PREPARED_"
    "SOURCE_BRIDGE_TRANSPORT_AND_INTERACTION_EXCHANGE_FAMILIES_SUMMARIZED_"
    "NO_MASTER_ACTION_PROMOTION"
)

ACCEPTED_REVIEW_FINDINGS = [
    "psi-A interaction family closed",
    "current/source/exchange/total-conservation route preserved",
    "C_exchange preserved as admissibility-only",
    "no C_k action embedding",
    "no C_k action variation",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_"
        "CLOSEOUT_RESULT_REVIEW_20260626_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1InteractionExchangeRuleFamilyCloseoutResultReview.lean"
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
        "multiplier_route_selected": False,
        "multiplier_action_route_selected": False,
        "penalty_route_selected": False,
        "candidate_varied": False,
        "direct_dynamical_law_claimed": False,
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
        "post_closeout_decision_executed": False,
        "master_action_surface_selected_after_closeout": False,
        "ck_family_status_synthesis_prepared": False,
        "master_action_ck_family_status_synthesis_prepared": False,
    }


def _review_criteria(closeout: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "closeout_consumed",
            "status": "accepted",
            "evidence": closeout.get("closeout_result"),
            "assessment": "The bounded interaction exchange rule-family closeout is consumed.",
        },
        {
            "row_id": "psi_A_interaction_family_closed",
            "status": "accepted",
            "evidence": CLOSEOUT_RESULT,
            "assessment": "The psi-A interaction family is accepted as closed.",
        },
        {
            "row_id": "current_source_exchange_total_conservation_route_preserved",
            "status": "accepted",
            "evidence": [
                CURRENT_CANDIDATE,
                CURRENT_CONSERVATION_RESULT,
                SOURCED_GAUGE_ROUTE,
                GAUGE_SECTOR_EXCHANGE_IDENTITY,
                MATTER_SECTOR_EXCHANGE_IDENTITY,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            ],
            "assessment": (
                "The current/source/exchange/total-conservation route is preserved."
            ),
        },
        {
            "row_id": "C_exchange_admissibility_only_preserved",
            "status": "accepted",
            "evidence": [
                C_EXCHANGE_CONSTRAINT_FORM,
                C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
                C_EXCHANGE_ADMISSIBILITY_CONDITION,
                RULE_EPISTEMIC_STATUS,
            ],
            "assessment": "C_exchange remains admissibility-only.",
        },
        {
            "row_id": "no_C_k_action_embedding_or_variation",
            "status": "accepted",
            "evidence": [
                "C_k_action_embedding_claimed=false",
                "C_k_action_variation_executed=false",
                "multiplier_route_selected=false",
                "penalty_route_selected=false",
            ],
            "assessment": "No C_k action, multiplier, penalty, or variation route is accepted.",
        },
        {
            "row_id": "no_EM_QFT_QFT_GR_or_master_action_promotion",
            "status": "accepted",
            "evidence": [
                "em_qft_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No EM-QFT closure, QFT-GR closure, or master-action promotion follows.",
        },
        {
            "row_id": "full_toeformal_aggregate_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full aggregate is preserved as NOT_RUN.",
        },
        {
            "row_id": "ck_family_status_synthesis_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is the master-action C_k family status synthesis.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_psi_A_u1_interaction_exchange_rule_family_closeout_result_review"
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


def build_toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_result_review(
    *,
    closeout_path: Path = CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = _read_json(closeout_path)
    review_criteria = _review_criteria(closeout)
    acceptance_criteria = {
        "consumes_expected_closeout": (
            closeout.get("schema_id") == CLOSEOUT_SCHEMA_ID
            and closeout.get("packet_id") == CLOSEOUT_PACKET_ID
            and closeout.get("outcome_id") == CLOSEOUT_OUTCOME
            and closeout.get("closeout_result") == CLOSEOUT_RESULT
            and closeout.get("selected_next_target") == CONSUMED_TARGET
            and closeout.get("accepted") is True
        ),
        "family_closed": (
            closeout.get("interaction_exchange_rule_family_closed") is True
            and closeout.get("bounded_current_source_exchange_admissibility_family_closed")
            is True
            and closeout.get("C_exchange_admissibility_rule_closed") is True
            and closeout.get("C_exchange_remains_admissibility_only") is True
        ),
        "required_route_preserved": (
            closeout.get("current_candidate") == CURRENT_CANDIDATE
            and closeout.get("current_conservation_result") == CURRENT_CONSERVATION_RESULT
            and closeout.get("sourced_gauge_route") == SOURCED_GAUGE_ROUTE
            and closeout.get("gauge_sector_exchange_identity")
            == GAUGE_SECTOR_EXCHANGE_IDENTITY
            and closeout.get("matter_sector_exchange_identity")
            == MATTER_SECTOR_EXCHANGE_IDENTITY
            and closeout.get("total_stress_energy_object") == TOTAL_STRESS_ENERGY_OBJECT
            and closeout.get("total_stress_energy_conservation_identity")
            == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
            and closeout.get("C_exchange_constraint_form") == C_EXCHANGE_CONSTRAINT_FORM
            and closeout.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "C_exchange_rule_admissibility_only": (
            closeout.get("C_exchange_rule_classification") == RULE_CLASSIFICATION
            and closeout.get("C_exchange_rule_epistemic_status") == RULE_EPISTEMIC_STATUS
            and closeout.get("C_exchange_remains_admissibility_only") is True
        ),
        "no_forbidden_claims": all(
            closeout.get(key) is False
            for key in _false_boundary_flags()
            if key in closeout
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            closeout.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and closeout.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and closeout.get("full_toeformal_aggregate_passed") is False
            and closeout.get("full_toeformal_aggregate_failed") is False
            and closeout.get("full_toeformal_aggregate_timed_out") is False
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_"
            "CLOSEOUT_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_"
            "RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "review_result": OUTCOME_ID if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "synthesis_outcome_hint": SYNTHESIS_OUTCOME_HINT,
        "closeout_schema_id": CLOSEOUT_SCHEMA_ID,
        "closeout_packet_id": CLOSEOUT_PACKET_ID,
        "closeout_outcome": CLOSEOUT_OUTCOME,
        "closeout_result": CLOSEOUT_RESULT,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
        "family_classification": FAMILY_CLASSIFICATION,
        "family_scope": FAMILY_SCOPE,
        "family_epistemic_status": FAMILY_EPISTEMIC_STATUS,
        "rule_family_id": RULE_FAMILY_ID,
        "rule_family_classification": RULE_FAMILY_CLASSIFICATION,
        "rule_family_epistemic_status": RULE_FAMILY_EPISTEMIC_STATUS,
        "route_family_chain": closeout.get("route_family_chain", []),
        "route_family_chain_count": len(closeout.get("route_family_chain", [])),
        "closed_route_roles": closeout.get("closed_route_roles", []),
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
        "closeout_result_review_prepared": accepted,
        "closeout_result_review_accepted": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": accepted,
        "closeout_accepted": accepted,
        "psi_A_interaction_family_closed": accepted,
        "interaction_exchange_rule_family_closed": accepted,
        "bounded_current_source_exchange_admissibility_family_closed": accepted,
        "current_source_exchange_total_conservation_route_preserved": accepted,
        "current_source_exchange_and_total_conservation_route_preserved": accepted,
        "C_exchange_admissibility_only_preserved": accepted,
        "C_exchange_remains_admissibility_only": accepted,
        "C_exchange_admissibility_rule_closed": accepted,
        "C_exchange_rule_family_closed": accepted,
        "master_action_ck_family_status_synthesis_authorized": accepted,
        "master_action_ck_family_status_synthesis_prepared": False,
        "ck_family_status_synthesis_prepared": False,
        "mathematical_statement": (
            "The closeout result review accepts the bounded psi-A U(1) "
            "interaction exchange family: "
            f"{CURRENT_CANDIDATE}; {CURRENT_CONSERVATION_RESULT}; "
            f"{SOURCED_GAUGE_ROUTE}; {GAUGE_SECTOR_EXCHANGE_IDENTITY}; "
            f"{MATTER_SECTOR_EXCHANGE_IDENTITY}; {TOTAL_STRESS_ENERGY_OBJECT}; "
            f"{TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY}; "
            f"{C_EXCHANGE_CONSTRAINT_FORM}; {C_EXCHANGE_ADMISSIBILITY_CONDITION}."
        ),
        "plain_meaning": (
            "The review accepts that matter creates a current, the current "
            "sources the gauge field, matter and gauge field exchange equal "
            "and opposite energy-momentum, the total system stays balanced, "
            "and C_exchange records that balance as an admissibility rule."
        ),
        "non_claim_boundary": (
            "This result review accepts only that the bounded psi-A U(1) "
            "interaction family is closed, that the current/source/exchange/"
            "total-conservation route is preserved, and that C_exchange remains "
            "admissibility-only. It records no C_k action embedding, no C_k "
            "action variation, no multiplier route, no penalty route, no direct "
            "dynamical-law claim, no full Maxwell closure, no EM-QFT closure, "
            "no QFT-GR closure, no quantized electromagnetism, no anomaly "
            "analysis, no Standard Model derivation, no Phase 2 authorization, "
            "no empirical validation, no seam closure, and no master-action "
            "promotion. The master action remains a working-form, noncanonical, "
            "non-promoted organizing surface. The full ToeFormal aggregate is "
            "kept as NOT_RUN."
        ),
        "critical_gate_fail_conditions": [
            "drop the closed psi-A interaction family",
            "drop the current/source/exchange/total-conservation route",
            "drop C_exchange admissibility-only status",
            "claim C_k action embedding",
            "execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "interpret C_exchange as a direct dynamical law",
            "claim full Maxwell closure",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "claim quantized electromagnetism",
            "perform anomaly analysis",
            "derive the Standard Model",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "prepare the master-action C_k family status synthesis inside this review",
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
            "ToeFormal.Derivation.ToeNativePsiAU1InteractionExchangeRuleFamilyCloseoutResultReview",
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
            "closeout_file": _ptr(closeout_path),
            "closeout_lean_file": _ptr(CLOSEOUT_LEAN_PACKET_PATH),
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
            "closeout result."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--closeout", type=Path, default=CLOSEOUT_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    closeout_path = (
        args.closeout if args.closeout.is_absolute() else REPO_ROOT / args.closeout
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_result_review(
        closeout_path=closeout_path,
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
