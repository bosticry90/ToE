from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_psi_a_u1_cexchange_admissibility_rule_closeout_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ADMISSIBILITY_ONLY_ROUTE_STATUS,
    BLOCKED_CLAIMS,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CLOSEOUT_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as CLOSEOUT_PATH,
    EXCHANGE_TERM_CANCELLATION,
    FOLLOW_ON_SYNTHESIS_OUTCOME,
    FOLLOW_ON_SYNTHESIS_TARGET,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MULTIPLIER_ACTION_FORM,
    MULTIPLIER_ACTION_ROUTE_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as CLOSEOUT_OUTCOME,
    PACKET_ID as CLOSEOUT_PACKET_ID,
    PENALTY_ACTION_FORM,
    PENALTY_ROUTE_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RULE_CLASSIFICATION,
    RULE_EPISTEMIC_STATUS,
    SCHEMA_ID as CLOSEOUT_SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_RESULT_REVIEW_"
    "20260626_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_RESULT_REVIEW_"
    "ACCEPTS_INTERACTION_EXCHANGE_BALANCE_RULE_NO_ACTION_VARIATION_OR_EM_QFT_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_cexchange_admissibility_rule_closeout_result_review_"
    "accepts_interaction_exchange_balance_rule_no_action_variation_or_em_qft_closure"
)
NEXT_TARGET = FOLLOW_ON_SYNTHESIS_TARGET
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_interaction_exchange_rule_family_synthesis_packet_preparation"
)

ACCEPTED_REVIEW_FINDINGS = [
    "C_exchange closeout accepted",
    "C_exchange remains admissibility-only",
    "C_exchange is based on accepted psi-A total-conservation route",
    "no functional embedding",
    "no multiplier/action route",
    "no penalty route",
    "no C_k variation",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_RESULT_REVIEW_"
    "20260626_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1CExchangeAdmissibilityRuleCloseoutResultReview.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _review_criteria(closeout: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "closeout_consumed",
            "status": "accepted",
            "evidence": closeout.get("closeout_result"),
            "assessment": "The accepted C_exchange admissibility-rule closeout is consumed.",
        },
        {
            "row_id": "interaction_exchange_balance_rule_accepted",
            "status": "accepted",
            "evidence": RULE_CLASSIFICATION,
            "assessment": "C_exchange is accepted only as an interaction exchange-balance rule.",
        },
        {
            "row_id": "admissibility_only_status_preserved",
            "status": "accepted",
            "evidence": RULE_EPISTEMIC_STATUS,
            "assessment": "The rule remains admissibility-only.",
        },
        {
            "row_id": "cexchange_candidate_preserved",
            "status": "accepted",
            "evidence": [
                C_EXCHANGE_CONSTRAINT_FORM,
                C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
                C_EXCHANGE_ADMISSIBILITY_CONDITION,
            ],
            "assessment": "The C_exchange residual and rule equation are preserved.",
        },
        {
            "row_id": "accepted_total_conservation_route_basis_preserved",
            "status": "accepted",
            "evidence": TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
            "assessment": "The accepted psi-A total-conservation route remains the basis.",
        },
        {
            "row_id": "exchange_halves_context_preserved",
            "status": "accepted",
            "evidence": [
                GAUGE_SECTOR_EXCHANGE_IDENTITY,
                MATTER_SECTOR_EXCHANGE_IDENTITY,
                EXCHANGE_TERM_CANCELLATION,
            ],
            "assessment": "The gauge and matter exchange halves remain context.",
        },
        {
            "row_id": "no_functional_embedding_multiplier_penalty_or_ck_variation",
            "status": "accepted",
            "evidence": [
                "functional_action_embedding_claimed=false",
                "multiplier_action_route_selected=false",
                "penalty_route_selected=false",
                "C_k_action_variation_executed=false",
            ],
            "assessment": "No functional embedding, multiplier/action, penalty, or C_k variation route is accepted.",
        },
        {
            "row_id": "closure_and_promotion_claims_blocked",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "EM-QFT, QFT-GR, empirical, Phase 2, and master-action promotion claims remain blocked.",
        },
        {
            "row_id": "synthesis_packet_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is the interaction exchange rule-family synthesis packet.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_psi_A_u1_cexchange_admissibility_rule_closeout_result_review"
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


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "functional_action_embedding_claimed": False,
        "functional_action_embedding_selected": False,
        "functional_action_embedding_constructed": False,
        "C_exchange_functional_embedding_claimed": False,
        "C_exchange_functional_embedding_selected": False,
        "C_exchange_functional_embedding_constructed": False,
        "multiplier_action_route_selected": False,
        "multiplier_action_route_constructed": False,
        "multiplier_field_selected": False,
        "penalty_route_selected": False,
        "penalty_route_constructed": False,
        "penalty_route_licensed": False,
        "penalty_functional_selected": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_constructed": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "candidate_varied": False,
        "direct_dynamical_law_interpretation_selected": False,
        "direct_force_law_claimed": False,
        "new_force_law_claimed": False,
        "full_maxwell_closure_claimed": False,
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
        "interaction_exchange_rule_family_synthesis_packet_prepared": False,
        "interaction_exchange_rule_family_synthesized": False,
    }


def build_toe_native_psi_a_u1_cexchange_admissibility_rule_closeout_result_review(
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
        "candidate_forms_preserved": (
            closeout.get("C_exchange_constraint_id") == C_EXCHANGE_CONSTRAINT_ID
            and closeout.get("C_exchange_constraint_form") == C_EXCHANGE_CONSTRAINT_FORM
            and closeout.get("C_exchange_total_stress_energy_form")
            == C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
            and closeout.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "accepted_route_basis_preserved": (
            closeout.get("based_on_accepted_total_stress_energy_conservation_route")
            is True
            and closeout.get("total_stress_energy_conservation_identity")
            == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "admissibility_only_rule_preserved": (
            closeout.get("rule_classification") == RULE_CLASSIFICATION
            and closeout.get("rule_epistemic_status") == RULE_EPISTEMIC_STATUS
            and closeout.get("admissibility_only_route_selected") is True
            and closeout.get("candidate_recorded_as_rule_only") is True
        ),
        "no_forbidden_routes_or_claims": all(
            closeout.get(key) is False for key in _false_boundary_flags()
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
            "ACTIVE_TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_"
            "RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "review_prepared": accepted,
        "review_accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSEOUT_RESULT_"
            "REVIEW_REQUIRES_REMEDIATION"
        ),
        "review_result": OUTCOME_ID if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_"
            "CLOSEOUT_RESULT_REVIEW"
        ),
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "closeout_schema_id": CLOSEOUT_SCHEMA_ID,
        "closeout_packet_id": CLOSEOUT_PACKET_ID,
        "closeout_outcome": CLOSEOUT_OUTCOME,
        "closeout_result": CLOSEOUT_RESULT,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "source_current": SOURCE_CURRENT,
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
        "C_exchange_plain_meaning": C_EXCHANGE_PLAIN_MEANING,
        "C_exchange_candidate_scope": C_EXCHANGE_CANDIDATE_SCOPE,
        "admissibility_only_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
        "rule_classification": RULE_CLASSIFICATION,
        "rule_epistemic_status": RULE_EPISTEMIC_STATUS,
        "multiplier_action_route_id": MULTIPLIER_ACTION_ROUTE_ID,
        "multiplier_action_form": MULTIPLIER_ACTION_FORM,
        "penalty_route_id": PENALTY_ROUTE_ID,
        "penalty_action_form": PENALTY_ACTION_FORM,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "closeout_result_review_prepared": accepted,
        "closeout_result_review_accepted": accepted,
        "C_exchange_closeout_accepted": accepted,
        "C_exchange_admissibility_rule_closeout_result_review_result": (
            OUTCOME_ID if accepted else "REVIEW_REQUIRES_REMEDIATION"
        ),
        "C_exchange_admissibility_rule_closed": accepted,
        "C_exchange_rule_closed_as_interaction_exchange_balance_rule": accepted,
        "interaction_exchange_balance_rule_closed": accepted,
        "admissibility_only_status_preserved": accepted,
        "based_on_accepted_total_stress_energy_conservation_route": accepted,
        "C_exchange_candidate_preserved": accepted,
        "T_total_preserved": accepted,
        "follow_on_synthesis_target": FOLLOW_ON_SYNTHESIS_TARGET,
        "follow_on_synthesis_outcome": FOLLOW_ON_SYNTHESIS_OUTCOME,
        "follow_on_synthesis_prepared": False,
        "mathematical_statement": (
            "The review accepts the C_exchange closeout as an "
            "interaction exchange-balance admissibility rule: "
            f"{C_EXCHANGE_CONSTRAINT_FORM}, with "
            f"{C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM} and "
            f"{C_EXCHANGE_ADMISSIBILITY_CONDITION}."
        ),
        "plain_meaning": (
            "The psi-A interaction exchange rule is accepted only as a rule "
            "for admissible total energy-momentum balance."
        ),
        "non_claim_boundary": (
            "This result review accepts the C_exchange closeout only. "
            "C_exchange remains admissibility-only and is based on the "
            "accepted psi-A total-conservation route. The review records no "
            "functional embedding, no multiplier/action route, no penalty "
            "route, no C_k variation, no direct dynamical-law interpretation, "
            "no full Maxwell closure, no EM-QFT closure, no QFT-GR closure, "
            "no quantized electromagnetism, no anomaly analysis, no Standard "
            "Model derivation, no Phase 2 authorization, no empirical "
            "validation, and no master-action promotion. The full ToeFormal "
            "aggregate is recorded as NOT_RUN for this review."
        ),
        "critical_gate_fail_conditions": [
            "drop the accepted C_exchange closeout",
            "functionalize C_exchange",
            "select a multiplier/action route",
            "license a penalty route",
            "execute C_k variation",
            "claim C_exchange as a new force law",
            "claim full Maxwell closure",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "claim empirical validation",
            "promote the master action",
            "prepare synthesis without preserving no-closure boundaries",
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
            "ToeFormal.Derivation.ToeNativePsiAU1CExchangeAdmissibilityRuleCloseoutResultReview",
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
            "closeout_lean_packet_file": _ptr(CLOSEOUT_LEAN_PACKET_PATH),
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
            "Review the ToE-native psi-A U(1) C_exchange admissibility-rule closeout."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--closeout", type=Path, default=CLOSEOUT_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    closeout_path = args.closeout if args.closeout.is_absolute() else REPO_ROOT / args.closeout
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_toe_native_psi_a_u1_cexchange_admissibility_rule_closeout_result_review(
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
