from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.master_action_ck_family_status_synthesis_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    C_BRIDGE_CLASSIFICATION,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CLASSIFICATION,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_SOURCE_CLASSIFICATION,
    C_TRANSPORT_CLASSIFICATION,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as REVIEW_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as REVIEW_OUTCOME,
    PACKET_ID as REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID as REVIEW_SCHEMA_ID,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS_20260626_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS_v0"
SELECTION_RESULT = (
    "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS_SELECTS_"
    "CK_FAMILY_GAP_REVIEW_NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "master_action_surface_selection_after_ck_family_status_synthesis_selects_"
    "ck_family_gap_review_no_action_variation_or_master_action_promotion"
)

NEXT_TARGET = "prepare_master_action_ck_family_gap_review_after_phi_A_and_psi_A"
NEXT_TARGET_KIND = "master_action_ck_family_gap_review_after_phi_A_and_psi_A_preparation"

SELECTED_MASTER_ACTION_SURFACE = "ck_family_gap_review"
SELECTED_SURFACE_LABEL = "C_k family gap review after phi, A, and psi-A"
SELECTED_SURFACE_STATUS = "selected_for_gap_review_preparation"
SELECTED_SURFACE_EXECUTION_STATUS = "not_prepared"
SELECTED_SURFACE_REASON = (
    "A gap review is selected before any new field or interaction so the "
    "project can identify which C_k rules remain theorem-linked, policy-level, "
    "assumption-supplied, or route-check-only before considering stronger "
    "action, variation, seam-closure, or empirical claims."
)

SELECTOR_CHOICES = [
    "return_to_QFT_GR_source_admissibility_lane",
    "prepare_ck_family_public_plain_language_status_packet",
    "select_next_interaction_surface_after_psi_A_u1",
    NEXT_TARGET,
]

GAP_REVIEW_INSPECTION_QUESTIONS = [
    "Are C_source, C_bridge, C_transport, and C_exchange theorem-linked?",
    "Which rules are still policy-level?",
    "Which assumptions are still supplied?",
    "Which rules are only route checks?",
    "What would be required for action embedding?",
    "What would be required for C_k variation?",
    "What would be required for seam closure?",
    "What would be required for empirical prediction?",
]

BLOCKED_CLAIMS = [
    "C_k action embedding",
    "C_k action variation",
    "multiplier route",
    "penalty route",
    "direct dynamical-law claim",
    "full Maxwell closure",
    "EM-QFT closure",
    "QFT-GR closure",
    "GR-QM closure",
    "Standard Model derivation",
    "Phase 2 authorization",
    "empirical validation",
    "seam closure",
    "master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS_20260626_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionSurfaceSelectionAfterCKFamilyStatusSynthesis.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "C_k_action_embedding_claimed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "ck_action_embedding_claimed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "multiplier_route_selected": False,
        "multiplier_action_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_claimed": False,
        "direct_dynamical_law_interpretation_selected": False,
        "dynamical_law_claimed": False,
        "functional_action_embedding_claimed": False,
        "C_exchange_functional_embedding_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "full_em_closure_claimed": False,
        "em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "standard_model_derivation_claimed": False,
        "phase2_authorized": False,
        "phase2_readiness_claim": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "pillar_completion_inferred": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "return_to_qft_gr_source_admissibility_lane_selected": False,
        "public_plain_language_status_packet_prepared": False,
        "next_interaction_surface_selected": False,
        "immediate_new_field_or_interaction_expansion_selected": False,
    }


def _input_boundary_clear(review: dict[str, Any]) -> bool:
    return all(
        review.get(key) is False
        for key in _false_boundary_flags()
        if key in review
    )


def _surface_options() -> list[dict[str, Any]]:
    return [
        {
            "surface_option_id": SELECTED_MASTER_ACTION_SURFACE,
            "surface_label": SELECTED_SURFACE_LABEL,
            "candidate_target": NEXT_TARGET,
            "status": SELECTED_SURFACE_STATUS,
            "execution_status": SELECTED_SURFACE_EXECUTION_STATUS,
            "selection_reason": SELECTED_SURFACE_REASON,
            "gap_review_preparation_authorized": True,
            "gap_review_prepared": False,
            "new_field_or_interaction_expansion_selected": False,
            "C_k_action_embedding_selected": False,
            "C_k_variation_selected": False,
            "master_action_promotion_selected": False,
        },
        {
            "surface_option_id": "return_to_QFT_GR_source_admissibility_lane",
            "status": "deferred_not_rejected",
            "execution_status": "not_executed",
            "selection_reason": (
                "Deferred until the new C_k architecture result is gap-reviewed "
                "so the QFT-GR return can cite a clearer rule-status boundary."
            ),
        },
        {
            "surface_option_id": "prepare_ck_family_public_plain_language_status_packet",
            "status": "deferred_not_rejected",
            "execution_status": "not_executed",
            "selection_reason": (
                "Deferred because a scientific gap review should precede any "
                "public-facing compression of the C_k architecture status."
            ),
        },
        {
            "surface_option_id": "select_next_interaction_surface_after_psi_A_u1",
            "status": "deferred_not_rejected",
            "execution_status": "not_executed",
            "selection_reason": (
                "Deferred to avoid expanding the interaction catalog before "
                "checking what the first interaction rule family can and cannot "
                "support."
            ),
        },
    ]


def _selection_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_consumes_ck_family_status_selector_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": (
                "The selector consumes the active target selected by the "
                "C_k-family status synthesis result review."
            ),
        },
        {
            "row_id": "ck_family_status_review_accepted",
            "status": "accepted",
            "evidence": review.get("review_result"),
            "assessment": "The prior CK-family status synthesis review is accepted.",
        },
        {
            "row_id": "mature_rule_architecture_available_for_gap_review",
            "status": "accepted",
            "evidence": [
                C_SOURCE_CLASSIFICATION,
                C_BRIDGE_CLASSIFICATION,
                C_TRANSPORT_CLASSIFICATION,
                C_EXCHANGE_CLASSIFICATION,
            ],
            "assessment": (
                "The mature C_source, C_bridge, C_transport, and C_exchange "
                "classifications are available as the object of the gap review."
            ),
        },
        {
            "row_id": "psi_A_interaction_family_not_reopened",
            "status": "accepted",
            "evidence": [
                CURRENT_CANDIDATE,
                CURRENT_CONSERVATION_RESULT,
                SOURCED_GAUGE_ROUTE,
                GAUGE_SECTOR_EXCHANGE_IDENTITY,
                MATTER_SECTOR_EXCHANGE_IDENTITY,
                TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
                C_EXCHANGE_ADMISSIBILITY_CONDITION,
            ],
            "assessment": (
                "The psi-A interaction family is carried as context, not "
                "reopened for new derivation or closure."
            ),
        },
        {
            "row_id": "gap_review_selected_before_new_surface_expansion",
            "status": "accepted",
            "evidence": SELECTED_MASTER_ACTION_SURFACE,
            "assessment": (
                "The selector chooses a C_k family gap review instead of a new "
                "field or interaction expansion."
            ),
        },
        {
            "row_id": "gap_review_questions_enumerated",
            "status": "accepted",
            "evidence": GAP_REVIEW_INSPECTION_QUESTIONS,
            "assessment": "The follow-on gap review inspection questions are enumerated.",
        },
        {
            "row_id": "gap_review_preparation_only_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "Only preparation of the gap review is authorized; the review "
                "itself is not executed in this selector."
            ),
        },
        {
            "row_id": "no_action_variation_seam_empirical_or_promotion_claim",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": (
                "The selector preserves the no-action, no-variation, no-seam, "
                "no-empirical, and no-promotion boundary."
            ),
        },
        {
            "row_id": "full_toeformal_aggregate_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full aggregate is preserved as NOT_RUN.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "master_action_surface_selection_after_ck_family_status_synthesis",
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


def build_master_action_surface_selection_after_ck_family_status_synthesis(
    *,
    review_path: Path = REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    surface_options = _surface_options()
    selection_criteria = _selection_criteria(review)
    acceptance_criteria = {
        "consumes_expected_selector_target": (
            review.get("schema_id") == REVIEW_SCHEMA_ID
            and review.get("packet_id") == REVIEW_PACKET_ID
            and review.get("outcome_id") == REVIEW_OUTCOME
            and review.get("review_result") == REVIEW_RESULT
            and review.get("packet_result") == REVIEW_OUTCOME
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "ck_status_review_preserved_as_admissibility_only": (
            review.get("all_C_k_families_admissibility_only") is True
            and review.get("all_summarized_rules_not_action_embedded") is True
            and review.get("all_summarized_rules_not_varied") is True
            and review.get("all_summarized_rules_not_direct_dynamical_laws") is True
            and review.get("all_summarized_rules_not_empirical_claims") is True
        ),
        "rule_classifications_available": (
            review.get("C_source_classification") == C_SOURCE_CLASSIFICATION
            and review.get("C_bridge_classification") == C_BRIDGE_CLASSIFICATION
            and review.get("C_transport_classification") == C_TRANSPORT_CLASSIFICATION
            and review.get("C_exchange_classification") == C_EXCHANGE_CLASSIFICATION
        ),
        "gap_review_questions_enumerated": len(GAP_REVIEW_INSPECTION_QUESTIONS) == 8,
        "blocked_claims_enumerated": len(BLOCKED_CLAIMS) == 14,
        "exactly_one_surface_selected": (
            sum(1 for row in surface_options if row["status"] == SELECTED_SURFACE_STATUS)
            == 1
        ),
        "no_input_forbidden_claims": _input_boundary_clear(review),
        "selection_criteria_all_accepted": all(
            row["status"] == "accepted" for row in selection_criteria
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            review.get("aggregate_lean_validation_status_for_review")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and review.get("full_toeformal_aggregate_status_for_review")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and review.get("full_toeformal_aggregate_passed") is False
            and review.get("full_toeformal_aggregate_failed") is False
            and review.get("full_toeformal_aggregate_timed_out") is False
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS_REQUIRES_REMEDIATION",
        "selection_result": OUTCOME_ID if accepted else "SELECTION_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID if accepted else "SELECTION_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "review_schema_id": REVIEW_SCHEMA_ID,
        "review_packet_id": REVIEW_PACKET_ID,
        "review_outcome": REVIEW_OUTCOME,
        "review_result": REVIEW_RESULT,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "selected_master_action_surface": SELECTED_MASTER_ACTION_SURFACE,
        "selected_surface_label": SELECTED_SURFACE_LABEL,
        "selected_surface_status": SELECTED_SURFACE_STATUS,
        "selected_surface_execution_status": SELECTED_SURFACE_EXECUTION_STATUS,
        "selected_surface_reason": SELECTED_SURFACE_REASON,
        "surface_options": surface_options,
        "surface_option_count": len(surface_options),
        "surface_options_selected_count": sum(
            1 for row in surface_options if row["status"] == SELECTED_SURFACE_STATUS
        ),
        "surface_options_deferred_count": sum(
            1 for row in surface_options if row["status"].startswith("deferred")
        ),
        "selector_choices": SELECTOR_CHOICES,
        "selector_choices_count": len(SELECTOR_CHOICES),
        "gap_review_inspection_questions": GAP_REVIEW_INSPECTION_QUESTIONS,
        "gap_review_inspection_question_count": len(GAP_REVIEW_INSPECTION_QUESTIONS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "selection_criteria": selection_criteria,
        "selection_criteria_count": len(selection_criteria),
        "selection_criteria_accepted_count": sum(
            1 for row in selection_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "selector_target_prepared": accepted,
        "selector_target_accepted": accepted,
        "selection_executed": accepted,
        "master_action_surface_selector_executed": accepted,
        "master_action_surface_selection_executed": accepted,
        "next_master_action_surface_selected": accepted,
        "master_action_surface_selected": accepted,
        "ck_family_gap_review_selected": accepted,
        "ck_family_gap_review_preparation_authorized": accepted,
        "ck_family_gap_review_prepared": False,
        "gap_review_prepared": False,
        "gap_review_executed": False,
        "gap_review_target": selected_next_target,
        "gap_review_target_kind": NEXT_TARGET_KIND,
        "new_physics_created": False,
        "new_field_or_interaction_expansion_selected": False,
        "immediate_new_field_or_interaction_expansion_selected": False,
        "return_to_qft_gr_source_admissibility_lane_selected": False,
        "public_plain_language_status_packet_prepared": False,
        "next_interaction_surface_selected": False,
        "rule_architecture_status_review_consumed": accepted,
        "ck_family_status_synthesis_result_review_consumed": accepted,
        "all_C_k_families_admissibility_only": accepted,
        "all_summarized_rules_admissibility_only": accepted,
        "all_summarized_rules_not_action_embedded": accepted,
        "all_summarized_rules_not_varied": accepted,
        "all_summarized_rules_not_direct_dynamical_laws": accepted,
        "all_summarized_rules_not_empirical_claims": accepted,
        "C_source_classification": C_SOURCE_CLASSIFICATION,
        "C_bridge_classification": C_BRIDGE_CLASSIFICATION,
        "C_transport_classification": C_TRANSPORT_CLASSIFICATION,
        "C_exchange_classification": C_EXCHANGE_CLASSIFICATION,
        "current_candidate": CURRENT_CANDIDATE,
        "current_conservation_result": CURRENT_CONSERVATION_RESULT,
        "sourced_gauge_route": SOURCED_GAUGE_ROUTE,
        "gauge_sector_exchange_identity": GAUGE_SECTOR_EXCHANGE_IDENTITY,
        "matter_sector_exchange_identity": MATTER_SECTOR_EXCHANGE_IDENTITY,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_constraint_form": C_EXCHANGE_CONSTRAINT_FORM,
        "C_exchange_admissibility_condition": C_EXCHANGE_ADMISSIBILITY_CONDITION,
        "plain_meaning": (
            "The selector chooses a C_k family gap review before expanding to "
            "another field or interaction."
        ),
        "mathematical_statement": (
            "The selector carries phi: C_source + C_bridge + C_transport; "
            "A: C_source + C_bridge + C_transport; and psi-A: "
            f"{CURRENT_CANDIDATE}; {CURRENT_CONSERVATION_RESULT}; "
            f"{SOURCED_GAUGE_ROUTE}; {GAUGE_SECTOR_EXCHANGE_IDENTITY}; "
            f"{MATTER_SECTOR_EXCHANGE_IDENTITY}; "
            f"{TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY}; "
            f"{C_EXCHANGE_CONSTRAINT_FORM}; {C_EXCHANGE_ADMISSIBILITY_CONDITION} "
            "as context for a gap review only."
        ),
        "non_claim_boundary": (
            "This selector chooses a C_k family gap review after the phi, A, "
            "and psi-A C_k status synthesis. It creates no new physics and does "
            "not expand immediately to another field or interaction. It asks "
            "what remains theorem-linked, policy-level, assumption-supplied, "
            "or route-check-only before any stronger claim. It records no C_k "
            "action embedding, no C_k action variation, no multiplier route, "
            "no penalty route, no direct dynamical-law claim, no full Maxwell "
            "closure, no EM-QFT closure, no QFT-GR closure, no GR-QM closure, "
            "no Standard Model derivation, no Phase 2 authorization, no "
            "empirical validation, no seam closure, and no master-action "
            "promotion. The master action remains a working-form, noncanonical, "
            "non-promoted organizing surface. The full ToeFormal aggregate is "
            "kept as NOT_RUN."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume the CK-family status synthesis selector target",
            "drop phi/A/psi-A C_k architecture context",
            "select a new field or interaction expansion instead of the gap review",
            "prepare or execute the gap review inside the selector",
            "claim any C_k family is action embedded",
            "execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "claim a direct dynamical-law interpretation",
            "claim full Maxwell closure",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "claim GR-QM closure",
            "derive the Standard Model",
            "authorize Phase 2",
            "claim empirical validation",
            "claim seam closure",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.MasterActionSurfaceSelectionAfterCKFamilyStatusSynthesis",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "review_file": _ptr(review_path),
            "review_lean_file": _ptr(REVIEW_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }
    payload.update(_false_boundary_flags())
    return payload


def write_selection(selection: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(selection, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Select the next master-action surface after the CK-family status synthesis."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--review", type=Path, default=REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = args.review if args.review.is_absolute() else REPO_ROOT / args.review
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_master_action_surface_selection_after_ck_family_status_synthesis(
        review_path=review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_selection(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "selection_result": payload["selection_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
