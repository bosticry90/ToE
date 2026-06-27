from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.master_action_ck_family_gap_review_after_phi_a_and_psi_a_report import (
    ALTERNATE_POST_REVIEW_BRANCH,
    C_BRIDGE_CLASSIFICATION,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CLASSIFICATION,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_SOURCE_CLASSIFICATION,
    C_TRANSPORT_CLASSIFICATION,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as GAP_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAP_REVIEW_RESULT,
    GAP_REVIEW_INSPECTION_QUESTIONS,
    LEAN_PACKET_PATH as GAP_REVIEW_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as GAP_REVIEW_OUTCOME,
    PACKET_ID as GAP_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RECOMMENDED_POST_REVIEW_BRANCH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as GAP_REVIEW_SCHEMA_ID,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = (
    "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_"
    "RESULT_REVIEW_20260626_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_"
    "ACCEPTS_RULE_FAMILY_GAPS_INDEXED_NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "master_action_ck_family_gap_review_after_phi_A_and_psi_A_result_review_"
    "accepts_rule_family_gaps_indexed_no_action_variation_or_master_action_promotion"
)

NEXT_TARGET = "select_next_master_action_surface_after_ck_family_gap_review"
NEXT_TARGET_KIND = "master_action_surface_selection_after_ck_family_gap_review"

RECOMMENDED_SELECTOR_CHOICE = "prepare_ck_family_theorem_linkage_obligation_index"
ALTERNATE_SELECTOR_CHOICES = [
    "return_to_QFT_GR_source_admissibility_lane",
    "prepare_ck_family_public_plain_language_status_packet",
    "select_next_interaction_surface_after_psi_A_u1",
]
SELECTOR_CHOICES = [RECOMMENDED_SELECTOR_CHOICE, *ALTERNATE_SELECTOR_CHOICES]

ACCEPTED_REVIEW_FINDINGS = [
    "GAP-1 through GAP-8 indexed",
    "all gaps remain open",
    "no gap is discharged",
    "no rule is promoted",
    "no C_k functionalization occurs",
    "no C_k variation occurs",
    "no seam closure occurs",
    "no master-action promotion occurs",
]

EXPECTED_GAP_LABELS = [
    "theorem-linkage gap",
    "assumption gap",
    "functionalization gap",
    "variation gap",
    "physical-meaning gap",
    "interaction-generalization gap",
    "seam-closure gap",
    "empirical-discriminator gap",
]

BLOCKED_CLAIMS = [
    "no C_k action embedding",
    "no C_k action variation",
    "no multiplier route",
    "no penalty route",
    "no direct dynamical-law claim",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no Standard Model derivation",
    "no Phase 2 authorization",
    "no empirical validation",
    "no seam closure",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_"
        "RESULT_REVIEW_20260626_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionCKFamilyGapReviewAfterPhiAAndPsiAResultReview.lean"
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
        "C_k_action_embedding_authorized": False,
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
        "functionalization_authorized": False,
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
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "pillar_completion_inferred": False,
        "theorem_linkage_completed": False,
        "assumption_discharge_completed": False,
        "gap_review_closes_any_gap": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "rule_promoted": False,
        "post_review_selector_executed": False,
        "theorem_linkage_obligation_index_prepared": False,
        "theorem_linkage_obligation_index_selected": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
    }


def _input_boundary_clear(gap_review: dict[str, Any]) -> bool:
    return all(
        gap_review.get(key) is False
        for key in _false_boundary_flags()
        if key in gap_review
    )


def _review_criteria(gap_review: dict[str, Any]) -> list[dict[str, Any]]:
    gap_rows = gap_review.get("gap_rows", [])
    return [
        {
            "row_id": "gap_review_consumed",
            "status": "accepted",
            "evidence": gap_review.get("gap_review_result"),
            "assessment": "The C_k family gap-review packet is consumed.",
        },
        {
            "row_id": "gap_1_through_gap_8_indexed",
            "status": "accepted",
            "evidence": [row.get("gap_id") for row in gap_rows],
            "assessment": "GAP-1 through GAP-8 are indexed.",
        },
        {
            "row_id": "all_gaps_remain_open",
            "status": "accepted",
            "evidence": [row.get("resolution_status") for row in gap_rows],
            "assessment": "Every indexed gap remains open_indexed_only.",
        },
        {
            "row_id": "no_gap_discharged",
            "status": "accepted",
            "evidence": {
                "open_gap_count": gap_review.get("open_gap_count"),
                "closed_gap_count": gap_review.get("closed_gap_count"),
            },
            "assessment": "The review accepts no gap discharge or closure.",
        },
        {
            "row_id": "no_rule_promoted",
            "status": "accepted",
            "evidence": "master_action_promoted=false",
            "assessment": "No C_k rule or master-action surface is promoted.",
        },
        {
            "row_id": "no_functionalization_or_variation",
            "status": "accepted",
            "evidence": [
                "functionalization_authorized=false",
                "C_k_action_variation_executed=false",
            ],
            "assessment": "No C_k functionalization or variation occurs.",
        },
        {
            "row_id": "no_seam_or_empirical_closure",
            "status": "accepted",
            "evidence": [
                "em_qft_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "gr_qm_closure_claimed=false",
                "empirical_validation_claimed=false",
            ],
            "assessment": "No seam closure or empirical validation is accepted.",
        },
        {
            "row_id": "post_review_selector_only",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The review selects only the next bounded selector.",
        },
        {
            "row_id": "recommended_theorem_linkage_choice_not_executed",
            "status": "accepted",
            "evidence": RECOMMENDED_SELECTOR_CHOICE,
            "assessment": (
                "The theorem-linkage obligation index is recommended for the selector "
                "but not prepared inside this review."
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
        "checkpoint_type": (
            "master_action_ck_family_gap_review_after_phi_A_and_psi_A_result_review"
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


def build_master_action_ck_family_gap_review_after_phi_a_and_psi_a_result_review(
    *,
    gap_review_path: Path = GAP_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    gap_review = _read_json(gap_review_path)
    gap_rows = gap_review.get("gap_rows", [])
    review_criteria = _review_criteria(gap_review)
    acceptance_criteria = {
        "consumes_expected_gap_review": (
            gap_review.get("schema_id") == GAP_REVIEW_SCHEMA_ID
            and gap_review.get("packet_id") == GAP_REVIEW_PACKET_ID
            and gap_review.get("outcome_id") == GAP_REVIEW_OUTCOME
            and gap_review.get("packet_result") == GAP_REVIEW_OUTCOME
            and gap_review.get("selected_next_target") == CONSUMED_TARGET
            and gap_review.get("accepted") is True
        ),
        "gap_1_through_gap_8_indexed": (
            [row.get("gap_id") for row in gap_rows]
            == [f"GAP-{index}" for index in range(1, 9)]
            and [row.get("gap_label") for row in gap_rows] == EXPECTED_GAP_LABELS
            and len(gap_rows) == 8
        ),
        "all_gaps_remain_open": (
            gap_review.get("gap_count") == 8
            and gap_review.get("open_gap_count") == 8
            and gap_review.get("closed_gap_count") == 0
            and all(row.get("resolution_status") == "open_indexed_only" for row in gap_rows)
            and gap_review.get("gap_review_closes_any_gap") is False
        ),
        "gap_index_flags_preserved": all(
            gap_review.get(key) is True
            for key in [
                "admissibility_to_functionalization_gaps_indexed",
                "rule_family_gaps_indexed",
                "theorem_linkage_gap_indexed",
                "assumption_gap_indexed",
                "functionalization_gap_indexed",
                "variation_gap_indexed",
                "physical_meaning_gap_indexed",
                "interaction_generalization_gap_indexed",
                "seam_closure_gap_indexed",
                "empirical_discriminator_gap_indexed",
            ]
        ),
        "no_gap_discharged_or_rule_promoted": (
            gap_review.get("theorem_linkage_completed") is False
            and gap_review.get("assumption_discharge_completed") is False
            and gap_review.get("functionalization_authorized") is False
            and gap_review.get("variation_authorized") is False
            and gap_review.get("seam_closure_authorized") is False
            and gap_review.get("master_action_promoted") is False
        ),
        "rule_architecture_context_preserved": (
            gap_review.get("C_source_classification") == C_SOURCE_CLASSIFICATION
            and gap_review.get("C_bridge_classification") == C_BRIDGE_CLASSIFICATION
            and gap_review.get("C_transport_classification") == C_TRANSPORT_CLASSIFICATION
            and gap_review.get("C_exchange_classification") == C_EXCHANGE_CLASSIFICATION
            and gap_review.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "no_forbidden_claims": _input_boundary_clear(gap_review),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            gap_review.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and gap_review.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and gap_review.get("full_toeformal_aggregate_passed") is False
            and gap_review.get("full_toeformal_aggregate_failed") is False
            and gap_review.get("full_toeformal_aggregate_timed_out") is False
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_MASTER_ACTION_CK_FAMILY_GAP_REVIEW_RESULT"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_"
            "RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "recommended_selector_choice": RECOMMENDED_SELECTOR_CHOICE,
        "alternate_selector_choices": ALTERNATE_SELECTOR_CHOICES,
        "selector_choices": SELECTOR_CHOICES,
        "selector_choices_count": len(SELECTOR_CHOICES),
        "selector_executed": False,
        "gap_review_schema_id": GAP_REVIEW_SCHEMA_ID,
        "gap_review_packet_id": GAP_REVIEW_PACKET_ID,
        "gap_review_outcome": GAP_REVIEW_OUTCOME,
        "gap_review_result": GAP_REVIEW_RESULT,
        "gap_review_inspection_questions": GAP_REVIEW_INSPECTION_QUESTIONS,
        "gap_review_inspection_question_count": len(GAP_REVIEW_INSPECTION_QUESTIONS),
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
        "review_executed": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": accepted,
        "gap_review_result_review_prepared": accepted,
        "gap_review_result_review_accepted": accepted,
        "gap_1_through_gap_8_indexed": accepted,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "no_rule_promoted": accepted,
        "no_C_k_functionalization_occurs": accepted,
        "no_C_k_variation_occurs": accepted,
        "no_seam_closure_occurs": accepted,
        "no_master_action_promotion_occurs": accepted,
        "gap_rows": gap_rows,
        "gap_count": gap_review.get("gap_count"),
        "open_gap_count": gap_review.get("open_gap_count"),
        "closed_gap_count": gap_review.get("closed_gap_count"),
        "gap_resolution_status": "all_open_indexed_only",
        "admissibility_to_functionalization_gaps_indexed": accepted,
        "rule_family_gaps_indexed": accepted,
        "theorem_linkage_gap_indexed": accepted,
        "assumption_gap_indexed": accepted,
        "functionalization_gap_indexed": accepted,
        "variation_gap_indexed": accepted,
        "physical_meaning_gap_indexed": accepted,
        "interaction_generalization_gap_indexed": accepted,
        "seam_closure_gap_indexed": accepted,
        "empirical_discriminator_gap_indexed": accepted,
        "all_C_k_families_admissibility_only": accepted,
        "all_summarized_rules_admissibility_only": accepted,
        "all_summarized_rules_not_action_embedded": accepted,
        "all_summarized_rules_not_varied": accepted,
        "all_summarized_rules_not_direct_dynamical_laws": accepted,
        "all_summarized_rules_not_empirical_claims": accepted,
        "post_review_selector_authorized": accepted,
        "post_review_selector_executed": False,
        "master_action_surface_selector_authorized": accepted,
        "master_action_surface_selector_executed": False,
        "master_action_surface_selected": False,
        "theorem_linkage_obligation_index_authorized_for_selector": accepted,
        "theorem_linkage_obligation_index_prepared": False,
        "theorem_linkage_obligation_index_selected": False,
        "recommended_post_review_branch": RECOMMENDED_POST_REVIEW_BRANCH,
        "alternate_post_review_branch": ALTERNATE_POST_REVIEW_BRANCH,
        "post_review_branch_selected": False,
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
            "The review accepts that the C_k families have open indexed gaps, "
            "and it authorizes only a bounded next selector for choosing a follow-on."
        ),
        "mathematical_statement": (
            "The result review accepts GAP-1 through GAP-8 as indexed and open. "
            "It preserves phi: C_source + C_bridge + C_transport; A: C_source + "
            "C_bridge + C_transport; and psi-A: "
            f"{CURRENT_CANDIDATE}; {CURRENT_CONSERVATION_RESULT}; "
            f"{SOURCED_GAUGE_ROUTE}; {GAUGE_SECTOR_EXCHANGE_IDENTITY}; "
            f"{MATTER_SECTOR_EXCHANGE_IDENTITY}; "
            f"{TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY}; "
            f"{C_EXCHANGE_CONSTRAINT_FORM}; {C_EXCHANGE_ADMISSIBILITY_CONDITION}. "
            "No indexed gap is discharged."
        ),
        "non_claim_boundary": (
            "This result review accepts only that GAP-1 through GAP-8 were indexed "
            "and remain open. It discharges no gap, promotes no rule, creates no "
            "C_k functionalization, executes no C_k variation, closes no seam, "
            "and promotes no master action. It records no C_k action embedding, "
            "no multiplier route, no penalty route, no direct dynamical-law claim, "
            "no full Maxwell closure, no EM-QFT closure, no QFT-GR closure, no "
            "GR-QM closure, no Standard Model derivation, no Phase 2 authorization, "
            "no empirical validation, and no master-action promotion. The master "
            "action remains a working-form, noncanonical, non-promoted organizing "
            "surface. The full ToeFormal aggregate is kept as NOT_RUN."
        ),
        "critical_gate_fail_conditions": [
            "drop any GAP-1 through GAP-8 indexed row",
            "claim any indexed gap is discharged",
            "claim any indexed gap is closed",
            "promote any C_k rule",
            "claim any C_k family is action embedded",
            "authorize or execute C_k action variation",
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
            "promote the master action",
            "prepare the theorem-linkage obligation index inside this review",
            "execute the post-review selector inside this review",
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
            "ToeFormal.Derivation.MasterActionCKFamilyGapReviewAfterPhiAAndPsiAResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "gap_review_file": _ptr(gap_review_path),
            "gap_review_lean_file": _ptr(GAP_REVIEW_LEAN_PACKET_PATH),
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
            "Review the master-action C_k family gap review after phi, A, and psi-A."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--gap-review", type=Path, default=GAP_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    gap_review_path = (
        args.gap_review
        if args.gap_review.is_absolute()
        else REPO_ROOT / args.gap_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_master_action_ck_family_gap_review_after_phi_a_and_psi_a_result_review(
        gap_review_path=gap_review_path,
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
