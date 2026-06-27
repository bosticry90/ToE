from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.master_action_surface_selection_after_ck_family_status_synthesis_report import (
    C_BRIDGE_CLASSIFICATION,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CLASSIFICATION,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_SOURCE_CLASSIFICATION,
    C_TRANSPORT_CLASSIFICATION,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as SELECTOR_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAP_REVIEW_INSPECTION_QUESTIONS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as SELECTOR_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as SELECTOR_OUTCOME,
    PACKET_ID as SELECTOR_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as SELECTOR_SCHEMA_ID,
    SELECTED_MASTER_ACTION_SURFACE,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_20260626_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_v0"
GAP_REVIEW_RESULT = (
    "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_PREPARED_"
    "RULE_FAMILY_GAPS_INDEXED_NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = GAP_REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "master_action_ck_family_gap_review_after_phi_A_and_psi_A_prepared_"
    "rule_family_gaps_indexed_no_action_variation_or_master_action_promotion"
)

NEXT_TARGET = "review_master_action_ck_family_gap_review_after_phi_A_and_psi_A_result"
NEXT_TARGET_KIND = "master_action_ck_family_gap_review_after_phi_A_and_psi_A_result_review"

RECOMMENDED_POST_REVIEW_BRANCH = "prepare_ck_family_theorem_linkage_obligation_index"
ALTERNATE_POST_REVIEW_BRANCH = "return_to_QFT_GR_source_admissibility_lane"
POST_REVIEW_BRANCHES = [
    RECOMMENDED_POST_REVIEW_BRANCH,
    ALTERNATE_POST_REVIEW_BRANCH,
    "select_next_master_action_surface_after_ck_family_gap_review",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_20260626_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionCKFamilyGapReviewAfterPhiAAndPsiA.lean"
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
        "gap_review_closes_any_gap": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
    }


def _input_boundary_clear(selector: dict[str, Any]) -> bool:
    forbidden_keys = [
        "C_k_action_embedding_claimed",
        "C_k_action_embedding_selected",
        "C_k_action_variation_executed",
        "C_k_action_variation_authorized",
        "multiplier_route_selected",
        "multiplier_action_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_claimed",
        "direct_dynamical_law_interpretation_selected",
        "full_maxwell_closure_claimed",
        "full_Maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "standard_model_derivation_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
        "master_action_promotion",
    ]
    return all(selector.get(key) is False for key in forbidden_keys if key in selector)


def _gap_rows() -> list[dict[str, Any]]:
    return [
        {
            "gap_id": "GAP-1",
            "gap_label": "theorem-linkage gap",
            "inspection_question": (
                "Which C_k rules are theorem-backed versus policy-backed?"
            ),
            "current_status": (
                "The architecture has accepted route records and admissibility "
                "rule closeouts, but no unified theorem-linkage index proving "
                "which C_k rules follow from established premises."
            ),
            "required_before_strengthening": (
                "A per-rule theorem-linkage obligation index with proof objects, "
                "dependency assumptions, and failure conditions."
            ),
            "resolution_status": "open_indexed_only",
        },
        {
            "gap_id": "GAP-2",
            "gap_label": "assumption gap",
            "inspection_question": "Which rules still depend on supplied assumptions?",
            "current_status": (
                "The phi, A, and psi-A routes still depend on selected domains, "
                "sign conventions, stress-energy policies, boundary behavior, "
                "and route-specific assumptions."
            ),
            "required_before_strengthening": (
                "An assumption ledger mapping each C_k rule to supplied, reduced, "
                "proved, or blocked assumptions."
            ),
            "resolution_status": "open_indexed_only",
        },
        {
            "gap_id": "GAP-3",
            "gap_label": "functionalization gap",
            "inspection_question": (
                "What would be required to put C_k into the action safely?"
            ),
            "current_status": (
                "No safe action embedding exists for C_k rules; multiplier and "
                "penalty routes remain blocked or unlicensed."
            ),
            "required_before_strengthening": (
                "A non-circular functionalization criterion showing how C_k "
                "terms could enter an action without changing their meaning or "
                "creating fake dynamics."
            ),
            "resolution_status": "open_indexed_only",
        },
        {
            "gap_id": "GAP-4",
            "gap_label": "variation gap",
            "inspection_question": (
                "What would be required to vary C_k without circularity or fake dynamics?"
            ),
            "current_status": (
                "C_k rules are not varied and are not treated as Euler-Lagrange "
                "equations or dynamical laws."
            ),
            "required_before_strengthening": (
                "A variation-safety theorem distinguishing admissibility checks "
                "from independent dynamics, including circularity controls."
            ),
            "resolution_status": "open_indexed_only",
        },
        {
            "gap_id": "GAP-5",
            "gap_label": "physical-meaning gap",
            "inspection_question": (
                "Which C_k rules are only route checks, not laws of nature?"
            ),
            "current_status": (
                "C_source, C_bridge, C_transport, and C_exchange are currently "
                "admissibility checks over routes and exchanges, not standalone "
                "laws of nature."
            ),
            "required_before_strengthening": (
                "A physical-meaning classifier separating route admissibility, "
                "derivation stability, exchange balance, and genuine dynamics."
            ),
            "resolution_status": "open_indexed_only",
        },
        {
            "gap_id": "GAP-6",
            "gap_label": "interaction-generalization gap",
            "inspection_question": "Does C_exchange generalize beyond psi-A U1?",
            "current_status": (
                "C_exchange is closed only for the bounded psi-A U(1) "
                "current/source/exchange/total-conservation family."
            ),
            "required_before_strengthening": (
                "A generalization test across other interactions, non-Abelian "
                "cases, quantized sectors, and anomaly-sensitive routes."
            ),
            "resolution_status": "open_indexed_only",
        },
        {
            "gap_id": "GAP-7",
            "gap_label": "seam-closure gap",
            "inspection_question": (
                "What is still missing before any C_k rule can close EM-QFT, "
                "QFT-GR, or GR-QM?"
            ),
            "current_status": (
                "No C_k rule currently closes EM-QFT, QFT-GR, GR-QM, full "
                "Maxwell, or Standard Model seams."
            ),
            "required_before_strengthening": (
                "Seam-specific closure criteria tying theorem linkage, "
                "assumptions, functionalization safety, and empirical content "
                "to each target seam."
            ),
            "resolution_status": "open_indexed_only",
        },
        {
            "gap_id": "GAP-8",
            "gap_label": "empirical-discriminator gap",
            "inspection_question": (
                "What would make C_k produce a testable difference?"
            ),
            "current_status": (
                "The C_k architecture currently organizes admissibility; it does "
                "not yet produce a distinct empirical prediction."
            ),
            "required_before_strengthening": (
                "A discriminator map showing where C_k rules exclude, rank, or "
                "modify candidate models in a way that yields testable differences."
            ),
            "resolution_status": "open_indexed_only",
        },
    ]


def _gap_review_criteria(selector: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_consumed",
            "status": "accepted",
            "evidence": selector.get("selection_result"),
            "assessment": "The post-synthesis surface selector is consumed.",
        },
        {
            "row_id": "all_eight_gaps_indexed",
            "status": "accepted",
            "evidence": [row["gap_id"] for row in _gap_rows()],
            "assessment": "GAP-1 through GAP-8 are indexed.",
        },
        {
            "row_id": "admissibility_to_functionalization_boundary_recorded",
            "status": "accepted",
            "evidence": (
                "C_k as admissibility-only rulebook versus C_k as "
                "action-embedded, varied, theorem-linked, physically predictive "
                "structure"
            ),
            "assessment": "The strengthening boundary is recorded without crossing it.",
        },
        {
            "row_id": "phi_A_psi_A_rule_context_preserved",
            "status": "accepted",
            "evidence": [
                C_SOURCE_CLASSIFICATION,
                C_BRIDGE_CLASSIFICATION,
                C_TRANSPORT_CLASSIFICATION,
                C_EXCHANGE_CLASSIFICATION,
                C_EXCHANGE_ADMISSIBILITY_CONDITION,
            ],
            "assessment": "The current mature C_k architecture is preserved as context.",
        },
        {
            "row_id": "no_action_variation_or_promotion",
            "status": "accepted",
            "evidence": [
                "C_k_action_embedding_claimed=false",
                "C_k_action_variation_executed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No action embedding, C_k variation, or promotion follows.",
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
            "row_id": "full_toeformal_aggregate_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full aggregate is preserved as NOT_RUN.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "master_action_ck_family_gap_review_after_phi_A_and_psi_A",
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


def build_master_action_ck_family_gap_review_after_phi_a_and_psi_a(
    *,
    selector_path: Path = SELECTOR_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector = _read_json(selector_path)
    gap_rows = _gap_rows()
    gap_review_criteria = _gap_review_criteria(selector)
    acceptance_criteria = {
        "consumes_expected_gap_review_target": (
            selector.get("schema_id") == SELECTOR_SCHEMA_ID
            and selector.get("packet_id") == SELECTOR_PACKET_ID
            and selector.get("outcome_id") == SELECTOR_OUTCOME
            and selector.get("packet_result") == SELECTOR_OUTCOME
            and selector.get("selected_next_target") == CONSUMED_TARGET
            and selector.get("accepted") is True
        ),
        "selector_chose_gap_review": (
            selector.get("selected_master_action_surface") == SELECTED_MASTER_ACTION_SURFACE
            and selector.get("ck_family_gap_review_selected") is True
            and selector.get("ck_family_gap_review_preparation_authorized") is True
            and selector.get("ck_family_gap_review_prepared") is False
        ),
        "gap_rows_indexed": (
            [row["gap_id"] for row in gap_rows]
            == [f"GAP-{index}" for index in range(1, 9)]
        ),
        "inspection_questions_preserved": (
            len(GAP_REVIEW_INSPECTION_QUESTIONS) == 8
            and len(gap_rows) == 8
        ),
        "rule_architecture_context_preserved": (
            selector.get("C_source_classification") == C_SOURCE_CLASSIFICATION
            and selector.get("C_bridge_classification") == C_BRIDGE_CLASSIFICATION
            and selector.get("C_transport_classification") == C_TRANSPORT_CLASSIFICATION
            and selector.get("C_exchange_classification") == C_EXCHANGE_CLASSIFICATION
            and selector.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "no_input_forbidden_claims": _input_boundary_clear(selector),
        "gap_review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in gap_review_criteria
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            selector.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and selector.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and selector.get("full_toeformal_aggregate_passed") is False
            and selector.get("full_toeformal_aggregate_failed") is False
            and selector.get("full_toeformal_aggregate_timed_out") is False
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_REQUIRES_REMEDIATION",
        "gap_review_result": OUTCOME_ID if accepted else "GAP_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID if accepted else "GAP_REVIEW_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selector_schema_id": SELECTOR_SCHEMA_ID,
        "selector_packet_id": SELECTOR_PACKET_ID,
        "selector_outcome": SELECTOR_OUTCOME,
        "selector_selected_surface": SELECTED_MASTER_ACTION_SURFACE,
        "gap_review_prepared": accepted,
        "gap_review_accepted": accepted,
        "gap_review_executed": accepted,
        "gap_review_scope": "admissibility_to_functionalization_gap_index_only",
        "gap_review_closes_any_gap": False,
        "gap_rows": gap_rows,
        "gap_count": len(gap_rows),
        "open_gap_count": len(gap_rows),
        "closed_gap_count": 0,
        "gap_review_inspection_questions": GAP_REVIEW_INSPECTION_QUESTIONS,
        "gap_review_inspection_question_count": len(GAP_REVIEW_INSPECTION_QUESTIONS),
        "gap_review_criteria": gap_review_criteria,
        "gap_review_criteria_count": len(gap_review_criteria),
        "gap_review_criteria_accepted_count": sum(
            1 for row in gap_review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "admissibility_only_rulebook_status": "current_status",
        "stronger_physics_status": "not_authorized",
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
        "theorem_linkage_completed": False,
        "assumption_discharge_completed": False,
        "functionalization_authorized": False,
        "variation_authorized": False,
        "seam_closure_authorized": False,
        "empirical_prediction_claimed": False,
        "post_review_branches": POST_REVIEW_BRANCHES,
        "recommended_post_review_branch": RECOMMENDED_POST_REVIEW_BRANCH,
        "alternate_post_review_branch": ALTERNATE_POST_REVIEW_BRANCH,
        "post_review_branch_selected": False,
        "result_review_prepared": False,
        "result_review_accepted": False,
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
            "The framework has a useful C_k rule pattern, but the gaps before "
            "stronger physics claims are still open and explicitly indexed."
        ),
        "mathematical_statement": (
            "The gap review preserves phi: C_source + C_bridge + C_transport; "
            "A: C_source + C_bridge + C_transport; and psi-A: "
            f"{CURRENT_CANDIDATE}; {CURRENT_CONSERVATION_RESULT}; "
            f"{SOURCED_GAUGE_ROUTE}; {GAUGE_SECTOR_EXCHANGE_IDENTITY}; "
            f"{MATTER_SECTOR_EXCHANGE_IDENTITY}; "
            f"{TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY}; "
            f"{C_EXCHANGE_CONSTRAINT_FORM}; {C_EXCHANGE_ADMISSIBILITY_CONDITION}. "
            "It indexes GAP-1 through GAP-8 without closing them."
        ),
        "non_claim_boundary": (
            "This packet is a C_k family gap review only. It indexes the gap "
            "between C_k as an admissibility-only rulebook and C_k as an "
            "action-embedded, varied, theorem-linked, physically predictive "
            "structure. The stronger structure is not authorized. It records "
            "no C_k action embedding, no C_k action variation, no multiplier "
            "route, no penalty route, no direct dynamical-law claim, no full "
            "Maxwell closure, no EM-QFT closure, no QFT-GR closure, no GR-QM "
            "closure, no Standard Model derivation, no Phase 2 authorization, "
            "no empirical prediction or validation, no seam closure, and no "
            "master-action promotion. The master action remains a working-form, "
            "noncanonical, non-promoted organizing surface. The full ToeFormal "
            "aggregate is kept as NOT_RUN."
        ),
        "critical_gate_fail_conditions": [
            "fail to index GAP-1 through GAP-8",
            "claim any indexed gap is closed",
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
            "claim empirical prediction or validation",
            "claim seam closure",
            "promote the master action",
            "select the post-review branch before result review",
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
            "ToeFormal.Derivation.MasterActionCKFamilyGapReviewAfterPhiAAndPsiA",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "selector_file": _ptr(selector_path),
            "selector_lean_file": _ptr(SELECTOR_LEAN_PACKET_PATH),
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


def write_gap_review(gap_review: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(gap_review, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the master-action C_k family gap review after phi, A, and psi-A."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--selector", type=Path, default=SELECTOR_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    selector_path = (
        args.selector if args.selector.is_absolute() else REPO_ROOT / args.selector
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_master_action_ck_family_gap_review_after_phi_a_and_psi_a(
        selector_path=selector_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_gap_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "gap_count": payload["gap_count"],
                "gap_review_result": payload["gap_review_result"],
                "out": _ptr(path),
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
