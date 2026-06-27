from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.master_action_ck_family_status_synthesis_after_phi_a_and_psi_a_report import (
    C_BRIDGE_CLASSIFICATION,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CLASSIFICATION,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_SOURCE_CLASSIFICATION,
    C_TRANSPORT_CLASSIFICATION,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as SYNTHESIS_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as SYNTHESIS_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as SYNTHESIS_OUTCOME,
    PACKET_ID as SYNTHESIS_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RULE_ARCHITECTURE_STATUS,
    SCHEMA_ID as SYNTHESIS_SCHEMA_ID,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = (
    "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_"
    "RESULT_REVIEW_20260626_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_"
    "RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_ACCEPTS_"
    "SOURCE_BRIDGE_TRANSPORT_AND_EXCHANGE_RULE_FAMILY_SYNTHESIS_"
    "NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "master_action_ck_family_status_synthesis_result_review_accepts_"
    "source_bridge_transport_and_exchange_rule_family_synthesis_"
    "no_action_variation_or_master_action_promotion"
)
NEXT_TARGET = "select_next_master_action_surface_after_ck_family_status_synthesis"
NEXT_TARGET_KIND = "master_action_surface_selection_after_ck_family_status_synthesis"
RECOMMENDED_SELECTOR_CHOICE = "prepare_master_action_ck_family_gap_review"
SELECTOR_CHOICES = [
    "return_to_QFT_GR_source_admissibility_lane",
    "prepare_ck_family_public_plain_language_status_packet",
    "select_next_interaction_surface_after_psi_A_u1",
    RECOMMENDED_SELECTOR_CHOICE,
]

ACCEPTED_REVIEW_FINDINGS = [
    "phi source-bridge-transport family synthesized",
    "A source-bridge-transport family synthesized",
    "psi-A current-source-exchange-total-conservation family synthesized",
    "C_exchange recognized as interaction exchange-balance admissibility rule",
    "all C_k families remain admissibility-only",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_"
        "RESULT_REVIEW_20260626_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionCKFamilyStatusSynthesisAfterPhiAAndPsiAResultReview.lean"
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
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "master_action_surface_selected": False,
        "master_action_surface_selector_executed": False,
        "ck_family_gap_review_prepared": False,
        "public_plain_language_status_packet_prepared": False,
        "next_interaction_surface_selected": False,
        "return_to_qft_gr_source_admissibility_lane_selected": False,
    }


def _input_boundary_clear(synthesis: dict[str, Any]) -> bool:
    return all(
        synthesis.get(key) is False
        for key in _false_boundary_flags()
        if key in synthesis
    )


def _review_criteria(synthesis: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "synthesis_consumed",
            "status": "accepted",
            "evidence": synthesis.get("packet_result"),
            "assessment": "The CK-family status synthesis packet is consumed.",
        },
        {
            "row_id": "phi_source_bridge_transport_family_synthesized",
            "status": "accepted",
            "evidence": "phi: C_source + C_bridge + C_transport",
            "assessment": "The phi isolated-field rule family is accepted as summarized.",
        },
        {
            "row_id": "A_source_bridge_transport_family_synthesized",
            "status": "accepted",
            "evidence": "A: C_source + C_bridge + C_transport",
            "assessment": "The A isolated-field rule family is accepted as summarized.",
        },
        {
            "row_id": "psi_A_interaction_family_synthesized",
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
                "The bounded psi-A current/source/exchange/total-conservation "
                "family is accepted as summarized."
            ),
        },
        {
            "row_id": "C_exchange_interaction_exchange_balance_admissibility",
            "status": "accepted",
            "evidence": C_EXCHANGE_CLASSIFICATION,
            "assessment": "C_exchange is accepted as interaction exchange-balance admissibility.",
        },
        {
            "row_id": "rule_architecture_classifications_preserved",
            "status": "accepted",
            "evidence": [
                C_SOURCE_CLASSIFICATION,
                C_BRIDGE_CLASSIFICATION,
                C_TRANSPORT_CLASSIFICATION,
                C_EXCHANGE_CLASSIFICATION,
            ],
            "assessment": "The four mature C_k classifications are preserved.",
        },
        {
            "row_id": "all_ck_families_admissibility_only",
            "status": "accepted",
            "evidence": "all_summarized_rules_admissibility_only=true",
            "assessment": "All summarized C_k families remain admissibility-only.",
        },
        {
            "row_id": "no_action_embedding_variation_or_promotion",
            "status": "accepted",
            "evidence": [
                "C_k_action_embedding_claimed=false",
                "C_k_action_variation_executed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No action embedding, C_k variation, or master-action promotion follows.",
        },
        {
            "row_id": "no_seam_closure_or_empirical_claim",
            "status": "accepted",
            "evidence": [
                "seam_closure_claim=false",
                "empirical_validation_claimed=false",
            ],
            "assessment": "No seam closure or empirical claim is accepted.",
        },
        {
            "row_id": "full_toeformal_aggregate_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full aggregate is preserved as NOT_RUN.",
        },
        {
            "row_id": "next_selector_target_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The review selects a bounded next-surface selector.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "master_action_ck_family_status_synthesis_after_phi_A_and_psi_A_"
            "result_review"
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


def build_master_action_ck_family_status_synthesis_result_review(
    *,
    synthesis_path: Path = SYNTHESIS_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    synthesis = _read_json(synthesis_path)
    review_criteria = _review_criteria(synthesis)
    acceptance_criteria = {
        "consumes_expected_synthesis": (
            synthesis.get("schema_id") == SYNTHESIS_SCHEMA_ID
            and synthesis.get("packet_id") == SYNTHESIS_PACKET_ID
            and synthesis.get("outcome_id") == SYNTHESIS_OUTCOME
            and synthesis.get("packet_result") == SYNTHESIS_OUTCOME
            and synthesis.get("selected_next_target") == CONSUMED_TARGET
            and synthesis.get("accepted") is True
        ),
        "phi_A_and_psi_A_families_synthesized": (
            synthesis.get("phi_source_bridge_transport_family_synthesized") is True
            and synthesis.get("A_source_bridge_transport_family_synthesized") is True
            and synthesis.get("psi_A_interaction_exchange_family_synthesized") is True
            and synthesis.get("current_source_exchange_and_total_conservation_family_synthesized")
            is True
        ),
        "C_exchange_classified_as_exchange_balance": (
            synthesis.get("C_exchange_classification") == C_EXCHANGE_CLASSIFICATION
            and synthesis.get("C_exchange_classified") is True
            and synthesis.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "all_ck_families_admissibility_only": (
            synthesis.get("all_summarized_rules_admissibility_only") is True
            and synthesis.get("all_summarized_rules_not_action_embedded") is True
            and synthesis.get("all_summarized_rules_not_varied") is True
            and synthesis.get("all_summarized_rules_not_direct_dynamical_laws") is True
            and synthesis.get("all_summarized_rules_not_empirical_claims") is True
        ),
        "rule_classifications_preserved": (
            synthesis.get("C_source_classification") == C_SOURCE_CLASSIFICATION
            and synthesis.get("C_bridge_classification") == C_BRIDGE_CLASSIFICATION
            and synthesis.get("C_transport_classification") == C_TRANSPORT_CLASSIFICATION
            and synthesis.get("C_exchange_classification") == C_EXCHANGE_CLASSIFICATION
            and synthesis.get("mature_rule_class_count") == 4
            and synthesis.get("family_count") == 3
            and synthesis.get("isolated_field_family_count") == 2
            and synthesis.get("interaction_family_count") == 1
        ),
        "no_forbidden_claims": _input_boundary_clear(synthesis),
        "full_toeformal_aggregate_recorded_not_run": (
            synthesis.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and synthesis.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and synthesis.get("full_toeformal_aggregate_passed") is False
            and synthesis.get("full_toeformal_aggregate_failed") is False
            and synthesis.get("full_toeformal_aggregate_timed_out") is False
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_RESULT"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_"
            "RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "recommended_selector_choice": RECOMMENDED_SELECTOR_CHOICE,
        "selector_choices": SELECTOR_CHOICES,
        "selector_choices_count": len(SELECTOR_CHOICES),
        "selector_executed": False,
        "synthesis_schema_id": SYNTHESIS_SCHEMA_ID,
        "synthesis_packet_id": SYNTHESIS_PACKET_ID,
        "synthesis_outcome": SYNTHESIS_OUTCOME,
        "rule_architecture_status": RULE_ARCHITECTURE_STATUS,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_findings_count": len(ACCEPTED_REVIEW_FINDINGS),
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
        "synthesis_result_review_prepared": accepted,
        "synthesis_result_review_accepted": accepted,
        "master_action_ck_family_status_synthesis_result_review_prepared": accepted,
        "master_action_ck_family_status_synthesis_result_review_accepted": accepted,
        "phi_source_bridge_transport_family_synthesized": accepted,
        "A_source_bridge_transport_family_synthesized": accepted,
        "psi_A_current_source_exchange_total_conservation_family_synthesized": accepted,
        "psi_A_interaction_exchange_family_synthesized": accepted,
        "C_exchange_recognized_as_interaction_exchange_balance_admissibility_rule": accepted,
        "all_C_k_families_admissibility_only": accepted,
        "all_summarized_rules_admissibility_only": accepted,
        "all_summarized_rules_not_action_embedded": accepted,
        "all_summarized_rules_not_varied": accepted,
        "all_summarized_rules_not_direct_dynamical_laws": accepted,
        "all_summarized_rules_not_empirical_claims": accepted,
        "master_action_surface_selector_authorized": accepted,
        "master_action_surface_selector_executed": False,
        "master_action_surface_selected": False,
        "ck_family_gap_review_prepared": False,
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
            "The review accepts that the framework now has admissibility rules "
            "for isolated phi and A fields plus one bounded psi-A interaction "
            "exchange family."
        ),
        "mathematical_statement": (
            "The review accepts phi: C_source + C_bridge + C_transport; "
            "A: C_source + C_bridge + C_transport; and psi-A: "
            f"{CURRENT_CANDIDATE}; {CURRENT_CONSERVATION_RESULT}; "
            f"{SOURCED_GAUGE_ROUTE}; {GAUGE_SECTOR_EXCHANGE_IDENTITY}; "
            f"{MATTER_SECTOR_EXCHANGE_IDENTITY}; "
            f"{TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY}; "
            f"{C_EXCHANGE_CONSTRAINT_FORM}; {C_EXCHANGE_ADMISSIBILITY_CONDITION}."
        ),
        "non_claim_boundary": (
            "This result review accepts only that the phi source-bridge-transport "
            "family, A source-bridge-transport family, and psi-A current-source-"
            "exchange-total-conservation family were synthesized, that C_exchange "
            "is recognized as an interaction exchange-balance admissibility rule, "
            "and that all C_k families remain admissibility-only. It records no "
            "C_k action embedding, no C_k action variation, no multiplier route, "
            "no penalty route, no direct dynamical-law claim, no full Maxwell "
            "closure, no EM-QFT closure, no QFT-GR closure, no GR-QM closure, no "
            "Standard Model derivation, no Phase 2 authorization, no empirical "
            "validation, no seam closure, and no master-action promotion. The "
            "master action remains a working-form, noncanonical, non-promoted "
            "organizing surface. The full ToeFormal aggregate is kept as NOT_RUN."
        ),
        "critical_gate_fail_conditions": [
            "drop phi source-bridge-transport synthesis",
            "drop A source-bridge-transport synthesis",
            "drop psi-A current/source/exchange/total-conservation synthesis",
            "drop C_exchange as interaction exchange-balance admissibility",
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
            "promote the master action",
            "execute the next selector inside this review",
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
            "ToeFormal.Derivation.MasterActionCKFamilyStatusSynthesisAfterPhiAAndPsiAResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "synthesis_file": _ptr(synthesis_path),
            "synthesis_lean_file": _ptr(SYNTHESIS_LEAN_PACKET_PATH),
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
            "Review the master-action C_k family status synthesis after phi, A, and psi-A."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--synthesis", type=Path, default=SYNTHESIS_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    synthesis_path = (
        args.synthesis if args.synthesis.is_absolute() else REPO_ROOT / args.synthesis
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_master_action_ck_family_status_synthesis_result_review(
        synthesis_path=synthesis_path,
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
