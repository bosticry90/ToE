from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_ck_source_bridge_transport_rule_family_closeout_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM as PHI_BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    DEFAULT_OUT as PHI_CLOSEOUT_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_VALIDATION_POLICY_ID,
    OUTCOME_ID as PHI_CLOSEOUT_OUTCOME,
    PACKET_ID as PHI_CLOSEOUT_PACKET_ID,
    SCHEMA_ID as PHI_CLOSEOUT_SCHEMA_ID,
    SOURCE_RULE_DISPLAY_FORM as PHI_SOURCE_RULE_DISPLAY_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM as PHI_TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
)
from formal.python.tools.toe_native_a_ck_source_bridge_transport_rule_family_closeout_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM as A_BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    DEFAULT_OUT as A_CLOSEOUT_PATH,
    OUTCOME_ID as A_CLOSEOUT_OUTCOME,
    PACKET_ID as A_CLOSEOUT_PACKET_ID,
    SCHEMA_ID as A_CLOSEOUT_SCHEMA_ID,
    SOURCE_RULE_DISPLAY_FORM as A_SOURCE_RULE_DISPLAY_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM as A_TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
)
from formal.python.tools.toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_result_review_report import (
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CONSTRAINT_FORM,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    DEFAULT_OUT as PSI_A_CLOSEOUT_RESULT_REVIEW_PATH,
    EXCHANGE_TERM_CANCELLATION,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as PSI_A_CLOSEOUT_RESULT_REVIEW_OUTCOME,
    PACKET_ID as PSI_A_CLOSEOUT_RESULT_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    REVIEW_RESULT as PSI_A_CLOSEOUT_RESULT_REVIEW_RESULT,
    SCHEMA_ID as PSI_A_CLOSEOUT_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
    CURRENT_TARGET_AGGREGATE_PATH,
    LEAN_VALIDATION_POLICY_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_20260626_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_v0"
PACKET_RESULT = (
    "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_PREPARED_"
    "SOURCE_BRIDGE_TRANSPORT_AND_EXCHANGE_RULE_FAMILIES_SYNTHESIZED_"
    "NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = PACKET_RESULT
PACKET_CLASSIFICATION = (
    "master_action_ck_family_status_synthesis_after_phi_A_and_psi_A_prepared_"
    "source_bridge_transport_and_exchange_rule_families_synthesized_"
    "no_action_variation_or_master_action_promotion"
)
NEXT_TARGET = "review_master_action_ck_family_status_synthesis_after_phi_A_and_psi_A_result"
NEXT_TARGET_KIND = (
    "master_action_ck_family_status_synthesis_after_phi_A_and_psi_A_result_review"
)
REVIEW_OUTCOME_HINT = (
    "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_"
    "ACCEPTS_SOURCE_BRIDGE_TRANSPORT_AND_EXCHANGE_RULE_FAMILY_SUMMARY_"
    "NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)

C_SOURCE_CLASSIFICATION = "field/source admissibility"
C_BRIDGE_CLASSIFICATION = "route-matching admissibility"
C_TRANSPORT_CLASSIFICATION = "derivation-chain stability"
C_EXCHANGE_CLASSIFICATION = "interaction exchange-balance admissibility"
RULE_ARCHITECTURE_STATUS = (
    "source_bridge_transport_and_exchange_families_synthesized"
)
MASTER_ACTION_STATUS = "working-form, noncanonical, non-promoted organizing surface"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_20260626_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionCKFamilyStatusSynthesisAfterPhiAAndPsiA.lean"
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
        "quantized_electromagnetism_claimed": False,
        "anomaly_analysis_performed": False,
        "standard_model_derivation_claimed": False,
        "phase2_authorized": False,
        "phase2_readiness_claim": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "ck_family_status_synthesis_result_review_prepared": False,
    }


def _input_boundary_clear(payloads: list[dict[str, Any]]) -> bool:
    boundary_keys = set(_false_boundary_flags())
    boundary_keys.update(
        {
            "master_action_promoted",
            "master_action_promotion_authorized",
            "qft_gr_closure_claimed",
            "em_qft_closure_claimed",
            "seam_closure_claim",
            "empirical_validation_claimed",
            "standard_model_derivation_claimed",
            "phase2_authorized",
            "phase2_readiness_claim",
        }
    )
    return all(
        payload.get(key) is False
        for payload in payloads
        for key in boundary_keys
        if key in payload
    )


def _synthesis_criteria(
    phi_closeout: dict[str, Any],
    a_closeout: dict[str, Any],
    psi_a_review: dict[str, Any],
) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "phi_source_bridge_transport_family_synthesized",
            "status": "accepted",
            "evidence": [
                PHI_SOURCE_RULE_DISPLAY_FORM,
                PHI_BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
                PHI_TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
            ],
            "assessment": "The phi isolated-field source/bridge/transport family is summarized.",
        },
        {
            "row_id": "A_source_bridge_transport_family_synthesized",
            "status": "accepted",
            "evidence": [
                A_SOURCE_RULE_DISPLAY_FORM,
                A_BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
                A_TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
            ],
            "assessment": "The vacuum U(1) A source/bridge/transport family is summarized.",
        },
        {
            "row_id": "psi_A_current_source_exchange_total_conservation_family_synthesized",
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
            "assessment": "The bounded psi-A interaction current/source/exchange family is summarized.",
        },
        {
            "row_id": "C_source_classified",
            "status": "accepted",
            "evidence": C_SOURCE_CLASSIFICATION,
            "assessment": "C_source is classified as field/source admissibility.",
        },
        {
            "row_id": "C_bridge_classified",
            "status": "accepted",
            "evidence": C_BRIDGE_CLASSIFICATION,
            "assessment": "C_bridge is classified as route-matching admissibility.",
        },
        {
            "row_id": "C_transport_classified",
            "status": "accepted",
            "evidence": C_TRANSPORT_CLASSIFICATION,
            "assessment": "C_transport is classified as derivation-chain stability.",
        },
        {
            "row_id": "C_exchange_classified",
            "status": "accepted",
            "evidence": C_EXCHANGE_CLASSIFICATION,
            "assessment": "C_exchange is classified as interaction exchange-balance admissibility.",
        },
        {
            "row_id": "admissibility_only_not_action_embedded_or_varied",
            "status": "accepted",
            "evidence": [
                phi_closeout.get("family_epistemic_status"),
                a_closeout.get("family_epistemic_status"),
                psi_a_review.get("C_exchange_rule_epistemic_status"),
                "not_action_embedded=true",
                "not_varied=true",
            ],
            "assessment": "All summarized C_k families remain admissibility-only, not action-embedded, and not varied.",
        },
        {
            "row_id": "no_seam_closure_or_empirical_claim",
            "status": "accepted",
            "evidence": [
                "seam_closure_claim=false",
                "empirical_validation_claimed=false",
            ],
            "assessment": "The packet makes no seam-closure or empirical claim.",
        },
        {
            "row_id": "no_master_action_promotion",
            "status": "accepted",
            "evidence": MASTER_ACTION_STATUS,
            "assessment": "The master action remains working-form, noncanonical, and non-promoted.",
        },
        {
            "row_id": "full_toeformal_aggregate_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full ToeFormal aggregate status is preserved as NOT_RUN.",
        },
        {
            "row_id": "result_review_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is the result review for this status synthesis.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "master_action_ck_family_status_synthesis_after_phi_A_and_psi_A"
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


def build_master_action_ck_family_status_synthesis_after_phi_a_and_psi_a(
    *,
    phi_closeout_path: Path = PHI_CLOSEOUT_PATH,
    a_closeout_path: Path = A_CLOSEOUT_PATH,
    psi_a_closeout_result_review_path: Path = PSI_A_CLOSEOUT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    phi_closeout = _read_json(phi_closeout_path)
    a_closeout = _read_json(a_closeout_path)
    psi_a_review = _read_json(psi_a_closeout_result_review_path)
    payloads = [phi_closeout, a_closeout, psi_a_review]
    synthesis_criteria = _synthesis_criteria(phi_closeout, a_closeout, psi_a_review)
    acceptance_criteria = {
        "phi_closeout_accepted": (
            phi_closeout.get("schema_id") == PHI_CLOSEOUT_SCHEMA_ID
            and phi_closeout.get("packet_id") == PHI_CLOSEOUT_PACKET_ID
            and phi_closeout.get("outcome_id") == PHI_CLOSEOUT_OUTCOME
            and phi_closeout.get("accepted") is True
            and phi_closeout.get("source_bridge_transport_admissibility_rule_family_closed")
            is True
            and phi_closeout.get("all_three_rules_admissibility_only") is True
            and phi_closeout.get("all_three_rules_not_action_embedded") is True
            and phi_closeout.get("all_three_rules_not_varied") is True
        ),
        "A_closeout_accepted": (
            a_closeout.get("schema_id") == A_CLOSEOUT_SCHEMA_ID
            and a_closeout.get("packet_id") == A_CLOSEOUT_PACKET_ID
            and a_closeout.get("outcome_id") == A_CLOSEOUT_OUTCOME
            and a_closeout.get("accepted") is True
            and a_closeout.get("source_bridge_transport_family_closed") is True
            and a_closeout.get("all_three_rules_admissibility_only") is True
            and a_closeout.get("all_three_rules_not_action_embedded") is True
            and a_closeout.get("all_three_rules_not_varied") is True
        ),
        "psi_A_closeout_result_review_accepted": (
            psi_a_review.get("schema_id") == PSI_A_CLOSEOUT_RESULT_REVIEW_SCHEMA_ID
            and psi_a_review.get("packet_id") == PSI_A_CLOSEOUT_RESULT_REVIEW_PACKET_ID
            and psi_a_review.get("outcome_id")
            == PSI_A_CLOSEOUT_RESULT_REVIEW_OUTCOME
            and psi_a_review.get("review_result")
            == PSI_A_CLOSEOUT_RESULT_REVIEW_RESULT
            and psi_a_review.get("accepted") is True
            and psi_a_review.get("selected_next_target") == CONSUMED_TARGET
            and psi_a_review.get("psi_A_interaction_family_closed") is True
            and psi_a_review.get(
                "current_source_exchange_total_conservation_route_preserved"
            )
            is True
            and psi_a_review.get("C_exchange_remains_admissibility_only") is True
        ),
        "rule_classifications_defined": all(
            [
                C_SOURCE_CLASSIFICATION,
                C_BRIDGE_CLASSIFICATION,
                C_TRANSPORT_CLASSIFICATION,
                C_EXCHANGE_CLASSIFICATION,
            ]
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            phi_closeout.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and a_closeout.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and psi_a_review.get("aggregate_lean_validation_status_for_review")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
        ),
        "input_boundary_flags_clear": _input_boundary_clear(payloads),
        "synthesis_criteria_all_accepted": all(
            row["status"] == "accepted" for row in synthesis_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID if accepted else "SYNTHESIS_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID if accepted else "SYNTHESIS_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "review_outcome_hint": REVIEW_OUTCOME_HINT,
        "rule_architecture_status": RULE_ARCHITECTURE_STATUS,
        "master_action_status": MASTER_ACTION_STATUS,
        "phi_closeout_packet_id": PHI_CLOSEOUT_PACKET_ID,
        "phi_closeout_outcome": PHI_CLOSEOUT_OUTCOME,
        "A_closeout_packet_id": A_CLOSEOUT_PACKET_ID,
        "A_closeout_outcome": A_CLOSEOUT_OUTCOME,
        "psi_A_closeout_result_review_packet_id": (
            PSI_A_CLOSEOUT_RESULT_REVIEW_PACKET_ID
        ),
        "psi_A_closeout_result_review_outcome": (
            PSI_A_CLOSEOUT_RESULT_REVIEW_OUTCOME
        ),
        "mature_rule_classes": [
            {
                "rule_id": "C_source",
                "classification": C_SOURCE_CLASSIFICATION,
                "status": "matured_as_admissibility_only",
            },
            {
                "rule_id": "C_bridge",
                "classification": C_BRIDGE_CLASSIFICATION,
                "status": "matured_as_admissibility_only",
            },
            {
                "rule_id": "C_transport",
                "classification": C_TRANSPORT_CLASSIFICATION,
                "status": "matured_as_admissibility_only",
            },
            {
                "rule_id": "C_exchange",
                "classification": C_EXCHANGE_CLASSIFICATION,
                "status": "matured_as_admissibility_only",
            },
        ],
        "mature_rule_class_count": 4,
        "family_status_summary": [
            {
                "family_id": "phi",
                "family_type": "isolated field",
                "summary": "C_source + C_bridge + C_transport",
                "rule_forms": [
                    PHI_SOURCE_RULE_DISPLAY_FORM,
                    PHI_BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
                    PHI_TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
                ],
                "epistemic_status": "admissibility-only",
            },
            {
                "family_id": "A",
                "family_type": "isolated vacuum U(1) field",
                "summary": "C_source + C_bridge + C_transport",
                "rule_forms": [
                    A_SOURCE_RULE_DISPLAY_FORM,
                    A_BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
                    A_TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
                ],
                "epistemic_status": "admissibility-only",
            },
            {
                "family_id": "psi-A",
                "family_type": "bounded interacting field pair",
                "summary": (
                    "current + sourced gauge route + exchange + total conservation + C_exchange"
                ),
                "rule_forms": [
                    CURRENT_CANDIDATE,
                    CURRENT_CONSERVATION_RESULT,
                    SOURCED_GAUGE_ROUTE,
                    GAUGE_SECTOR_EXCHANGE_IDENTITY,
                    MATTER_SECTOR_EXCHANGE_IDENTITY,
                    EXCHANGE_TERM_CANCELLATION,
                    TOTAL_STRESS_ENERGY_OBJECT,
                    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
                    C_EXCHANGE_CONSTRAINT_FORM,
                    C_EXCHANGE_ADMISSIBILITY_CONDITION,
                ],
                "epistemic_status": "bounded admissibility-only interaction family",
            },
        ],
        "family_count": 3,
        "isolated_field_family_count": 2,
        "interaction_family_count": 1,
        "source_current": SOURCE_CURRENT,
        "current_candidate": CURRENT_CANDIDATE,
        "current_conservation_result": CURRENT_CONSERVATION_RESULT,
        "sourced_gauge_route": SOURCED_GAUGE_ROUTE,
        "gauge_sector_exchange_identity": GAUGE_SECTOR_EXCHANGE_IDENTITY,
        "matter_sector_exchange_identity": MATTER_SECTOR_EXCHANGE_IDENTITY,
        "exchange_term_cancellation": EXCHANGE_TERM_CANCELLATION,
        "total_stress_energy_object": TOTAL_STRESS_ENERGY_OBJECT,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_constraint_form": C_EXCHANGE_CONSTRAINT_FORM,
        "C_exchange_admissibility_condition": C_EXCHANGE_ADMISSIBILITY_CONDITION,
        "C_source_classification": C_SOURCE_CLASSIFICATION,
        "C_bridge_classification": C_BRIDGE_CLASSIFICATION,
        "C_transport_classification": C_TRANSPORT_CLASSIFICATION,
        "C_exchange_classification": C_EXCHANGE_CLASSIFICATION,
        "synthesis_criteria": synthesis_criteria,
        "synthesis_criteria_count": len(synthesis_criteria),
        "synthesis_criteria_accepted_count": sum(
            1 for row in synthesis_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "synthesis_packet_prepared": accepted,
        "synthesis_packet_accepted": accepted,
        "master_action_ck_family_status_synthesis_prepared": accepted,
        "ck_family_status_synthesis_prepared": accepted,
        "phi_source_bridge_transport_family_synthesized": accepted,
        "A_source_bridge_transport_family_synthesized": accepted,
        "psi_A_interaction_exchange_family_synthesized": accepted,
        "current_source_exchange_and_total_conservation_family_synthesized": accepted,
        "C_source_classified": accepted,
        "C_bridge_classified": accepted,
        "C_transport_classified": accepted,
        "C_exchange_classified": accepted,
        "isolated_field_rule_families_summarized": accepted,
        "interaction_rule_family_summarized": accepted,
        "admissibility_rule_architecture_summary_prepared": accepted,
        "all_summarized_rules_admissibility_only": accepted,
        "all_summarized_rules_not_action_embedded": accepted,
        "all_summarized_rules_not_varied": accepted,
        "all_summarized_rules_not_direct_dynamical_laws": accepted,
        "all_summarized_rules_not_empirical_claims": accepted,
        "master_action_remains_working_form_noncanonical": accepted,
        "result_review_authorized": accepted,
        "result_review_prepared": False,
        "plain_meaning": (
            "The framework now has admissibility rules for isolated phi and A "
            "fields plus one bounded psi-A interaction exchange family."
        ),
        "mathematical_statement": (
            "The status synthesis records phi: C_source + C_bridge + C_transport; "
            "A: C_source + C_bridge + C_transport; and psi-A: "
            f"{CURRENT_CANDIDATE}; {CURRENT_CONSERVATION_RESULT}; "
            f"{SOURCED_GAUGE_ROUTE}; {GAUGE_SECTOR_EXCHANGE_IDENTITY}; "
            f"{MATTER_SECTOR_EXCHANGE_IDENTITY}; "
            f"{TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY}; "
            f"{C_EXCHANGE_CONSTRAINT_FORM}; {C_EXCHANGE_ADMISSIBILITY_CONDITION}."
        ),
        "non_claim_boundary": (
            "This packet is a master-action C_k family status synthesis only. "
            "It classifies C_source as field/source admissibility, C_bridge as "
            "route-matching admissibility, C_transport as derivation-chain "
            "stability, and C_exchange as interaction exchange-balance "
            "admissibility. It records isolated phi and A source/bridge/"
            "transport families and the bounded psi-A current/source/exchange/"
            "total-conservation family. All summarized rules remain "
            "admissibility-only, not action embedded, not varied, not direct "
            "dynamical laws, not empirical claims, and not master-action "
            "promotion. It records no C_k action embedding, no C_k action "
            "variation, no multiplier route, no penalty route, no full Maxwell "
            "closure, no EM-QFT closure, no QFT-GR closure, no GR-QM closure, "
            "no Standard Model derivation, no Phase 2 authorization, no "
            "empirical validation, no seam closure, and no master-action "
            "promotion. The master action remains a working-form, noncanonical, "
            "non-promoted organizing surface, and the full ToeFormal aggregate "
            "is kept as NOT_RUN."
        ),
        "critical_gate_fail_conditions": [
            "drop phi C_source + C_bridge + C_transport",
            "drop A C_source + C_bridge + C_transport",
            "drop psi-A current/source/exchange/total-conservation/C_exchange route",
            "misclassify C_source, C_bridge, C_transport, or C_exchange",
            "claim any summarized rule is action embedded",
            "execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "interpret C_k rules as direct dynamical laws",
            "claim full Maxwell closure",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "claim GR-QM closure",
            "derive the Standard Model",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "prepare the result review inside this synthesis",
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
            "ToeFormal.Derivation.MasterActionCKFamilyStatusSynthesisAfterPhiAAndPsiA",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "phi_closeout_file": _ptr(phi_closeout_path),
            "A_closeout_file": _ptr(a_closeout_path),
            "psi_A_closeout_result_review_file": _ptr(psi_a_closeout_result_review_path),
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


def write_synthesis(payload: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Build the master-action C_k family status synthesis after phi, A, and psi-A."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--phi-closeout", type=Path, default=PHI_CLOSEOUT_PATH)
    parser.add_argument("--a-closeout", type=Path, default=A_CLOSEOUT_PATH)
    parser.add_argument(
        "--psi-a-closeout-result-review",
        type=Path,
        default=PSI_A_CLOSEOUT_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    phi_closeout_path = (
        args.phi_closeout
        if args.phi_closeout.is_absolute()
        else REPO_ROOT / args.phi_closeout
    )
    a_closeout_path = (
        args.a_closeout
        if args.a_closeout.is_absolute()
        else REPO_ROOT / args.a_closeout
    )
    psi_a_review_path = (
        args.psi_a_closeout_result_review
        if args.psi_a_closeout_result_review.is_absolute()
        else REPO_ROOT / args.psi_a_closeout_result_review
    )

    payload = build_master_action_ck_family_status_synthesis_after_phi_a_and_psi_a(
        phi_closeout_path=phi_closeout_path,
        a_closeout_path=a_closeout_path,
        psi_a_closeout_result_review_path=psi_a_review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_synthesis(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "packet_result": payload["packet_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
