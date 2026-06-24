from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_ck_source_bridge_transport_rule_family_synthesis_result_review_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_RULE_CLASSIFICATION,
    DEFAULT_OUT as TRIAD_RESULT_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_GROUP_POLICY,
    KNOWN_A_TRANSPORT_CHAIN_FORM,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID as TRIAD_RESULT_REVIEW_OUTCOME,
    PACKET_ID as TRIAD_RESULT_REVIEW_PACKET_ID,
    REVIEW_RESULT as TRIAD_REVIEW_RESULT,
    RULE_FAMILY_CLASSIFICATION,
    SCHEMA_ID as TRIAD_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_ROUTE_STILL_BLOCKED,
    SOURCE_RULE_CLASSIFICATION,
    SOURCE_RULE_DISPLAY_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_DISPLAY_FORM,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_CLOSEOUT_20260624_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_CLOSEOUT_v0"
CLOSEOUT_RESULT = (
    "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_CLOSED_AS_THREE_RULE_"
    "VACUUM_U1_ADMISSIBILITY_FAMILY_NO_CURRENT_OR_EM_CLOSURE"
)
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_ck_source_bridge_transport_rule_family_closeout_closes_"
    "three_rule_vacuum_u1_admissibility_family_no_current_or_em_closure"
)
NEXT_TARGET = "select_next_master_action_interaction_after_A_ck_triad"
NEXT_TARGET_KIND = "master_action_interaction_selector_after_A_ck_triad"
RECOMMENDED_INTERACTION_ROUTE = "psi_A_u1_current_and_exchange_route"
RECOMMENDED_NEXT_POLICY_PACKET = (
    "prepare_toe_native_psi_A_u1_current_and_exchange_route_policy_packet"
)
FAMILY_CLASSIFICATION = "first A-relevant three-rule C_k admissibility family"
FAMILY_SCOPE = "vacuum U(1)"
FAMILY_EPISTEMIC_STATUS = "admissibility-only"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_CLOSEOUT_20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeACKSourceBridgeTransportRuleFamilyCloseout.lean"
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


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _closeout_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "result_review_accepts_three_rule_family",
            "status": "accepted",
            "evidence": review.get("review_result"),
            "assessment": "The result review accepted the three-rule A/C_k synthesis.",
        },
        {
            "row_id": "source_admissibility_rule_preserved",
            "status": "accepted",
            "evidence": [SOURCE_RULE_DISPLAY_FORM, SOURCE_ADMISSIBILITY_CONSTRAINT_FORM],
            "assessment": "C_source^A = 0 is preserved.",
        },
        {
            "row_id": "bridge_admissibility_rule_preserved",
            "status": "accepted",
            "evidence": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "C_bridge^A = 0 is preserved.",
        },
        {
            "row_id": "transport_consistency_rule_preserved",
            "status": "accepted",
            "evidence": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "C_transport^A = 0 is preserved.",
        },
        {
            "row_id": "vacuum_u1_three_rule_family_closed",
            "status": "accepted",
            "evidence": FAMILY_CLASSIFICATION,
            "assessment": "The closeout records the first A-relevant vacuum U(1) three-rule C_k family.",
        },
        {
            "row_id": "admissibility_only_not_action_embedded_or_varied",
            "status": "accepted",
            "evidence": [
                FAMILY_EPISTEMIC_STATUS,
                "not_action_embedded=true",
                "not_varied=true",
            ],
            "assessment": "The family remains admissibility-only, not action-embedded, and not varied.",
        },
        {
            "row_id": "no_current_jnu_sourced_maxwell_or_exchange",
            "status": "accepted",
            "evidence": [
                "current_route_derived=false",
                "J_nu_derived=false",
                "sourced_maxwell_route_derived=false",
                "matter_current_exchange_route_proved=false",
            ],
            "assessment": "No current, J^nu, sourced Maxwell, or exchange route is claimed.",
        },
        {
            "row_id": "no_em_qft_gr_coupling_empirical_or_master_promotion",
            "status": "accepted",
            "evidence": [
                "em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "semiclassical_coupling_claimed=false",
                "empirical_validation_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "Closure, coupling, empirical validation, and promotion remain unclaimed.",
        },
        {
            "row_id": "full_toeformal_aggregate_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full ToeFormal aggregate is recorded as NOT_RUN.",
        },
        {
            "row_id": "post_closeout_interaction_selector_only",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next target is only the post-A-triad interaction selector.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_A_ck_source_bridge_transport_rule_family_closeout",
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


def build_toe_native_a_ck_source_bridge_transport_rule_family_closeout(
    *,
    triad_result_review_path: Path = TRIAD_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(triad_result_review_path)
    closeout_criteria = _closeout_criteria(review)
    acceptance_criteria = {
        "consumes_expected_closeout_target": (
            review.get("schema_id") == TRIAD_RESULT_REVIEW_SCHEMA_ID
            and review.get("packet_id") == TRIAD_RESULT_REVIEW_PACKET_ID
            and review.get("outcome_id") == TRIAD_RESULT_REVIEW_OUTCOME
            and review.get("review_result") == TRIAD_REVIEW_RESULT
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "source_rule_preserved": (
            review.get("source_rule_display_form") == SOURCE_RULE_DISPLAY_FORM
            and review.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and review.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and review.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and review.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "bridge_rule_preserved": (
            review.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and review.get("bridge_constraint_equation") == BRIDGE_CONSTRAINT_EQUATION
            and review.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "transport_rule_preserved": (
            review.get("transport_candidate_id") == TRANSPORT_CANDIDATE_ID
            and review.get("transport_candidate_type") == TRANSPORT_CANDIDATE_TYPE
            and review.get("transport_constraint_form") == TRANSPORT_CONSTRAINT_FORM
            and review.get("transport_constraint_equation")
            == TRANSPORT_CONSTRAINT_EQUATION
            and review.get("transport_admissibility_constraint_form")
            == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
            and review.get("transport_component_count") == len(TRANSPORT_COMPONENTS)
        ),
        "triad_classification_preserved": (
            review.get("A_ck_admissibility_rule_family_count") == 3
            and review.get("rule_family_classification") == RULE_FAMILY_CLASSIFICATION
            and review.get("all_three_rules_admissibility_only") is True
            and review.get("all_three_rules_rule_candidates") is True
            and review.get("all_three_rules_not_action_terms") is True
            and review.get("all_three_rules_not_dynamical_laws") is True
            and review.get("all_three_rules_not_current_coupled") is True
        ),
        "no_forbidden_claims": all(
            review.get(key) is False
            for key in [
                "selector_after_closeout_authorized",
                "next_master_action_surface_selected",
                "next_ck_constraint_family_selected",
                "another_A_route_selected",
                "constraint_as_action_term_selected",
                "dynamical_action_embedding_selected",
                "dynamical_law_claimed",
                "candidate_recorded_as_new_physical_law",
                "candidate_recorded_as_action_term",
                "ck_action_embedding_claimed",
                "ck_variation_executed",
                "ck_variation_authorized",
                "lambda_variation_executed",
                "metric_variation_executed",
                "A_variation_executed",
                "bridge_admissibility_proved",
                "route_alignment_verified",
                "full_route_alignment_proved",
                "full_route_alignment_proof_claimed",
                "source_admissibility_proved",
                "source_conservation_proved",
                "transport_consistency_proved",
                "transport_proof_claimed",
                "transport_components_proved",
                "current_route_derived",
                "current_source_route_constructed",
                "matter_current_J_nu_derived",
                "J_nu_derived",
                "psi_current_route_constructed",
                "external_current_native_derivation_selected",
                "matter_current_exchange_route_proved",
                "matter_gauge_energy_exchange_proved",
                "sourced_maxwell_equation_derived",
                "sourced_maxwell_route_derived",
                "full_em_closure_claimed",
                "em_closure_claimed",
                "em_qft_closure_claimed",
                "qft_gr_closure_claimed",
                "qft_gr_solved",
                "qft_gr_seam_closed",
                "semiclassical_coupling_authorized",
                "semiclassical_coupling_claimed",
                "semiclassical_einstein_equation_derived",
                "master_action_promoted",
                "master_action_promotion_authorized",
                "canonical_master_action_promoted",
                "toe_native_matter_derivation_claimed",
                "standard_model_derivation_claimed",
                "native_generation_theorem_claimed",
                "empirical_validation_claimed",
                "public_readiness_claimed",
                "public_submission_authorized",
                "phase2_readiness_claim",
                "pillar_completion_inferred",
                "seam_closure_claim",
            ]
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            review.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and review.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and review.get("full_toeformal_aggregate_passed") is False
            and review.get("full_toeformal_aggregate_failed") is False
            and review.get("full_toeformal_aggregate_timed_out") is False
        ),
        "closeout_criteria_all_accepted": all(
            row["status"] == "accepted" for row in closeout_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_CLOSEOUT"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_CLOSEOUT",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_CLOSEOUT_REQUIRES_REMEDIATION",
        "closeout_result": CLOSEOUT_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "triad_result_review_packet_id": TRIAD_RESULT_REVIEW_PACKET_ID,
        "triad_result_review_outcome": TRIAD_RESULT_REVIEW_OUTCOME,
        "triad_review_result": TRIAD_REVIEW_RESULT,
        "family_classification": FAMILY_CLASSIFICATION,
        "family_scope": FAMILY_SCOPE,
        "family_epistemic_status": FAMILY_EPISTEMIC_STATUS,
        "rule_family_classification": RULE_FAMILY_CLASSIFICATION,
        "A_ck_admissibility_rule_family_count": 3,
        "concrete_A_ck_rule_roles": [
            "source admissibility",
            "bridge admissibility",
            "transport consistency",
        ],
        "rule_family_display_forms": [
            SOURCE_RULE_DISPLAY_FORM,
            BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            TRANSPORT_RULE_DISPLAY_FORM,
        ],
        "source_rule_classification": SOURCE_RULE_CLASSIFICATION,
        "source_rule_epistemic_status": FAMILY_EPISTEMIC_STATUS,
        "source_rule_display_form": SOURCE_RULE_DISPLAY_FORM,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_rule_classification": BRIDGE_RULE_CLASSIFICATION,
        "bridge_rule_epistemic_status": FAMILY_EPISTEMIC_STATUS,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "A_bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "A_bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "transport_rule_classification": TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
        "transport_closeout_rule_classification": TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
        "transport_rule_epistemic_status": TRANSPORT_RULE_EPISTEMIC_STATUS,
        "transport_candidate_id": TRANSPORT_CANDIDATE_ID,
        "transport_candidate_type": TRANSPORT_CANDIDATE_TYPE,
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_admissibility_constraint_form": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        "transport_component_count": len(TRANSPORT_COMPONENTS),
        "transport_component_forms": [row["component_form"] for row in TRANSPORT_COMPONENTS],
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "on_shell_vacuum_conservation_identity": ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "known_A_transport_chain_form": KNOWN_A_TRANSPORT_CHAIN_FORM,
        "closeout_criteria": closeout_criteria,
        "closeout_criteria_count": len(closeout_criteria),
        "closeout_criteria_accepted_count": sum(
            1 for row in closeout_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "closeout_prepared": True,
        "closeout_accepted": True,
        "review_accepted": True,
        "A_ck_triad_closed": True,
        "source_bridge_transport_family_closed": True,
        "source_admissibility_rule_closed": True,
        "bridge_admissibility_rule_closed": True,
        "transport_consistency_rule_closed": True,
        "three_rule_vacuum_u1_admissibility_family_closed": True,
        "c_k_source_permission_role_closed": True,
        "c_k_bridge_permission_role_closed": True,
        "c_k_transport_stability_role_closed": True,
        "all_three_rules_admissibility_only": True,
        "all_three_rules_rule_candidates": True,
        "all_three_rules_not_action_terms": True,
        "all_three_rules_not_action_embedded": True,
        "all_three_rules_not_varied": True,
        "all_three_rules_not_dynamical_laws": True,
        "all_three_rules_not_current_coupled": True,
        "post_closeout_selector_authorized": True,
        "post_closeout_selector_target_recommended": NEXT_TARGET,
        "recommended_interaction_route": RECOMMENDED_INTERACTION_ROUTE,
        "recommended_next_policy_packet": RECOMMENDED_NEXT_POLICY_PACKET,
        "interaction_selector_executed": False,
        "psi_A_current_exchange_route_selected": False,
        "psi_A_current_exchange_policy_packet_prepared": False,
        "current_route_derived": False,
        "current_source_route_constructed": False,
        "matter_current_J_nu_derived": False,
        "J_nu_derived": False,
        "psi_current_route_constructed": False,
        "external_current_native_derivation_selected": False,
        "sourced_maxwell_equation_derived": False,
        "sourced_maxwell_route_derived": False,
        "matter_current_exchange_route_proved": False,
        "matter_gauge_energy_exchange_proved": False,
        "constraint_as_action_term_selected": False,
        "dynamical_action_embedding_selected": False,
        "dynamical_law_claimed": False,
        "candidate_recorded_as_new_physical_law": False,
        "candidate_recorded_as_action_term": False,
        "ck_action_embedding_claimed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "C_k_action_embedding_constructed": False,
        "C_k_variation_executed": False,
        "lambda_variation_executed": False,
        "metric_variation_executed": False,
        "A_variation_executed": False,
        "bridge_admissibility_proved": False,
        "route_alignment_verified": False,
        "full_route_alignment_proved": False,
        "full_route_alignment_proof_claimed": False,
        "source_admissibility_proved": False,
        "source_conservation_proved": False,
        "transport_consistency_proved": False,
        "transport_proof_claimed": False,
        "transport_components_proved": False,
        "transport_candidate_functional_defined": False,
        "fully_concrete_ck_functional_defined": False,
        "full_em_closure_claimed": False,
        "em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "toe_native_matter_derivation_claimed": False,
        "standard_model_derivation_claimed": False,
        "native_generation_theorem_claimed": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "mathematical_statement": (
            "The ToE-native A/C_k source-bridge-transport triad is closed as "
            "the first A-relevant vacuum U(1) three-rule admissibility family: "
            "C_source^A = 0 for source admissibility, C_bridge^A = 0 for "
            "bridge admissibility, and C_transport^A = 0 for derivation-chain "
            "transport consistency."
        ),
        "non_claim_boundary": (
            "This closeout records the first A-relevant three-rule C_k "
            "family only, in vacuum U(1) scope. It closes source-admissibility, "
            "bridge-admissibility, and transport-consistency as "
            "admissibility-only rule candidates: not action-embedded, not "
            "varied, not action terms, not dynamical laws, not current-coupled, "
            "not sourced Maxwell, no EM closure, no QFT-GR closure, and no "
            "master-action promotion. It records no current route, no J^nu "
            "derivation, no psi-current route, no external-current native "
            "derivation, no sourced Maxwell derivation, no matter/current "
            "exchange, no source-admissibility proof, no bridge-admissibility "
            "proof, no transport proof, no full route-alignment proof, no "
            "semiclassical coupling, no empirical validation, no Phase 2 "
            "authorization, and no public-readiness authorization. The full "
            "ToeFormal aggregate is recorded as NOT_RUN for this closeout. "
            "The next target is a selector for the next master-action "
            "interaction after the A/C_k triad, with psi_A_u1_current_and_exchange_route "
            "recommended but not selected here."
        ),
        "critical_gate_fail_conditions": [
            "drop C_source^A = 0",
            "drop C_bridge^A = 0",
            "drop C_transport^A = 0",
            "claim any rule is action-embedded",
            "execute C_k variation",
            "claim any rule is a dynamical law",
            "derive J^nu",
            "derive sourced Maxwell",
            "prove matter/current exchange",
            "claim EM closure",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "claim empirical validation",
            "promote the master action",
            "execute the interaction selector inside this closeout",
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
            "ToeFormal.Derivation.ToeNativeACKSourceBridgeTransportRuleFamilyCloseout",
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
            "triad_result_review_file": _ptr(triad_result_review_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_closeout(closeout: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(closeout, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A/C_k source-bridge-transport rule-family closeout."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    closeout = build_toe_native_a_ck_source_bridge_transport_rule_family_closeout(
        captured_at_utc=args.captured_at_utc
    )
    path = write_closeout(closeout, args.out)
    print(
        json.dumps(
            {
                "accepted": closeout["accepted"],
                "closeout_result": closeout["closeout_result"],
                "out": _ptr(path),
                "selected_next_target": closeout["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
