from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_vacuum_variation_retry_under_selected_u1_policy_result_review_report import (
    A_FIELD_DOMAIN_POLICY,
    A_VACUUM_VARIATION_RETRY_REVIEW_RESULT,
    A_VACUUM_VARIATION_RETRY_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as A_VACUUM_RETRY_RESULT_REVIEW_PATH,
    DELTA_F_FORM,
    F_DEFINITION_POLICY,
    GAUGE_GROUP_POLICY,
    INTEGRATION_BY_PARTS_FORM,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as A_VACUUM_RETRY_RESULT_REVIEW_OUTCOME,
    PACKET_ID as A_VACUUM_RETRY_RESULT_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as A_VACUUM_RETRY_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_ROUTE_STILL_BLOCKED,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-21T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_U1_VARIATION_20260621_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_U1_VARIATION_v0"
SELECTION_RESULT = (
    "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_U1_VARIATION_SELECTS_STRESS_"
    "ENERGY_ROUTE_NO_CURRENT_DERIVATION_OR_EM_CLOSURE"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_route_selection_after_vacuum_u1_variation_selects_stress_"
    "energy_route_no_current_derivation_or_em_closure"
)

NEXT_TARGET = "prepare_toe_native_A_stress_energy_route_under_selected_u1_policy"
NEXT_TARGET_KIND = "toe_native_A_stress_energy_route_under_selected_u1_policy_packet_preparation"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

SELECTED_ROUTE_ID = "A_stress_energy_route"
SELECTED_ROUTE_LABEL = "metric variation of the U(1) gauge action to T_A_mu_nu route"
SELECTED_ROUTE_STATUS = "selected_for_packet_preparation"
SELECTED_ROUTE_EXECUTION_STATUS = "not_executed"
SELECTED_ROUTE_REASON = (
    "The stress-energy route can proceed from the pure U(1) gauge action by "
    "metric variation before any external-current policy or psi/A matter "
    "coupling is selected."
)

CURRENT_COUPLING_TARGET = "prepare_toe_native_A_current_coupling_policy_packet"
CURRENT_CONSERVATION_TARGET = (
    "prepare_toe_native_A_current_conservation_route_under_selected_u1_policy"
)
A_RELEVANT_CK_TARGET = "prepare_toe_native_A_relevant_ck_rule_family_packet"
NONABELIAN_POLICY_TARGET = "prepare_toe_native_A_nonabelian_policy_packet"

ROUTE_SELECTOR_CANDIDATES = [
    SELECTED_ROUTE_ID,
    "A_current_coupling_route",
    "A_current_conservation_route",
    "A_relevant_C_k_source_bridge_transport_route",
    "A_nonabelian_route",
]
ROUTE_SELECTOR_COMPARISON = {
    SELECTED_ROUTE_ID: SELECTED_ROUTE_REASON,
    "A_current_coupling_route": (
        "Deferred because nabla_mu F^{mu nu} = J^nu still requires an "
        "external-current policy or psi/A matter coupling route."
    ),
    "A_current_conservation_route": (
        "Premature because no current J^nu has been derived or admitted."
    ),
    "A_relevant_C_k_source_bridge_transport_route": (
        "Premature before the A stress-energy/source route is available."
    ),
    "A_nonabelian_route": (
        "Deferred beyond the selected minimal U(1) / Abelian test route."
    ),
}

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_U1_VARIATION_20260621_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeARouteSelectionAfterVacuumU1Variation.lean"
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


def _route_options() -> list[dict[str, Any]]:
    return [
        {
            "route_id": SELECTED_ROUTE_ID,
            "route_label": SELECTED_ROUTE_LABEL,
            "candidate_target": NEXT_TARGET,
            "status": SELECTED_ROUTE_STATUS,
            "execution_status": SELECTED_ROUTE_EXECUTION_STATUS,
            "selection_reason": SELECTED_ROUTE_REASON,
            "stress_energy_derivation_executed": False,
            "current_route_derived": False,
            "em_closure_claimed": False,
        },
        {
            "route_id": "A_current_coupling_route",
            "candidate_target": CURRENT_COUPLING_TARGET,
            "status": "deferred_blocked_pending_J_nu_policy",
            "execution_status": "not_executed",
            "selection_reason": ROUTE_SELECTOR_COMPARISON["A_current_coupling_route"],
            "current_route_derived": False,
            "J_nu_derived": False,
        },
        {
            "route_id": "A_current_conservation_route",
            "candidate_target": CURRENT_CONSERVATION_TARGET,
            "status": "deferred_premature_without_current_derivation",
            "execution_status": "not_executed",
            "selection_reason": ROUTE_SELECTOR_COMPARISON["A_current_conservation_route"],
            "current_conservation_proved": False,
        },
        {
            "route_id": "A_relevant_C_k_source_bridge_transport_route",
            "candidate_target": A_RELEVANT_CK_TARGET,
            "status": "deferred_premature_before_T_A_source_route",
            "execution_status": "not_executed",
            "selection_reason": ROUTE_SELECTOR_COMPARISON[
                "A_relevant_C_k_source_bridge_transport_route"
            ],
            "A_relevant_C_k_rules_constructed": False,
        },
        {
            "route_id": "A_nonabelian_route",
            "candidate_target": NONABELIAN_POLICY_TARGET,
            "status": "deferred_beyond_minimal_U1_route",
            "execution_status": "not_executed",
            "selection_reason": ROUTE_SELECTOR_COMPARISON["A_nonabelian_route"],
            "nonabelian_route_selected": False,
        },
    ]


def _selection_criteria(previous_review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_consumes_current_a_route_selector_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The active selector target is consumed.",
        },
        {
            "row_id": "vacuum_u1_result_review_preserved",
            "status": "accepted",
            "evidence": previous_review.get("review_result"),
            "assessment": "The bounded vacuum U(1) result review remains the input.",
        },
        {
            "row_id": "selected_u1_policy_preserved",
            "status": "accepted",
            "evidence": [
                GAUGE_GROUP_POLICY,
                A_FIELD_DOMAIN_POLICY,
                F_DEFINITION_POLICY,
            ],
            "assessment": "The selected U(1) policy and F=dA definition are preserved.",
        },
        {
            "row_id": "vacuum_route_preserved",
            "status": "accepted",
            "evidence": VACUUM_EULER_LAGRANGE_ROUTE,
            "assessment": "nabla_mu F^{mu nu} = 0 remains a vacuum route only.",
        },
        {
            "row_id": "source_route_shape_still_blocked",
            "status": "accepted",
            "evidence": SOURCE_ROUTE_STILL_BLOCKED,
            "assessment": "nabla_mu F^{mu nu} = J^nu remains blocked route shape.",
        },
        {
            "row_id": "stress_energy_route_selected_as_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next packet is the bounded A stress-energy route.",
        },
        {
            "row_id": "current_coupling_deferred_pending_current_policy",
            "status": "accepted",
            "evidence": CURRENT_COUPLING_TARGET,
            "assessment": "Current coupling remains blocked pending J^nu policy.",
        },
        {
            "row_id": "current_conservation_deferred_until_current_route",
            "status": "accepted",
            "evidence": CURRENT_CONSERVATION_TARGET,
            "assessment": "Current conservation remains premature without J^nu.",
        },
        {
            "row_id": "a_relevant_ck_deferred_until_source_route",
            "status": "accepted",
            "evidence": A_RELEVANT_CK_TARGET,
            "assessment": "A-relevant C_k rules remain premature before T_A/source route.",
        },
        {
            "row_id": "nonabelian_route_deferred",
            "status": "accepted",
            "evidence": NONABELIAN_POLICY_TARGET,
            "assessment": "The non-Abelian route is deferred beyond minimal U(1).",
        },
        {
            "row_id": "selector_only_no_stress_energy_derivation",
            "status": "accepted",
            "evidence": "stress_energy_derivation_executed=false",
            "assessment": "The selector does not perform metric variation or derive T_A.",
        },
        {
            "row_id": "no_closure_or_promotion",
            "status": "accepted",
            "evidence": [
                "em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No closure or master-action promotion follows.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_A_route_selection_after_vacuum_u1_variation",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "aggregate_timeout_with_steady_progress_interpretation": (
            "incomplete_validation_not_mathematical_failure"
        ),
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": "NOT_RUN",
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_toe_native_a_route_selection_after_vacuum_u1_variation(
    *,
    a_vacuum_retry_result_review_path: Path = A_VACUUM_RETRY_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    previous_review = _read_json(a_vacuum_retry_result_review_path)
    route_options = _route_options()
    selection_criteria = _selection_criteria(previous_review)
    acceptance_criteria = {
        "consumes_expected_selector_target": (
            previous_review.get("schema_id") == A_VACUUM_RETRY_RESULT_REVIEW_SCHEMA_ID
            and previous_review.get("packet_id")
            == A_VACUUM_RETRY_RESULT_REVIEW_PACKET_ID
            and previous_review.get("outcome_id")
            == A_VACUUM_RETRY_RESULT_REVIEW_OUTCOME
            and previous_review.get("review_result")
            == A_VACUUM_VARIATION_RETRY_REVIEW_RESULT
            and previous_review.get("selected_next_target") == CONSUMED_TARGET
            and previous_review.get("accepted") is True
        ),
        "vacuum_u1_route_preserved": (
            previous_review.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and previous_review.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and previous_review.get("F_definition_policy") == F_DEFINITION_POLICY
            and previous_review.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
        ),
        "source_route_still_shape_only": (
            previous_review.get("source_route_still_blocked")
            == SOURCE_ROUTE_STILL_BLOCKED
            and previous_review.get("current_route_derived") is False
            and previous_review.get("J_nu_derived") is False
        ),
        "stress_energy_route_selected_once": (
            sum(1 for row in route_options if row["status"] == SELECTED_ROUTE_STATUS)
            == 1
            and NEXT_TARGET
            == "prepare_toe_native_A_stress_energy_route_under_selected_u1_policy"
        ),
        "deferred_routes_not_executed": all(
            row["execution_status"] == "not_executed" for row in route_options
        ),
        "selection_criteria_all_accepted": all(
            row["status"] == "accepted" for row in selection_criteria
        ),
        "selector_only_no_derivation_or_closure": True,
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_U1_VARIATION"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_U1_VARIATION",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_U1_VARIATION_REQUIRES_REMEDIATION",
        "selection_result": SELECTION_RESULT,
        "route_selection_result": SELECTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "previous_review_outcome": A_VACUUM_RETRY_RESULT_REVIEW_OUTCOME,
        "previous_review_result": A_VACUUM_VARIATION_RETRY_REVIEW_RESULT,
        "a_vacuum_variation_retry_result": A_VACUUM_VARIATION_RETRY_RESULT,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "delta_F_form": DELTA_F_FORM,
        "integration_by_parts_form": INTEGRATION_BY_PARTS_FORM,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "route_selector_candidates": ROUTE_SELECTOR_CANDIDATES,
        "route_selector_comparison": ROUTE_SELECTOR_COMPARISON,
        "route_option_count": len(route_options),
        "route_options": route_options,
        "route_options_selected_count": sum(
            1 for row in route_options if row["status"] == SELECTED_ROUTE_STATUS
        ),
        "route_options_deferred_count": sum(
            1 for row in route_options if row["status"] != SELECTED_ROUTE_STATUS
        ),
        "selected_route_id": SELECTED_ROUTE_ID,
        "selected_route_label": SELECTED_ROUTE_LABEL,
        "selected_route_status": SELECTED_ROUTE_STATUS,
        "selected_route_execution_status": SELECTED_ROUTE_EXECUTION_STATUS,
        "selected_route_target": selected_next_target,
        "selected_route_reason": SELECTED_ROUTE_REASON,
        "current_coupling_target": CURRENT_COUPLING_TARGET,
        "current_conservation_target": CURRENT_CONSERVATION_TARGET,
        "a_relevant_ck_target": A_RELEVANT_CK_TARGET,
        "nonabelian_policy_target": NONABELIAN_POLICY_TARGET,
        "selection_criteria": selection_criteria,
        "selection_criteria_count": len(selection_criteria),
        "selection_criteria_accepted_count": sum(
            1 for row in selection_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "selector_prepared": accepted,
        "selector_executed": accepted,
        "route_selection_executed": accepted,
        "next_a_route_selected": accepted,
        "stress_energy_route_selected": accepted,
        "stress_energy_route_packet_authorized": accepted,
        "stress_energy_route_execution_authorized": False,
        "stress_energy_derivation_executed": False,
        "stress_energy_T_A_derived": False,
        "stress_energy_route_constructed": False,
        "stress_energy_source_admissibility_proved": False,
        "current_coupling_route_selected": False,
        "current_conservation_route_selected": False,
        "A_relevant_C_k_route_selected": False,
        "nonabelian_route_selected": False,
        "current_route_derived": False,
        "current_source_route_constructed": False,
        "matter_current_J_nu_derived": False,
        "J_nu_derived": False,
        "psi_current_route_constructed": False,
        "psi_derived_current": False,
        "external_current_policy_selected": False,
        "external_current_native_derivation_selected": False,
        "current_conservation_proved": False,
        "gauge_current_constraint_proved": False,
        "A_source_admissibility_proved": False,
        "source_admissibility_proved": False,
        "A_relevant_C_k_rules_constructed": False,
        "C_k_analogues_constructed": False,
        "source_bridge_transport_ck_analogues_constructed": False,
        "maxwell_equation_derived": False,
        "maxwell_equations_derived": False,
        "sourced_maxwell_equation_derived": False,
        "yang_mills_equations_derived": False,
        "field_equations_derived": False,
        "gauge_surface_derived": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_source_established": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "canonical_master_action_promoted": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "critical_gate_fail_conditions": [
            "execute the stress-energy metric variation",
            "derive T_A_mu_nu",
            "derive J^nu",
            "select current coupling before current policy",
            "prove current conservation",
            "construct A-relevant C_k rules",
            "select a non-Abelian route",
            "claim EM closure",
            "claim QFT-GR closure",
            "authorize semiclassical coupling",
            "promote the working-form master action",
        ],
        "downstream_progression": [
            {
                "stage": "A_route_selector_after_vacuum_u1_variation",
                "status": "SELECTED_STRESS_ENERGY_ROUTE_FOR_PACKET_PREPARATION",
                "decision": SELECTION_RESULT,
                "reason": SELECTED_ROUTE_REASON,
            },
            {
                "stage": "A_stress_energy_route_under_selected_u1_policy",
                "status": "NEXT_TARGET_AUTHORIZED_FOR_PREPARATION_ONLY",
                "decision": selected_next_target,
                "reason": (
                    "The next packet may prepare the metric-variation route "
                    "to T_A_mu_nu; derivation is not executed by this selector."
                ),
            },
        ],
        "mathematical_statement": (
            "The selector preserves the bounded U(1) vacuum route A smooth real "
            "1-form, F=dA, and nabla_mu F^{mu nu} = 0, then selects the next "
            "bounded packet: metric variation of the gauge action toward a "
            "stress-energy route. Current coupling, current conservation, "
            "A-relevant C_k rules, and non-Abelian policy remain deferred."
        ),
        "non_claim_boundary": (
            "This selector selects the A stress-energy route as the next "
            "preparation packet only. It does not execute stress-energy "
            "derivation, does not derive T_A_mu_nu, does not derive J^nu, "
            "does not select current coupling, does not prove current "
            "conservation, does not prove A-source admissibility, does not "
            "construct A-relevant C_k rules, does not select a non-Abelian "
            "route, does not close EM, does not close QFT-GR, does not "
            "authorize semiclassical coupling, does not claim empirical "
            "validation, and does not promote the master action."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeARouteSelectionAfterVacuumU1Variation",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "lane_level_lean_target_files": [
            _ptr(LEAN_PACKET_PATH),
            _ptr(QFTGR_AGGREGATE_PATH),
            _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            _ptr(RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH),
        ],
        "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        "validation_policy": _validation_policy(),
    }


def write_toe_native_a_route_selection_after_vacuum_u1_variation(
    *,
    a_vacuum_retry_result_review_path: Path = A_VACUUM_RETRY_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_a_route_selection_after_vacuum_u1_variation(
        a_vacuum_retry_result_review_path=a_vacuum_retry_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build the ToE-native A route selector after vacuum U(1) variation."
    )
    parser.add_argument(
        "--a-vacuum-retry-result-review",
        type=Path,
        default=A_VACUUM_RETRY_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_a_route_selection_after_vacuum_u1_variation(
        a_vacuum_retry_result_review_path=args.a_vacuum_retry_result_review,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
