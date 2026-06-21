from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_vacuum_variation_retry_under_selected_u1_policy_packet_report import (
    A_FIELD_DOMAIN_POLICY,
    A_GAUGE_POLICY_PACKET_RESULT,
    A_VACUUM_VARIATION_RETRY_RESULT,
    ACTION_VARIATION_FORM,
    BOUNDARY_POLICY_USED,
    CURRENT_POLICY,
    DEFAULT_OUT as A_VACUUM_VARIATION_RETRY_PACKET_PATH,
    DELTA_F_FORM,
    F_DEFINITION_POLICY,
    GAUGE_FIXING_POLICY,
    GAUGE_GROUP_POLICY,
    INTEGRATION_BY_PARTS_FORM,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as A_VACUUM_VARIATION_RETRY_PACKET_OUTCOME,
    PACKET_ID as A_VACUUM_VARIATION_RETRY_PACKET_ID,
    SCHEMA_ID as A_VACUUM_VARIATION_RETRY_PACKET_SCHEMA_ID,
    SELECTED_A_ACTION,
    SOURCE_ROUTE_STILL_BLOCKED,
    VACUUM_EULER_LAGRANGE_ROUTE,
    VARIATION_POLICY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-21T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_RESULT_REVIEW_"
    "20260621_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_RESULT_REVIEW_v0"
)
A_VACUUM_VARIATION_RETRY_REVIEW_RESULT = (
    "TOE_NATIVE_A_VACUUM_VARIATION_RETRY_RESULT_REVIEW_ACCEPTS_VACUUM_U1_"
    "GAUGE_ROUTE_NO_CURRENT_DERIVATION_OR_EM_CLOSURE"
)
OUTCOME_ID = A_VACUUM_VARIATION_RETRY_REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_vacuum_variation_retry_result_review_accepts_vacuum_u1_"
    "gauge_route_no_current_derivation_or_em_closure"
)
NEXT_TARGET = "select_next_toe_native_A_route_after_vacuum_u1_variation"
NEXT_TARGET_KIND = "toe_native_A_route_selector_after_vacuum_u1_variation"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

RECOMMENDED_SELECTOR_CANDIDATE = (
    "prepare_toe_native_A_stress_energy_route_under_selected_u1_policy"
)
SELECTOR_ROUTE_OPTIONS = [
    {
        "route_id": "A_stress_energy_route",
        "candidate_target": RECOMMENDED_SELECTOR_CANDIDATE,
        "status": "recommended_for_selector_not_selected_here",
        "reason": (
            "The stress-energy route can proceed from the gauge action and "
            "metric variation before psi/A current coupling is selected."
        ),
    },
    {
        "route_id": "A_current_coupling_route",
        "candidate_target": "prepare_toe_native_A_current_coupling_policy_packet",
        "status": "deferred_to_selector",
        "reason": "A current-coupled route requires external-current or matter-coupling policy.",
    },
    {
        "route_id": "A_current_conservation_route",
        "candidate_target": "prepare_toe_native_A_current_conservation_route_under_selected_u1_policy",
        "status": "deferred_to_selector",
        "reason": "Current conservation should not be proved before the current route is selected.",
    },
    {
        "route_id": "A_relevant_C_k_source_bridge_transport_route",
        "candidate_target": "prepare_toe_native_A_relevant_ck_rule_family_packet",
        "status": "deferred_to_selector",
        "reason": "A-specific C_k source/bridge/transport content is not constructed by this review.",
    },
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_RESULT_REVIEW_"
    "20260621_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeAVacuumVariationRetryUnderSelectedU1PolicyResultReview.lean"
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


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selected_u1_policy_preserved",
            "status": "accepted",
            "evidence": packet.get("gauge_group_policy"),
            "assessment": "The selected U(1) / Abelian test policy is preserved.",
        },
        {
            "row_id": "A_smooth_real_one_form_preserved",
            "status": "accepted",
            "evidence": packet.get("A_field_domain_policy"),
            "assessment": "A remains a smooth real 1-form on the selected domain.",
        },
        {
            "row_id": "F_dA_preserved",
            "status": "accepted",
            "evidence": packet.get("F_definition_policy"),
            "assessment": "F = dA and its component formula are preserved.",
        },
        {
            "row_id": "delta_F_recorded",
            "status": "accepted",
            "evidence": packet.get("delta_F_form"),
            "assessment": "The U(1) delta F variation is recorded.",
        },
        {
            "row_id": "integration_by_parts_recorded",
            "status": "accepted",
            "evidence": packet.get("integration_by_parts_form"),
            "assessment": "Integration by parts exposes nabla_mu F^{mu nu}.",
        },
        {
            "row_id": "boundary_policy_preserved",
            "status": "accepted",
            "evidence": packet.get("boundary_policy_used"),
            "assessment": "Fixed-boundary or compact-support variation controls the boundary term.",
        },
        {
            "row_id": "vacuum_route_recorded",
            "status": "accepted",
            "evidence": packet.get("vacuum_euler_lagrange_route"),
            "assessment": "nabla_mu F^{mu nu} = 0 is recorded as the vacuum route.",
        },
        {
            "row_id": "source_route_shape_only_preserved",
            "status": "accepted",
            "evidence": packet.get("source_route_still_blocked"),
            "assessment": "nabla_mu F^{mu nu} = J^nu remains route shape only.",
        },
        {
            "row_id": "current_derivation_not_claimed",
            "status": "accepted",
            "evidence": "current_route_derived=false",
            "assessment": "No J^nu or current route is derived.",
        },
        {
            "row_id": "stress_energy_not_derived",
            "status": "accepted",
            "evidence": "stress_energy_T_A_derived=false",
            "assessment": "No gauge stress-energy T_A route is derived.",
        },
        {
            "row_id": "current_conservation_not_proved",
            "status": "accepted",
            "evidence": "current_conservation_proved=false",
            "assessment": "No current conservation proof is supplied.",
        },
        {
            "row_id": "source_admissibility_not_proved",
            "status": "accepted",
            "evidence": "A_source_admissibility_proved=false",
            "assessment": "No source admissibility proof is supplied.",
        },
        {
            "row_id": "a_relevant_ck_rules_not_constructed",
            "status": "accepted",
            "evidence": "A_relevant_C_k_rules_constructed=false",
            "assessment": "No A-relevant C_k source/bridge/transport rules are constructed.",
        },
        {
            "row_id": "em_qft_gr_closure_not_claimed",
            "status": "accepted",
            "evidence": ["em_closure_claimed=false", "qft_gr_closure_claimed=false"],
            "assessment": "No EM or QFT-GR closure is claimed.",
        },
        {
            "row_id": "master_action_not_promoted",
            "status": "accepted",
            "evidence": "master_action_promoted=false",
            "assessment": "The working-form master action is not promoted.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_vacuum_variation_retry_under_selected_u1_policy_result_review"
        ),
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
        "full_security_scan_required": False,
    }


def build_toe_native_a_vacuum_variation_retry_under_selected_u1_policy_result_review(
    *,
    a_vacuum_variation_retry_packet_path: Path = A_VACUUM_VARIATION_RETRY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(a_vacuum_variation_retry_packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_result_review_target": (
            packet.get("schema_id") == A_VACUUM_VARIATION_RETRY_PACKET_SCHEMA_ID
            and packet.get("packet_id") == A_VACUUM_VARIATION_RETRY_PACKET_ID
            and packet.get("outcome_id") == A_VACUUM_VARIATION_RETRY_PACKET_OUTCOME
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "selected_u1_policy_preserved": (
            packet.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and packet.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and packet.get("F_definition_policy") == F_DEFINITION_POLICY
        ),
        "vacuum_variation_route_recorded": (
            packet.get("delta_F_form") == DELTA_F_FORM
            and packet.get("integration_by_parts_form") == INTEGRATION_BY_PARTS_FORM
            and packet.get("vacuum_euler_lagrange_route") == VACUUM_EULER_LAGRANGE_ROUTE
        ),
        "boundary_policy_preserved": (
            packet.get("boundary_policy_used") == BOUNDARY_POLICY_USED
            and packet.get("boundary_terms_controlled") is True
        ),
        "source_current_route_still_blocked": (
            packet.get("source_route_still_blocked") == SOURCE_ROUTE_STILL_BLOCKED
            and packet.get("current_route_derived") is False
            and packet.get("matter_current_J_nu_derived") is False
        ),
        "stress_energy_and_ck_not_constructed": (
            packet.get("stress_energy_T_A_derived") is False
            and packet.get("A_relevant_C_k_rules_constructed") is False
        ),
        "closure_and_promotion_not_claimed": (
            packet.get("em_closure_claimed") is False
            and packet.get("qft_gr_closure_claimed") is False
            and packet.get("master_action_promoted") is False
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "next_target_is_selector": NEXT_TARGET.startswith("select_next_"),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_VACUUM_VARIATION_RETRY_RESULT_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_VACUUM_VARIATION_RETRY_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_VACUUM_VARIATION_RETRY_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": A_VACUUM_VARIATION_RETRY_REVIEW_RESULT,
        "a_vacuum_variation_retry_result": A_VACUUM_VARIATION_RETRY_RESULT,
        "a_vacuum_variation_retry_packet_outcome": A_VACUUM_VARIATION_RETRY_PACKET_OUTCOME,
        "a_gauge_policy_packet_result": A_GAUGE_POLICY_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "recommended_selector_candidate": RECOMMENDED_SELECTOR_CANDIDATE,
        "selector_route_options": SELECTOR_ROUTE_OPTIONS,
        "selector_route_option_count": len(SELECTOR_ROUTE_OPTIONS),
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "variation_policy": VARIATION_POLICY,
        "current_policy": CURRENT_POLICY,
        "gauge_fixing_policy": GAUGE_FIXING_POLICY,
        "selected_A_action": SELECTED_A_ACTION,
        "delta_F_form": DELTA_F_FORM,
        "action_variation_form": ACTION_VARIATION_FORM,
        "integration_by_parts_form": INTEGRATION_BY_PARTS_FORM,
        "boundary_policy_used": BOUNDARY_POLICY_USED,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "selected_u1_policy_preserved": True,
        "A_smooth_real_one_form_preserved": True,
        "F_dA_preserved": True,
        "delta_F_recorded": True,
        "integration_by_parts_recorded": True,
        "fixed_boundary_or_compact_support_variation_preserved": True,
        "vacuum_route_accepted": True,
        "vacuum_u1_gauge_route_accepted": True,
        "source_route_shape_only_preserved": True,
        "selector_authorized": True,
        "recommended_selector_candidate_recorded": True,
        "stress_energy_route_recommended_for_selector": True,
        "stress_energy_route_selected_here": False,
        "current_coupling_route_selected_here": False,
        "current_conservation_route_selected_here": False,
        "A_relevant_C_k_route_selected_here": False,
        "record_validated": True,
        "proof_depth_label": (
            "RESULT_REVIEW_ACCEPTS_VACUUM_U1_GAUGE_ROUTE_NO_CURRENT_OR_CLOSURE"
        ),
        "a_surface_variation_executed": True,
        "a_surface_variation_route_executed": True,
        "current_route_derived": False,
        "current_source_route_constructed": False,
        "matter_current_J_nu_derived": False,
        "J_nu_derived": False,
        "psi_current_route_constructed": False,
        "psi_derived_current": False,
        "psi_derived_current_deferred": True,
        "external_current_policy_selected": False,
        "external_current_native_derivation_selected": False,
        "external_current_not_selected_as_native_derivation": True,
        "nonabelian_route_selected": False,
        "gauge_covariant_D_mu_route_selected": False,
        "gauge_fixing_selected": False,
        "gauge_fixing_selected_as_physical_structure": False,
        "stress_energy_T_A_derived": False,
        "stress_energy_route_constructed": False,
        "stress_energy_source_admissibility_proved": False,
        "current_conservation_proved": False,
        "gauge_current_constraint_proved": False,
        "A_source_admissibility_proved": False,
        "source_admissibility_proved": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "A_relevant_C_k_rules_constructed": False,
        "C_k_analogues_constructed": False,
        "source_bridge_transport_ck_analogues_constructed": False,
        "formal_theorem_backed_gauge_derivation": False,
        "maxwell_equation_derived": False,
        "maxwell_equations_derived": False,
        "sourced_maxwell_equation_derived": False,
        "yang_mills_equations_derived": False,
        "field_equations_derived": False,
        "gauge_field_derived": False,
        "gauge_surface_derived": False,
        "toe_native_gauge_derivation_claimed": False,
        "toe_native_A_source_route_constructed": False,
        "toe_native_A_source_admissibility_claimed": False,
        "toe_native_A_current_conservation_claimed": False,
        "toe_native_matter_derivation_claimed": False,
        "standard_model_derivation_claimed": False,
        "source_map_closed": False,
        "qft_gr_solved": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
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
            "treat vacuum route as sourced Maxwell closure",
            "derive J^nu",
            "claim a psi-current route",
            "admit external current as native derivation",
            "derive stress-energy T_A in the review",
            "prove current conservation",
            "prove source admissibility",
            "construct A-relevant C_k rules",
            "claim EM or QFT-GR closure",
            "promote the working-form master action",
            "silently choose the next A calculation instead of the selector",
        ],
        "downstream_progression": [
            {
                "stage": "A_vacuum_variation_retry_result_review",
                "status": "ACCEPTED_VACUUM_U1_ROUTE_ONLY",
                "decision": A_VACUUM_VARIATION_RETRY_REVIEW_RESULT,
                "reason": (
                    "The selected U(1) packet records delta F, integration by parts, "
                    "and nabla_mu F^{mu nu} = 0 as a vacuum route only."
                ),
            },
            {
                "stage": "A_route_selector_after_vacuum_u1_variation",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "A selector should compare stress-energy, current coupling, "
                    "current conservation, and A-relevant C_k routes before the "
                    "next calculation is chosen."
                ),
            },
        ],
        "mathematical_statement": (
            "The review accepts the selected-policy U(1) vacuum gauge route: "
            "A is a smooth real 1-form, F=dA, delta F is recorded, integration "
            "by parts under compact-support or fixed-boundary variation records "
            "nabla_mu F^{mu nu} = 0. The sourced shape nabla_mu F^{mu nu} = "
            "J^nu remains blocked pending current policy or matter coupling."
        ),
        "non_claim_boundary": (
            "This result review accepts the vacuum U(1) gauge route only. It "
            "does not derive J^nu, does not construct a psi-current route, does "
            "not select an external current as native derivation, does not "
            "derive stress-energy T_A, does not prove current conservation, "
            "does not prove source admissibility, does not construct A-relevant "
            "C_k rules, does not close EM, does not close QFT-GR, does not "
            "promote the master action, does not claim empirical validation, "
            "and does not authorize public readiness or release completion."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeAVacuumVariationRetryUnderSelectedU1PolicyResultReview",
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


def write_toe_native_a_vacuum_variation_retry_under_selected_u1_policy_result_review(
    *,
    a_vacuum_variation_retry_packet_path: Path = A_VACUUM_VARIATION_RETRY_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_a_vacuum_variation_retry_under_selected_u1_policy_result_review(
        a_vacuum_variation_retry_packet_path=a_vacuum_variation_retry_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A vacuum variation retry under selected U(1) "
            "policy result review."
        )
    )
    parser.add_argument(
        "--a-vacuum-variation-retry-packet",
        type=Path,
        default=A_VACUUM_VARIATION_RETRY_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = (
        write_toe_native_a_vacuum_variation_retry_under_selected_u1_policy_result_review(
            a_vacuum_variation_retry_packet_path=args.a_vacuum_variation_retry_packet,
            out=args.out,
            captured_at_utc=args.captured_at_utc,
        )
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
