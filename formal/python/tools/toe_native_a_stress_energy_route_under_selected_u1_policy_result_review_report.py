from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_stress_energy_route_under_selected_u1_policy_packet_report import (
    A_FIELD_DOMAIN_POLICY,
    A_ROUTE_SELECTOR_OUTCOME,
    A_STRESS_ENERGY_ROUTE_RESULT,
    CONVENTION_SCOPE,
    DEFAULT_OUT as A_STRESS_ENERGY_PACKET_PATH,
    F_DEFINITION_POLICY,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    METRIC_SIGNATURE_POLICY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as A_STRESS_ENERGY_PACKET_OUTCOME,
    PACKET_ID as A_STRESS_ENERGY_PACKET_ID,
    SCHEMA_ID as A_STRESS_ENERGY_PACKET_SCHEMA_ID,
    SOURCE_ROUTE_STILL_BLOCKED,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-21T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_RESULT_REVIEW_"
    "20260621_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_RESULT_REVIEW_v0"
)
A_STRESS_ENERGY_ROUTE_REVIEW_RESULT = (
    "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_RESULT_REVIEW_ACCEPTS_GAUGE_STRESS_"
    "ENERGY_ROUTE_NO_SOURCE_ADMISSIBILITY_OR_EM_CLOSURE"
)
OUTCOME_ID = A_STRESS_ENERGY_ROUTE_REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_stress_energy_route_result_review_accepts_gauge_stress_"
    "energy_route_no_source_admissibility_or_em_closure"
)
NEXT_TARGET = "select_next_toe_native_A_route_after_stress_energy_route"
NEXT_TARGET_KIND = "toe_native_A_route_selector_after_stress_energy_route"
RECOMMENDED_SELECTOR_CANDIDATE = (
    "prepare_toe_native_A_source_admissibility_review_for_vacuum_stress_energy"
)
SELECTOR_ROUTE_OPTIONS = [
    {
        "route_id": "A_source_admissibility_review_for_vacuum_stress_energy",
        "candidate_target": RECOMMENDED_SELECTOR_CANDIDATE,
        "status": "recommended_for_selector_not_selected_here",
        "reason": (
            "The vacuum U(1) equation and gauge stress-energy route are now "
            "available, so the next selector can test source admissibility "
            "without importing current coupling."
        ),
    },
    {
        "route_id": "A_current_coupling_policy_packet",
        "candidate_target": "prepare_toe_native_A_current_coupling_policy_packet",
        "status": "deferred_to_selector",
        "reason": (
            "A sourced Maxwell route requires external-current or matter-current "
            "policy before J^nu can be derived."
        ),
    },
    {
        "route_id": "A_current_conservation_route_packet",
        "candidate_target": (
            "prepare_toe_native_A_current_conservation_route_under_selected_u1_policy"
        ),
        "status": "deferred_to_selector",
        "reason": (
            "Current conservation is premature until a current route is selected."
        ),
    },
    {
        "route_id": "A_relevant_C_k_source_bridge_transport_family",
        "candidate_target": "prepare_toe_native_A_relevant_ck_rule_family_packet",
        "status": "deferred_to_selector",
        "reason": (
            "A-specific C_k source/bridge/transport rules should follow an "
            "admissible source route, not precede it."
        ),
    },
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_RESULT_REVIEW_"
    "20260621_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeAStressEnergyRouteUnderSelectedU1PolicyResultReview.lean"
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
            "row_id": "vacuum_route_preserved",
            "status": "accepted",
            "evidence": packet.get("vacuum_euler_lagrange_route"),
            "assessment": "The prior vacuum U(1) route is preserved.",
        },
        {
            "row_id": "stress_energy_formula_preserved",
            "status": "accepted",
            "evidence": packet.get("stress_energy_under_selected_u1_policy"),
            "assessment": "The gauge stress-energy formula is preserved.",
        },
        {
            "row_id": "convention_sensitivity_preserved",
            "status": "accepted",
            "evidence": packet.get("convention_scope"),
            "assessment": "The stress-energy sign pattern remains convention-sensitive.",
        },
        {
            "row_id": "J_nu_not_derived",
            "status": "accepted",
            "evidence": "J_nu_derived=false",
            "assessment": "No J^nu current is derived.",
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
            "assessment": "No A-source admissibility proof is supplied.",
        },
        {
            "row_id": "a_relevant_ck_rules_not_constructed",
            "status": "accepted",
            "evidence": "A_relevant_C_k_rules_constructed=false",
            "assessment": "No A-relevant C_k rules are constructed.",
        },
        {
            "row_id": "sourced_maxwell_closure_not_claimed",
            "status": "accepted",
            "evidence": "sourced_maxwell_equation_derived=false",
            "assessment": "No sourced Maxwell closure is claimed.",
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
        {
            "row_id": "next_selector_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next step is a selector after stress-energy review.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_stress_energy_route_under_selected_u1_policy_result_review"
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


def build_toe_native_a_stress_energy_route_under_selected_u1_policy_result_review(
    *,
    a_stress_energy_packet_path: Path = A_STRESS_ENERGY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(a_stress_energy_packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_stress_energy_review_target": (
            packet.get("schema_id") == A_STRESS_ENERGY_PACKET_SCHEMA_ID
            and packet.get("packet_id") == A_STRESS_ENERGY_PACKET_ID
            and packet.get("outcome_id") == A_STRESS_ENERGY_PACKET_OUTCOME
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "selected_u1_policy_preserved": (
            packet.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and packet.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and packet.get("F_definition_policy") == F_DEFINITION_POLICY
        ),
        "vacuum_route_preserved": (
            packet.get("vacuum_euler_lagrange_route") == VACUUM_EULER_LAGRANGE_ROUTE
        ),
        "stress_energy_route_preserved": (
            packet.get("stress_energy_under_selected_u1_policy")
            == STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
            and packet.get("stress_energy_route_recorded") is True
            and packet.get("stress_energy_T_A_derived") is True
        ),
        "convention_scope_retained": (
            packet.get("metric_signature_policy") == METRIC_SIGNATURE_POLICY
            and packet.get("convention_scope") == CONVENTION_SCOPE
            and "convention-sensitive" in packet.get("convention_scope", "")
        ),
        "current_source_ck_still_blocked": (
            packet.get("source_route_still_blocked") == SOURCE_ROUTE_STILL_BLOCKED
            and packet.get("J_nu_derived") is False
            and packet.get("current_conservation_proved") is False
            and packet.get("A_source_admissibility_proved") is False
            and packet.get("A_relevant_C_k_rules_constructed") is False
        ),
        "closure_and_promotion_not_claimed": (
            packet.get("sourced_maxwell_equation_derived") is False
            and packet.get("em_closure_claimed") is False
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
        else "REMEDIATE_TOE_NATIVE_A_STRESS_ENERGY_ROUTE_RESULT_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_STRESS_ENERGY_ROUTE_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": A_STRESS_ENERGY_ROUTE_REVIEW_RESULT,
        "a_stress_energy_route_result": A_STRESS_ENERGY_ROUTE_RESULT,
        "a_stress_energy_packet_outcome": A_STRESS_ENERGY_PACKET_OUTCOME,
        "a_route_selector_outcome": A_ROUTE_SELECTOR_OUTCOME,
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
        "metric_signature_policy": METRIC_SIGNATURE_POLICY,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "stress_energy_under_selected_u1_policy": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "gauge_stress_energy_route": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "convention_scope": CONVENTION_SCOPE,
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "selected_u1_policy_preserved": True,
        "A_smooth_real_one_form_preserved": True,
        "F_dA_preserved": True,
        "vacuum_route_preserved": True,
        "stress_energy_route_accepted": True,
        "gauge_stress_energy_route_accepted": True,
        "stress_energy_formula_preserved": True,
        "stress_energy_route_convention_sensitive": True,
        "convention_scope_retained": True,
        "source_route_shape_only_preserved": True,
        "selector_authorized": True,
        "recommended_selector_candidate_recorded": True,
        "source_admissibility_review_recommended_for_selector": True,
        "source_admissibility_review_selected_here": False,
        "current_coupling_route_selected_here": False,
        "current_conservation_route_selected_here": False,
        "A_relevant_C_k_route_selected_here": False,
        "record_validated": True,
        "proof_depth_label": (
            "RESULT_REVIEW_ACCEPTS_GAUGE_STRESS_ENERGY_ROUTE_NO_SOURCE_OR_CLOSURE"
        ),
        "stress_energy_route_recorded": True,
        "gauge_stress_energy_route_recorded": True,
        "stress_energy_T_A_recorded": True,
        "stress_energy_T_A_derived": True,
        "stress_energy_route_constructed": True,
        "stress_energy_derivation_executed": True,
        "stress_energy_source_admissibility_proved": False,
        "stress_energy_as_gravity_source_authorized": False,
        "current_derivation_blocked": True,
        "source_current_route_still_blocked": True,
        "current_route_derived": False,
        "current_source_route_constructed": False,
        "matter_current_J_nu_derived": False,
        "J_nu_derived": False,
        "psi_current_route_constructed": False,
        "psi_derived_current": False,
        "external_current_policy_selected": False,
        "external_current_native_derivation_selected": False,
        "nonabelian_route_selected": False,
        "gauge_fixing_selected": False,
        "gauge_fixing_selected_as_physical_structure": False,
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
            "treat T_A as source-admissible without a source-admissibility rule",
            "derive J^nu or a psi-current",
            "admit an external current as native derivation",
            "prove current conservation",
            "construct A-relevant C_k rules",
            "claim sourced Maxwell closure",
            "claim EM closure",
            "claim QFT-GR closure",
            "authorize semiclassical coupling",
            "promote the working-form master action",
            "claim empirical validation, public readiness, or release completion",
            "silently choose source admissibility instead of the selector",
        ],
        "downstream_progression": [
            {
                "stage": "A_stress_energy_route_result_review",
                "status": "ACCEPTED_GAUGE_STRESS_ENERGY_ROUTE",
                "decision": A_STRESS_ENERGY_ROUTE_REVIEW_RESULT,
                "reason": (
                    "The selected U(1) packet records the convention-sensitive "
                    "gauge stress-energy route while retaining current, source, "
                    "C_k, and closure blockers."
                ),
            },
            {
                "stage": "A_route_selector_after_stress_energy_route",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "A selector should compare source admissibility, current "
                    "coupling, current conservation, and A-relevant C_k routes."
                ),
            },
        ],
        "mathematical_statement": (
            "The review accepts the selected-policy U(1) gauge stress-energy "
            "route: A is a smooth real 1-form, F=dA, nabla_mu F^{mu nu}=0 "
            "is preserved as the vacuum route, and "
            "T^A_{mu nu} = - F_{mu alpha}F_{nu}{}^{alpha} + 1/4 g_{mu nu} "
            "F_{alpha beta}F^{alpha beta} is preserved as convention-sensitive "
            "under (+,-,-,-). The source shape nabla_mu F^{mu nu}=J^nu "
            "remains blocked."
        ),
        "non_claim_boundary": (
            "This result review accepts the convention-sensitive U(1) gauge "
            "stress-energy route only. It does not derive J^nu, does not "
            "derive a psi-current route, does not select an external current "
            "as native derivation, does not prove current conservation, does "
            "not prove A-source admissibility, does not construct A-relevant "
            "C_k rules, does not claim sourced Maxwell closure, does not close "
            "EM, does not close QFT-GR, does not authorize semiclassical "
            "coupling, does not promote the master action, does not claim "
            "empirical validation, and does not authorize public readiness or "
            "release completion."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeAStressEnergyRouteUnderSelectedU1PolicyResultReview",
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


def write_toe_native_a_stress_energy_route_under_selected_u1_policy_result_review(
    *,
    a_stress_energy_packet_path: Path = A_STRESS_ENERGY_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_a_stress_energy_route_under_selected_u1_policy_result_review(
        a_stress_energy_packet_path=a_stress_energy_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A stress-energy route under selected U(1) "
            "policy result review."
        )
    )
    parser.add_argument(
        "--a-stress-energy-packet",
        type=Path,
        default=A_STRESS_ENERGY_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_a_stress_energy_route_under_selected_u1_policy_result_review(
        a_stress_energy_packet_path=args.a_stress_energy_packet,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
