from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_surface_variation_and_source_route_result_review_report import (
    A_SURFACE_ROUTE_REVIEW_RESULT,
    DEFAULT_OUT as A_ROUTE_REVIEW_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as A_ROUTE_REVIEW_OUTCOME,
    PACKET_ID as A_ROUTE_REVIEW_PACKET_ID,
    RAW_GAUGE_ROUTE,
    RAW_VARIATION_ROUTE,
    SCHEMA_ID as A_ROUTE_REVIEW_SCHEMA_ID,
    SOURCE_FORM_ROUTE_SHAPE,
    VACUUM_ROUTE_SHAPE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-21T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_A_GAUGE_GROUP_DOMAIN_AND_CURRENT_POLICY_PACKET_20260621_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_GAUGE_GROUP_DOMAIN_AND_CURRENT_POLICY_PACKET_v0"
A_GAUGE_POLICY_DECISION = "U1_ROUTE_SELECTED_CURRENT_DERIVATION_STILL_BLOCKED"
A_GAUGE_POLICY_PACKET_RESULT = (
    "TOE_NATIVE_A_GAUGE_GROUP_DOMAIN_AND_CURRENT_POLICY_PACKET_PREPARED_"
    "U1_ROUTE_SELECTED_CURRENT_DERIVATION_STILL_BLOCKED"
)
OUTCOME_ID = A_GAUGE_POLICY_PACKET_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_gauge_group_domain_and_current_policy_packet_selects_minimal_"
    "u1_vacuum_route_and_blocks_current_derivation"
)
NEXT_TARGET = "prepare_toe_native_A_vacuum_variation_retry_under_selected_u1_policy"
NEXT_TARGET_KIND = (
    "toe_native_A_vacuum_variation_retry_under_selected_u1_policy_packet_preparation"
)
DEFERRED_CURRENT_POLICY_TARGET = "prepare_toe_native_A_current_coupling_policy_packet"
DEFERRED_A_CK_RULE_TARGET = "prepare_toe_native_A_relevant_ck_rule_family_packet"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_GAUGE_GROUP_DOMAIN_AND_CURRENT_POLICY_PACKET_20260621_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeAGaugeGroupDomainAndCurrentPolicyPacket.lean"
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

GAUGE_GROUP_POLICY = "U(1) / Abelian test route"
A_FIELD_DOMAIN_POLICY = "smooth real 1-form A on the selected spacetime domain"
F_DEFINITION_POLICY = (
    "F = dA; component form F_{mu nu} = partial_mu A_nu - partial_nu A_mu"
)
DERIVATIVE_CONVENTION_POLICY = (
    "Abelian route uses exterior derivative d for F and Levi-Civita divergence "
    "nabla_mu F^{mu nu}; non-Abelian gauge-covariant D_mu is not selected"
)
VARIATION_POLICY = "compact-support or fixed-boundary variation"
PURE_GAUGE_EQUATION_ROUTE = VACUUM_ROUTE_SHAPE
CURRENT_ROUTE_SHAPE = SOURCE_FORM_ROUTE_SHAPE
CURRENT_POLICY = (
    "current route shape recorded; current derivation blocked; psi-derived "
    "current deferred; external current not selected as native derivation"
)
GAUGE_FIXING_POLICY = (
    "no gauge fixing selected as physical structure; gauge equivalence handling "
    "is deferred"
)
CK_ROLE_POLICY = (
    "C_k remains the compatibility, bridge-admissibility, and transport-"
    "consistency layer; no A-relevant C_k rules are constructed here"
)
POLICY_ITEMS = [
    "gauge group",
    "A field/domain policy",
    "definition of F",
    "ordinary vs gauge-covariant derivative",
    "boundary variation policy",
    "pure gauge equation route",
    "current policy",
    "gauge fixing status",
    "A-relevant C_k role",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _policy_rows() -> list[dict[str, Any]]:
    return [
        {
            "policy_id": "gauge_group",
            "status": "selected_nonpromotionally",
            "decision": GAUGE_GROUP_POLICY,
            "reason": "The first A route uses the minimal Abelian test surface.",
        },
        {
            "policy_id": "A_field_domain",
            "status": "selected_for_packet_calculation",
            "decision": A_FIELD_DOMAIN_POLICY,
            "reason": "The vacuum route needs a smooth 1-form calculation domain.",
        },
        {
            "policy_id": "F_definition",
            "status": "selected_for_abelian_route",
            "decision": F_DEFINITION_POLICY,
            "reason": "The U(1) route fixes F as dA without non-Abelian curvature terms.",
        },
        {
            "policy_id": "derivative_convention",
            "status": "selected_for_abelian_vacuum_route",
            "decision": DERIVATIVE_CONVENTION_POLICY,
            "reason": "The packet selects nabla_mu F^{mu nu} for the Abelian route only.",
        },
        {
            "policy_id": "boundary_variation_policy",
            "status": "selected_for_future_variation_retry",
            "decision": VARIATION_POLICY,
            "reason": "The future variation retry needs boundary terms fixed or removed.",
        },
        {
            "policy_id": "pure_gauge_equation_route",
            "status": "selected_as_future_vacuum_route_shape_not_derived",
            "decision": PURE_GAUGE_EQUATION_ROUTE,
            "reason": "The pure gauge term naturally routes to the vacuum equation shape.",
        },
        {
            "policy_id": "current_policy",
            "status": "blocked_pending_external_or_matter_coupling_policy",
            "decision": CURRENT_POLICY,
            "reason": "A source equation requires external current or matter coupling.",
        },
        {
            "policy_id": "gauge_fixing_status",
            "status": "not_selected_as_physical_structure",
            "decision": GAUGE_FIXING_POLICY,
            "reason": "Gauge fixing is not physical structure for this policy packet.",
        },
        {
            "policy_id": "A_relevant_C_k_role",
            "status": "blocked_pending_A_relevant_ck_rule_construction",
            "decision": CK_ROLE_POLICY,
            "reason": "C_k content remains a separate compatibility/admissibility task.",
        },
    ]


def _review_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_expected_gauge_policy_packet_target",
            "status": "accepted",
            "evidence": review.get("selected_next_target"),
            "assessment": "The A route result review authorized this policy packet.",
        },
        {
            "row_id": "u1_abelian_route_selected",
            "status": "accepted",
            "evidence": GAUGE_GROUP_POLICY,
            "assessment": "The packet selects the minimal U(1)/Abelian test route.",
        },
        {
            "row_id": "A_smooth_real_one_form_domain_selected",
            "status": "accepted",
            "evidence": A_FIELD_DOMAIN_POLICY,
            "assessment": "A is treated as a smooth real 1-form on the selected domain.",
        },
        {
            "row_id": "F_definition_selected",
            "status": "accepted",
            "evidence": F_DEFINITION_POLICY,
            "assessment": "F is fixed as dA in component form.",
        },
        {
            "row_id": "abelian_derivative_convention_selected",
            "status": "accepted",
            "evidence": DERIVATIVE_CONVENTION_POLICY,
            "assessment": "The Abelian divergence route is selected; non-Abelian D_mu is not.",
        },
        {
            "row_id": "boundary_variation_policy_selected",
            "status": "accepted",
            "evidence": VARIATION_POLICY,
            "assessment": "Compact-support or fixed-boundary variation is selected.",
        },
        {
            "row_id": "pure_gauge_vacuum_route_recorded",
            "status": "accepted",
            "evidence": PURE_GAUGE_EQUATION_ROUTE,
            "assessment": "The vacuum route shape is recorded for the future retry.",
        },
        {
            "row_id": "current_route_shape_recorded_derivation_blocked",
            "status": "accepted",
            "evidence": CURRENT_ROUTE_SHAPE,
            "assessment": "The source-current route remains shape only.",
        },
        {
            "row_id": "external_current_not_selected_as_native_derivation",
            "status": "accepted",
            "evidence": "external_current_policy_selected=false",
            "assessment": "No external current policy is admitted as native derivation.",
        },
        {
            "row_id": "psi_derived_current_deferred",
            "status": "accepted",
            "evidence": "psi_derived_current_deferred=true",
            "assessment": "Matter-derived current from psi/A coupling is deferred.",
        },
        {
            "row_id": "nonabelian_route_not_selected",
            "status": "accepted",
            "evidence": "nonabelian_route_selected=false",
            "assessment": "The packet does not select a non-Abelian gauge route.",
        },
        {
            "row_id": "gauge_fixing_not_selected_as_physical_structure",
            "status": "accepted",
            "evidence": GAUGE_FIXING_POLICY,
            "assessment": "Gauge fixing is not selected as physical structure.",
        },
        {
            "row_id": "no_derivation_closure_or_promotion",
            "status": "accepted",
            "evidence": [
                "maxwell_equation_derived=false",
                "current_conservation_proved=false",
                "em_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "The packet remains policy-only and nonpromotional.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_A_gauge_group_domain_and_current_policy_packet",
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


def build_toe_native_a_gauge_group_domain_and_current_policy_packet(
    *,
    a_route_review_path: Path = A_ROUTE_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(a_route_review_path)
    policy_rows = _policy_rows()
    review_criteria = _review_criteria(review)
    acceptance_criteria = {
        "consumes_expected_gauge_policy_packet_target": (
            review.get("schema_id") == A_ROUTE_REVIEW_SCHEMA_ID
            and review.get("packet_id") == A_ROUTE_REVIEW_PACKET_ID
            and review.get("outcome_id") == A_ROUTE_REVIEW_OUTCOME
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "raw_routes_preserved_from_review": (
            review.get("raw_gauge_route") == RAW_GAUGE_ROUTE
            and review.get("raw_variation_route") == RAW_VARIATION_ROUTE
            and review.get("source_form_route_shape") == SOURCE_FORM_ROUTE_SHAPE
        ),
        "u1_abelian_route_selected": "U(1)" in GAUGE_GROUP_POLICY,
        "A_domain_policy_selected": "smooth real 1-form" in A_FIELD_DOMAIN_POLICY,
        "F_definition_selected": "F = dA" in F_DEFINITION_POLICY,
        "abelian_derivative_convention_selected": (
            "nabla_mu F^{mu nu}" in DERIVATIVE_CONVENTION_POLICY
            and "D_mu is not selected" in DERIVATIVE_CONVENTION_POLICY
        ),
        "boundary_variation_policy_selected": "fixed-boundary" in VARIATION_POLICY,
        "pure_gauge_vacuum_route_selected": PURE_GAUGE_EQUATION_ROUTE == VACUUM_ROUTE_SHAPE,
        "current_derivation_still_blocked": (
            "current derivation blocked" in CURRENT_POLICY
            and "psi-derived current deferred" in CURRENT_POLICY
            and "external current not selected" in CURRENT_POLICY
        ),
        "no_derivation_or_closure_claim": (
            review.get("maxwell_equations_derived") is False
            and review.get("current_conservation_proved") is False
            and review.get("qft_gr_closure_claimed") is False
            and review.get("master_action_promoted") is False
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "next_target_is_vacuum_variation_retry": NEXT_TARGET
        == "prepare_toe_native_A_vacuum_variation_retry_under_selected_u1_policy",
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_TOE_NATIVE_A_GAUGE_GROUP_DOMAIN_AND_CURRENT_POLICY_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_GAUGE_GROUP_DOMAIN_CURRENT_POLICY_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "TOE_NATIVE_A_GAUGE_GROUP_DOMAIN_AND_CURRENT_POLICY_PACKET_REQUIRES_REMEDIATION",
        "a_gauge_policy_decision": A_GAUGE_POLICY_DECISION,
        "a_gauge_policy_packet_result": A_GAUGE_POLICY_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "deferred_current_policy_target": DEFERRED_CURRENT_POLICY_TARGET,
        "deferred_A_ck_rule_target": DEFERRED_A_CK_RULE_TARGET,
        "review_result": A_SURFACE_ROUTE_REVIEW_RESULT,
        "reviewed_a_route_result_review_artifact_id": review.get("schema_id"),
        "reviewed_a_route_result_review_outcome": review.get("outcome_id"),
        "policy_status": "minimal_abelian_policy_selected_current_derivation_blocked",
        "policy_items": policy_rows,
        "policy_item_count": len(policy_rows),
        "policy_selected_count": sum(
            1 for row in policy_rows if not row["status"].startswith("blocked")
        ),
        "policy_blocked_count": sum(
            1 for row in policy_rows if row["status"].startswith("blocked")
        ),
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "selected_gauge_group": "U(1)",
        "minimal_abelian_route_selected": True,
        "u1_route_selected": True,
        "nonabelian_route_selected": False,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "A_as_smooth_real_one_form_selected": True,
        "bundle_domain_for_A_selected": True,
        "F_definition_policy": F_DEFINITION_POLICY,
        "definition_of_F_selected": True,
        "derivative_convention_policy": DERIVATIVE_CONVENTION_POLICY,
        "abelian_covariant_divergence_selected": True,
        "gauge_covariant_D_mu_route_selected": False,
        "covariant_derivative_D_mu_convention_selected": False,
        "variation_policy": VARIATION_POLICY,
        "boundary_variation_policy_selected": True,
        "boundary_terms_controlled": False,
        "pure_gauge_equation_route": PURE_GAUGE_EQUATION_ROUTE,
        "pure_gauge_vacuum_route_selected": True,
        "vacuum_variation_retry_authorized": prepared,
        "vacuum_variation_retry_executed": False,
        "current_route_shape": CURRENT_ROUTE_SHAPE,
        "source_form_route_shape": CURRENT_ROUTE_SHAPE,
        "current_route_shape_recorded": True,
        "current_policy": CURRENT_POLICY,
        "current_derivation_blocked": True,
        "current_route_derived": False,
        "external_current_policy_selected": False,
        "external_current_not_selected_as_native_derivation": True,
        "psi_derived_current_deferred": True,
        "matter_current_J_nu_derived": False,
        "gauge_fixing_policy": GAUGE_FIXING_POLICY,
        "gauge_fixing_selected": False,
        "gauge_fixing_selected_as_physical_structure": False,
        "ck_role_policy": CK_ROLE_POLICY,
        "C_k_analogues_constructed": False,
        "A_relevant_C_k_rules_constructed": False,
        "source_bridge_transport_ck_analogues_constructed": False,
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "policy_contract_recorded": True,
        "formal_theorem_backed_gauge_derivation": False,
        "record_validated": True,
        "symbolic_calculation_recorded": False,
        "native_derivation_blocked": True,
        "proof_depth_label": "POLICY_SELECTION_RECORDED_NO_GAUGE_DERIVATION",
        "a_surface_variation_executed": False,
        "a_surface_variation_route_executed": False,
        "maxwell_equation_derived": False,
        "maxwell_equations_derived": False,
        "yang_mills_equations_derived": False,
        "field_equations_derived": False,
        "gauge_field_derived": False,
        "gauge_surface_derived": False,
        "current_source_route_constructed": False,
        "current_conservation_proved": False,
        "gauge_current_constraint_proved": False,
        "stress_energy_T_A_derived": False,
        "stress_energy_route_constructed": False,
        "stress_energy_source_admissibility_proved": False,
        "A_source_admissibility_proved": False,
        "source_admissibility_proved": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "source_map_closed": False,
        "toe_native_gauge_derivation_claimed": False,
        "toe_native_A_source_route_constructed": False,
        "toe_native_A_source_admissibility_claimed": False,
        "toe_native_A_current_conservation_claimed": False,
        "toe_native_matter_derivation_claimed": False,
        "standard_model_derivation_claimed": False,
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
            "treat U(1) policy selection as a Maxwell derivation",
            "derive J^nu without external-current or matter-coupling policy",
            "claim current conservation",
            "select gauge fixing as physical structure",
            "select a non-Abelian gauge route",
            "derive T_A or A-source admissibility",
            "construct A-relevant C_k rules",
            "claim EM or QFT-GR closure",
            "promote the working-form master action",
            "claim empirical validation, public readiness, or release completion",
        ],
        "downstream_progression": [
            {
                "stage": "A_gauge_group_domain_current_policy_packet",
                "status": "U1_ROUTE_SELECTED_CURRENT_DERIVATION_STILL_BLOCKED",
                "decision": A_GAUGE_POLICY_DECISION,
                "reason": (
                    "The minimal Abelian policy is fixed for the first A route, "
                    "while current coupling remains unselected."
                ),
            },
            {
                "stage": "A_vacuum_variation_retry_under_selected_u1_policy",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The next packet may test the pure gauge vacuum route under "
                    "the selected U(1), A-domain, F-definition, derivative, and "
                    "boundary-variation policy."
                ),
            },
            {
                "stage": "A_current_coupling_policy",
                "status": "RETAINED_DEFERRED",
                "decision": DEFERRED_CURRENT_POLICY_TARGET,
                "reason": "J^nu requires external-current or psi/A matter-coupling policy.",
            },
            {
                "stage": "A_relevant_C_k_rule_family",
                "status": "RETAINED_DEFERRED",
                "decision": DEFERRED_A_CK_RULE_TARGET,
                "reason": "A-specific C_k source/bridge/transport rules are not constructed here.",
            },
        ],
        "mathematical_statement": (
            "This policy packet fixes the first ToE-native A-route calculation "
            "policy as a minimal U(1)/Abelian test route: A is a smooth real "
            "1-form on the selected spacetime domain, F = dA with components "
            "F_{mu nu} = partial_mu A_nu - partial_nu A_mu, and the Abelian "
            "vacuum route uses nabla_mu F^{mu nu}. Compact-support or fixed-"
            "boundary variation is selected for the future vacuum retry. The "
            "source-current equation nabla_mu F^{mu nu} = J^nu remains route "
            "shape only because no external-current policy or psi/A matter-"
            "coupling current is selected."
        ),
        "non_claim_boundary": (
            "This policy packet selects the minimal Abelian U(1) test route only. "
            "It does not derive Maxwell equations, does not derive J^nu, does "
            "not prove current conservation, does not select gauge fixing as "
            "physical structure, does not select a non-Abelian route, does not "
            "derive stress-energy T_A, does not prove A-source admissibility, "
            "does not construct A-relevant C_k rules, does not close EM, does "
            "not close QFT-GR, does not authorize semiclassical coupling, does "
            "not promote the master action, does not claim empirical validation, "
            "and does not authorize public readiness or release completion."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeAGaugeGroupDomainAndCurrentPolicyPacket",
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


def write_toe_native_a_gauge_group_domain_and_current_policy_packet(
    *,
    a_route_review_path: Path = A_ROUTE_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_a_gauge_group_domain_and_current_policy_packet(
        a_route_review_path=a_route_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A gauge group/domain/current policy packet."
        )
    )
    parser.add_argument("--a-route-review", type=Path, default=A_ROUTE_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_a_gauge_group_domain_and_current_policy_packet(
        a_route_review_path=args.a_route_review,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
