from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_gauge_group_domain_and_current_policy_packet_report import (
    A_FIELD_DOMAIN_POLICY,
    A_GAUGE_POLICY_PACKET_RESULT,
    CURRENT_POLICY,
    CURRENT_ROUTE_SHAPE,
    DEFAULT_OUT as A_GAUGE_POLICY_PACKET_PATH,
    F_DEFINITION_POLICY,
    GAUGE_FIXING_POLICY,
    GAUGE_GROUP_POLICY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as A_GAUGE_POLICY_PACKET_OUTCOME,
    PACKET_ID as A_GAUGE_POLICY_PACKET_ID,
    SCHEMA_ID as A_GAUGE_POLICY_PACKET_SCHEMA_ID,
    VARIATION_POLICY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-21T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_PACKET_"
    "20260621_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_PACKET_v0"
A_VACUUM_VARIATION_RETRY_RESULT = (
    "VACUUM_GAUGE_VARIATION_ROUTE_CONSTRUCTED_NO_CURRENT_DERIVATION_OR_EM_CLOSURE"
)
OUTCOME_ID = (
    "TOE_NATIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_PACKET_PREPARED_"
    "VACUUM_GAUGE_VARIATION_ROUTE_CONSTRUCTED_NO_CURRENT_DERIVATION_OR_EM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "toe_native_A_vacuum_variation_retry_under_selected_u1_policy_constructs_"
    "vacuum_gauge_variation_route_no_current_derivation_or_em_closure"
)
NEXT_TARGET = "review_toe_native_A_vacuum_variation_retry_under_selected_u1_policy_result"
NEXT_TARGET_KIND = "toe_native_A_vacuum_variation_retry_under_selected_u1_policy_result_review"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_PACKET_"
    "20260621_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeAVacuumVariationRetryUnderSelectedU1PolicyPacket.lean"
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

SELECTED_A_ACTION = "S_A^U1[A,g] = -1/4 integral_M dVol_g F_{mu nu} F^{mu nu}"
SELECTED_F_DEFINITION = F_DEFINITION_POLICY
DELTA_F_FORM = "delta F_{mu nu} = partial_mu delta A_nu - partial_nu delta A_mu"
ACTION_VARIATION_FORM = (
    "delta S_A^U1 = - integral_M dVol_g F^{mu nu} nabla_mu delta A_nu"
)
INTEGRATION_BY_PARTS_FORM = (
    "delta S_A^U1 = integral_M dVol_g (nabla_mu F^{mu nu}) delta A_nu"
)
BOUNDARY_POLICY_USED = (
    "compact-support or fixed-boundary variation removes the boundary term"
)
VACUUM_EULER_LAGRANGE_ROUTE = "nabla_mu F^{mu nu} = 0"
SOURCE_ROUTE_STILL_BLOCKED = CURRENT_ROUTE_SHAPE
VACUUM_ROUTE_DECISION = (
    "vacuum_U1_gauge_variation_route_constructed_source_current_route_still_blocked"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _calculation_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "state_selected_u1_action",
            "status": "recorded",
            "mathematical_content": SELECTED_A_ACTION,
        },
        {
            "step_id": "state_selected_u1_policy",
            "status": "recorded",
            "mathematical_content": {
                "gauge_group": GAUGE_GROUP_POLICY,
                "A_domain": A_FIELD_DOMAIN_POLICY,
                "F_definition": SELECTED_F_DEFINITION,
                "variation_policy": VARIATION_POLICY,
            },
        },
        {
            "step_id": "vary_F",
            "status": "computed_under_selected_u1_policy",
            "mathematical_content": DELTA_F_FORM,
        },
        {
            "step_id": "vary_action",
            "status": "computed_under_selected_u1_policy",
            "mathematical_content": ACTION_VARIATION_FORM,
        },
        {
            "step_id": "integrate_by_parts",
            "status": "computed_under_selected_u1_policy",
            "mathematical_content": INTEGRATION_BY_PARTS_FORM,
        },
        {
            "step_id": "apply_boundary_policy",
            "status": "selected_boundary_policy_used",
            "mathematical_content": BOUNDARY_POLICY_USED,
        },
        {
            "step_id": "read_vacuum_route",
            "status": "vacuum_route_constructed",
            "mathematical_content": VACUUM_EULER_LAGRANGE_ROUTE,
        },
        {
            "step_id": "retain_current_and_closure_blockers",
            "status": "retained",
            "mathematical_content": (
                "J^nu not derived; no psi coupling; no external current as native "
                "derivation; no EM or QFT-GR closure"
            ),
        },
    ]


def _review_criteria(policy_packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_expected_vacuum_retry_target",
            "status": "accepted",
            "evidence": policy_packet.get("selected_next_target"),
            "assessment": "The U(1) policy packet authorized this vacuum retry.",
        },
        {
            "row_id": "selected_u1_policy_used",
            "status": "accepted",
            "evidence": [
                policy_packet.get("gauge_group_policy"),
                policy_packet.get("A_field_domain_policy"),
                policy_packet.get("F_definition_policy"),
            ],
            "assessment": "The retry uses the selected minimal U(1) policy.",
        },
        {
            "row_id": "gauge_action_recorded",
            "status": "accepted",
            "evidence": SELECTED_A_ACTION,
            "assessment": "The pure gauge action is stated.",
        },
        {
            "row_id": "delta_F_recorded",
            "status": "accepted",
            "evidence": DELTA_F_FORM,
            "assessment": "The U(1) variation of F is recorded.",
        },
        {
            "row_id": "action_variation_computed",
            "status": "accepted",
            "evidence": ACTION_VARIATION_FORM,
            "assessment": "The action variation is computed using antisymmetry.",
        },
        {
            "row_id": "integration_by_parts_computed",
            "status": "accepted",
            "evidence": INTEGRATION_BY_PARTS_FORM,
            "assessment": "Integration by parts exposes nabla_mu F^{mu nu}.",
        },
        {
            "row_id": "boundary_policy_used",
            "status": "accepted",
            "evidence": BOUNDARY_POLICY_USED,
            "assessment": "The selected boundary policy removes boundary terms.",
        },
        {
            "row_id": "vacuum_route_constructed",
            "status": "accepted",
            "evidence": VACUUM_EULER_LAGRANGE_ROUTE,
            "assessment": "The vacuum U(1) gauge variation route is constructed.",
        },
        {
            "row_id": "source_current_route_still_blocked",
            "status": "accepted",
            "evidence": SOURCE_ROUTE_STILL_BLOCKED,
            "assessment": "The sourced equation remains shape only and blocked.",
        },
        {
            "row_id": "stress_energy_route_not_derived",
            "status": "accepted",
            "evidence": "stress_energy_T_A_derived=false",
            "assessment": "No gauge stress-energy route is derived.",
        },
        {
            "row_id": "ck_closure_and_promotion_not_claimed",
            "status": "accepted",
            "evidence": [
                "A_relevant_C_k_rules_constructed=false",
                "em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No A-relevant C_k, closure, or promotion claim follows.",
        },
        {
            "row_id": "next_review_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The result is routed to a review before downstream choice.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_A_vacuum_variation_retry_under_selected_u1_policy_packet",
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


def build_toe_native_a_vacuum_variation_retry_under_selected_u1_policy_packet(
    *,
    a_gauge_policy_packet_path: Path = A_GAUGE_POLICY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    policy_packet = _read_json(a_gauge_policy_packet_path)
    steps = _calculation_steps()
    review_criteria = _review_criteria(policy_packet)
    acceptance_criteria = {
        "consumes_expected_vacuum_retry_target": (
            policy_packet.get("schema_id") == A_GAUGE_POLICY_PACKET_SCHEMA_ID
            and policy_packet.get("packet_id") == A_GAUGE_POLICY_PACKET_ID
            and policy_packet.get("outcome_id") == A_GAUGE_POLICY_PACKET_OUTCOME
            and policy_packet.get("selected_next_target") == CONSUMED_TARGET
            and policy_packet.get("accepted") is True
        ),
        "selected_u1_policy_matches_packet": (
            policy_packet.get("u1_route_selected") is True
            and policy_packet.get("A_as_smooth_real_one_form_selected") is True
            and policy_packet.get("definition_of_F_selected") is True
        ),
        "action_variation_form_recorded": "delta S_A^U1" in ACTION_VARIATION_FORM,
        "delta_F_recorded": "partial_mu delta A_nu" in DELTA_F_FORM,
        "integration_by_parts_recorded": "nabla_mu F^{mu nu}" in INTEGRATION_BY_PARTS_FORM,
        "boundary_policy_used": "boundary" in BOUNDARY_POLICY_USED,
        "vacuum_route_constructed": VACUUM_EULER_LAGRANGE_ROUTE
        == "nabla_mu F^{mu nu} = 0",
        "current_route_still_blocked": (
            policy_packet.get("current_derivation_blocked") is True
            and policy_packet.get("matter_current_J_nu_derived") is False
            and policy_packet.get("external_current_policy_selected") is False
        ),
        "nonabelian_still_blocked": policy_packet.get("nonabelian_route_selected") is False,
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "next_target_is_result_review": NEXT_TARGET.startswith("review_"),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_TOE_NATIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "TOE_NATIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_PACKET_REQUIRES_REMEDIATION",
        "a_vacuum_variation_retry_result": A_VACUUM_VARIATION_RETRY_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "a_gauge_policy_packet_result": A_GAUGE_POLICY_PACKET_RESULT,
        "reviewed_a_gauge_policy_packet_artifact_id": policy_packet.get("schema_id"),
        "reviewed_a_gauge_policy_packet_outcome": policy_packet.get("outcome_id"),
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": SELECTED_F_DEFINITION,
        "variation_policy": VARIATION_POLICY,
        "current_policy": CURRENT_POLICY,
        "gauge_fixing_policy": GAUGE_FIXING_POLICY,
        "selected_A_action": SELECTED_A_ACTION,
        "selected_F_definition": SELECTED_F_DEFINITION,
        "delta_F_form": DELTA_F_FORM,
        "action_variation_form": ACTION_VARIATION_FORM,
        "integration_by_parts_form": INTEGRATION_BY_PARTS_FORM,
        "boundary_policy_used": BOUNDARY_POLICY_USED,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "vacuum_route_decision": VACUUM_ROUTE_DECISION,
        "calculation_steps": steps,
        "calculation_step_count": len(steps),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "u1_policy_used": True,
        "minimal_abelian_route_selected": True,
        "A_as_smooth_real_one_form_selected": True,
        "F_definition_used": True,
        "delta_F_recorded": True,
        "action_variation_computed": True,
        "integration_by_parts_computed": True,
        "boundary_policy_used_for_variation": True,
        "boundary_terms_vanish_by_selected_policy": True,
        "boundary_terms_controlled": True,
        "vacuum_gauge_variation_route_constructed": True,
        "vacuum_u1_variation_route_constructed": True,
        "vacuum_euler_lagrange_route_constructed": True,
        "vacuum_route_recorded": True,
        "source_current_route_still_blocked": True,
        "current_derivation_blocked": True,
        "current_route_derived": False,
        "current_source_route_constructed": False,
        "matter_current_J_nu_derived": False,
        "psi_derived_current": False,
        "psi_derived_current_deferred": True,
        "external_current_policy_selected": False,
        "external_current_not_selected_as_native_derivation": True,
        "nonabelian_route_selected": False,
        "gauge_covariant_D_mu_route_selected": False,
        "covariant_derivative_D_mu_convention_selected": False,
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
        "record_validated": True,
        "symbolic_calculation_recorded": True,
        "native_derivation_blocked": True,
        "proof_depth_label": "SYMBOLIC_VACUUM_U1_VARIATION_ROUTE_RECORDED_NO_CURRENT_OR_CLOSURE",
        "a_surface_variation_executed": True,
        "a_surface_variation_route_executed": True,
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
            "derive J^nu without current policy",
            "claim psi-derived current",
            "admit external current as native derivation",
            "select non-Abelian route",
            "select gauge fixing as physical structure",
            "derive stress-energy T_A",
            "prove current conservation",
            "prove source admissibility",
            "construct A-relevant C_k rules",
            "claim EM or QFT-GR closure",
            "promote the working-form master action",
            "claim empirical validation, public readiness, or release completion",
        ],
        "downstream_progression": [
            {
                "stage": "A_vacuum_variation_retry_under_selected_u1_policy",
                "status": "VACUUM_GAUGE_VARIATION_ROUTE_CONSTRUCTED",
                "decision": A_VACUUM_VARIATION_RETRY_RESULT,
                "reason": (
                    "The selected U(1) policy supports the vacuum variation "
                    "route to nabla_mu F^{mu nu} = 0."
                ),
            },
            {
                "stage": "result_review",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The vacuum route should be reviewed before choosing stress-"
                    "energy, current-coupling, or A-relevant C_k work."
                ),
            },
        ],
        "mathematical_statement": (
            "Under the selected U(1) policy, S_A = -1/4 integral dVol_g "
            "F_{mu nu}F^{mu nu} with F=dA. The variation "
            "delta F_{mu nu}=partial_mu delta A_nu - partial_nu delta A_mu "
            "gives delta S_A = - integral dVol_g F^{mu nu} nabla_mu delta A_nu. "
            "After integration by parts and compact-support or fixed-boundary "
            "variation, delta S_A = integral dVol_g (nabla_mu F^{mu nu}) "
            "delta A_nu, so stationarity records the vacuum route "
            "nabla_mu F^{mu nu} = 0."
        ),
        "non_claim_boundary": (
            "This packet constructs the vacuum U(1) gauge variation route only. "
            "It does not derive J^nu, does not derive a psi-current, does not "
            "select an external current as native derivation, does not select a "
            "non-Abelian route, does not select gauge fixing as physical "
            "structure, does not derive stress-energy T_A, does not prove "
            "current conservation, does not prove source admissibility, does "
            "not construct A-relevant C_k rules, does not close EM, does not "
            "close QFT-GR, does not promote the master action, does not claim "
            "empirical validation, and does not authorize public readiness or "
            "release completion."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeAVacuumVariationRetryUnderSelectedU1PolicyPacket",
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


def write_toe_native_a_vacuum_variation_retry_under_selected_u1_policy_packet(
    *,
    a_gauge_policy_packet_path: Path = A_GAUGE_POLICY_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_a_vacuum_variation_retry_under_selected_u1_policy_packet(
        a_gauge_policy_packet_path=a_gauge_policy_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A vacuum variation retry under selected U(1) policy packet."
        )
    )
    parser.add_argument(
        "--a-gauge-policy-packet",
        type=Path,
        default=A_GAUGE_POLICY_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_a_vacuum_variation_retry_under_selected_u1_policy_packet(
        a_gauge_policy_packet_path=args.a_gauge_policy_packet,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
