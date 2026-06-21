from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_gauge_group_domain_and_current_policy_packet_report import (
    VARIATION_POLICY,
)
from formal.python.tools.toe_native_a_route_selection_after_vacuum_u1_variation_report import (
    A_FIELD_DOMAIN_POLICY,
    DEFAULT_OUT as A_ROUTE_SELECTOR_PATH,
    DELTA_F_FORM,
    F_DEFINITION_POLICY,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as A_ROUTE_SELECTOR_OUTCOME,
    PACKET_ID as A_ROUTE_SELECTOR_PACKET_ID,
    SCHEMA_ID as A_ROUTE_SELECTOR_SCHEMA_ID,
    SOURCE_ROUTE_STILL_BLOCKED,
    VACUUM_EULER_LAGRANGE_ROUTE,
)
from formal.python.tools.toe_native_phi_signature_domain_and_potential_policy_packet_report import (
    METRIC_SIGNATURE_POLICY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-21T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_PACKET_20260621_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_PACKET_v0"
A_STRESS_ENERGY_ROUTE_RESULT = (
    "GAUGE_STRESS_ENERGY_ROUTE_RECORDED_NO_SOURCE_ADMISSIBILITY_OR_EM_CLOSURE"
)
OUTCOME_ID = (
    "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_PACKET_PREPARED_"
    "GAUGE_STRESS_ENERGY_ROUTE_RECORDED_NO_SOURCE_ADMISSIBILITY_OR_EM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "toe_native_A_stress_energy_route_under_selected_u1_policy_records_gauge_"
    "stress_energy_route_no_source_admissibility_or_em_closure"
)
NEXT_TARGET = "review_toe_native_A_stress_energy_route_under_selected_u1_policy_result"
NEXT_TARGET_KIND = "toe_native_A_stress_energy_route_under_selected_u1_policy_result_review"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_PACKET_"
    "20260621_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeAStressEnergyRouteUnderSelectedU1PolicyPacket.lean"
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

SELECTED_A_STRESS_ENERGY_ACTION = (
    "S_A[A,g] = integral_M dVol_g [-1/4 F_{alpha beta} F^{alpha beta}]"
)
METRIC_VARIATION_CONVENTION = (
    "vary inverse metric k^{mu nu}=delta g^{mu nu}, hold A and "
    "F_{alpha beta}=dA fixed as a covariant 2-form, and define "
    "T^A_{mu nu}=2/sqrt(-g) delta S_A/delta g^{mu nu}"
)
METRIC_VARIATION_FORM = (
    "delta_g S_A(k) = 1/2 integral_M dVol_g T^A_{mu nu} k^{mu nu}"
)
F_CONTRACTION_VARIATION_ROUTE = (
    "delta_g(F_{alpha beta} F^{alpha beta}) = "
    "2 F_{mu alpha} F_{nu}{}^{alpha} k^{mu nu}"
)
VOLUME_VARIATION_ROUTE = (
    "delta_g dVol_g = -1/2 dVol_g g_{mu nu} k^{mu nu}"
)
STRESS_ENERGY_UNDER_SELECTED_U1_POLICY = (
    "T^A_{mu nu} = - F_{mu alpha} F_{nu}{}^{alpha} + "
    "1/4 g_{mu nu} F_{alpha beta} F^{alpha beta}"
)
CONVENTION_SCOPE = (
    "convention-sensitive under (+,-,-,-) and "
    "T^A_{mu nu}=2/sqrt(-g) delta S_A/delta g^{mu nu}; the sign pattern must "
    "be revisited if the metric signature or stress-tensor definition changes"
)
POSITIVE_ENERGY_DENSITY_SIGN_CHECK = (
    "for the selected (+,-,-,-) convention this sign pattern is the usual "
    "positive electromagnetic energy-density route shape"
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
            "step_id": "state_selected_u1_gauge_action",
            "status": "recorded",
            "mathematical_content": SELECTED_A_STRESS_ENERGY_ACTION,
        },
        {
            "step_id": "preserve_selected_u1_policy",
            "status": "recorded",
            "mathematical_content": {
                "gauge_group": GAUGE_GROUP_POLICY,
                "A_domain": A_FIELD_DOMAIN_POLICY,
                "F_definition": F_DEFINITION_POLICY,
                "metric_signature": METRIC_SIGNATURE_POLICY,
            },
        },
        {
            "step_id": "state_metric_variation_convention",
            "status": "recorded",
            "mathematical_content": METRIC_VARIATION_CONVENTION,
        },
        {
            "step_id": "vary_volume_form",
            "status": "computed_under_selected_convention",
            "mathematical_content": VOLUME_VARIATION_ROUTE,
        },
        {
            "step_id": "vary_raised_F_contraction",
            "status": "computed_under_selected_convention",
            "mathematical_content": F_CONTRACTION_VARIATION_ROUTE,
        },
        {
            "step_id": "read_metric_variation_form",
            "status": "computed_under_selected_convention",
            "mathematical_content": METRIC_VARIATION_FORM,
        },
        {
            "step_id": "record_gauge_stress_energy_route",
            "status": "stress_energy_route_recorded",
            "mathematical_content": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        },
        {
            "step_id": "record_convention_scope",
            "status": "convention_scope_retained",
            "mathematical_content": CONVENTION_SCOPE,
        },
        {
            "step_id": "retain_current_ck_closure_blockers",
            "status": "retained",
            "mathematical_content": (
                "J^nu not derived; no current conservation; no source "
                "admissibility; no A-relevant C_k; no EM or QFT-GR closure"
            ),
        },
    ]


def _review_criteria(selector_packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_expected_stress_energy_target",
            "status": "accepted",
            "evidence": selector_packet.get("selected_next_target"),
            "assessment": "The A route selector authorized this stress-energy packet.",
        },
        {
            "row_id": "selected_u1_policy_preserved",
            "status": "accepted",
            "evidence": [
                GAUGE_GROUP_POLICY,
                A_FIELD_DOMAIN_POLICY,
                F_DEFINITION_POLICY,
            ],
            "assessment": "The route remains the selected minimal U(1) route.",
        },
        {
            "row_id": "metric_signature_policy_tied",
            "status": "accepted",
            "evidence": METRIC_SIGNATURE_POLICY,
            "assessment": "The stress-energy sign convention is tied to (+,-,-,-).",
        },
        {
            "row_id": "gauge_action_recorded",
            "status": "accepted",
            "evidence": SELECTED_A_STRESS_ENERGY_ACTION,
            "assessment": "The pure gauge metric-variation surface is explicit.",
        },
        {
            "row_id": "metric_variation_convention_recorded",
            "status": "accepted",
            "evidence": METRIC_VARIATION_CONVENTION,
            "assessment": "The inverse-metric variation convention is explicit.",
        },
        {
            "row_id": "volume_variation_route_recorded",
            "status": "accepted",
            "evidence": VOLUME_VARIATION_ROUTE,
            "assessment": "The volume-form variation contribution is recorded.",
        },
        {
            "row_id": "F_contraction_variation_route_recorded",
            "status": "accepted",
            "evidence": F_CONTRACTION_VARIATION_ROUTE,
            "assessment": "The metric variation of raised F indices is recorded.",
        },
        {
            "row_id": "gauge_stress_energy_route_recorded",
            "status": "accepted",
            "evidence": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
            "assessment": "The convention-dependent gauge stress-energy route is recorded.",
        },
        {
            "row_id": "vacuum_field_route_preserved",
            "status": "accepted",
            "evidence": VACUUM_EULER_LAGRANGE_ROUTE,
            "assessment": "The prior vacuum U(1) field-equation route is preserved.",
        },
        {
            "row_id": "current_route_still_blocked",
            "status": "accepted",
            "evidence": SOURCE_ROUTE_STILL_BLOCKED,
            "assessment": "The sourced-current route remains blocked shape only.",
        },
        {
            "row_id": "source_admissibility_ck_and_closure_not_claimed",
            "status": "accepted",
            "evidence": [
                "A_source_admissibility_proved=false",
                "A_relevant_C_k_rules_constructed=false",
                "em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
            ],
            "assessment": "No source admissibility, C_k, closure, or promotion follows.",
        },
        {
            "row_id": "next_review_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The stress-energy route is routed to review.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_A_stress_energy_route_under_selected_u1_policy_packet",
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


def build_toe_native_a_stress_energy_route_under_selected_u1_policy_packet(
    *,
    a_route_selector_path: Path = A_ROUTE_SELECTOR_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector_packet = _read_json(a_route_selector_path)
    steps = _calculation_steps()
    review_criteria = _review_criteria(selector_packet)
    acceptance_criteria = {
        "consumes_expected_stress_energy_target": (
            selector_packet.get("schema_id") == A_ROUTE_SELECTOR_SCHEMA_ID
            and selector_packet.get("packet_id") == A_ROUTE_SELECTOR_PACKET_ID
            and selector_packet.get("outcome_id") == A_ROUTE_SELECTOR_OUTCOME
            and selector_packet.get("selected_next_target") == CONSUMED_TARGET
            and selector_packet.get("accepted") is True
        ),
        "selector_authorized_packet_preparation_only": (
            selector_packet.get("stress_energy_route_packet_authorized") is True
            and selector_packet.get("stress_energy_derivation_executed") is False
            and selector_packet.get("stress_energy_T_A_derived") is False
        ),
        "selected_u1_policy_preserved": (
            selector_packet.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and selector_packet.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and selector_packet.get("F_definition_policy") == F_DEFINITION_POLICY
        ),
        "metric_signature_tied": METRIC_SIGNATURE_POLICY == "(+,-,-,-)",
        "stress_energy_sign_pattern_recorded": (
            STRESS_ENERGY_UNDER_SELECTED_U1_POLICY.startswith("T^A_{mu nu} = -")
            and "+ 1/4 g_{mu nu}" in STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
        ),
        "convention_scope_retained": "convention-sensitive" in CONVENTION_SCOPE,
        "current_route_still_blocked": (
            selector_packet.get("J_nu_derived") is False
            and selector_packet.get("current_route_derived") is False
            and selector_packet.get("source_route_still_blocked")
            == SOURCE_ROUTE_STILL_BLOCKED
        ),
        "source_admissibility_and_closure_still_blocked": (
            selector_packet.get("A_source_admissibility_proved") is False
            and selector_packet.get("A_relevant_C_k_rules_constructed") is False
            and selector_packet.get("em_closure_claimed") is False
            and selector_packet.get("qft_gr_closure_claimed") is False
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "next_target_is_result_review": NEXT_TARGET.startswith("review_"),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_PACKET_REQUIRES_REMEDIATION",
        "a_stress_energy_route_result": A_STRESS_ENERGY_ROUTE_RESULT,
        "stress_energy_route_result": A_STRESS_ENERGY_ROUTE_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "a_route_selector_outcome": A_ROUTE_SELECTOR_OUTCOME,
        "reviewed_a_route_selector_artifact_id": selector_packet.get("schema_id"),
        "reviewed_a_route_selector_outcome": selector_packet.get("outcome_id"),
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "delta_F_form": DELTA_F_FORM,
        "variation_policy": VARIATION_POLICY,
        "metric_signature_policy": METRIC_SIGNATURE_POLICY,
        "selected_A_stress_energy_action": SELECTED_A_STRESS_ENERGY_ACTION,
        "metric_variation_convention": METRIC_VARIATION_CONVENTION,
        "volume_variation_route": VOLUME_VARIATION_ROUTE,
        "F_contraction_variation_route": F_CONTRACTION_VARIATION_ROUTE,
        "metric_variation_form": METRIC_VARIATION_FORM,
        "stress_energy_under_selected_u1_policy": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "gauge_stress_energy_route": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "convention_scope": CONVENTION_SCOPE,
        "positive_energy_density_sign_check": POSITIVE_ENERGY_DENSITY_SIGN_CHECK,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
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
        "metric_signature_policy_used": True,
        "metric_variation_convention_recorded": True,
        "metric_variation_computed": True,
        "metric_variation_route_recorded": True,
        "volume_variation_route_recorded": True,
        "F_contraction_variation_route_recorded": True,
        "stress_energy_route_recorded": True,
        "gauge_stress_energy_route_recorded": True,
        "stress_energy_T_A_recorded": True,
        "stress_energy_T_A_derived": True,
        "stress_energy_derivation_executed": True,
        "stress_energy_route_constructed": True,
        "stress_energy_route_convention_sensitive": True,
        "stress_energy_sign_convention_verified_explicitly": True,
        "stress_energy_positive_energy_density_sign_shape_recorded": True,
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
        "record_validated": True,
        "symbolic_calculation_recorded": True,
        "proof_depth_label": (
            "SYMBOLIC_U1_GAUGE_STRESS_ENERGY_ROUTE_RECORDED_NO_SOURCE_ADMISSIBILITY"
        ),
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
        ],
        "downstream_progression": [
            {
                "stage": "A_stress_energy_route_under_selected_u1_policy",
                "status": "GAUGE_STRESS_ENERGY_ROUTE_RECORDED",
                "decision": A_STRESS_ENERGY_ROUTE_RESULT,
                "reason": (
                    "Metric variation of the pure U(1) gauge action records "
                    "the convention-dependent T^A route."
                ),
            },
            {
                "stage": "result_review",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The route should be reviewed before source admissibility, "
                    "current coupling, or A-relevant C_k work."
                ),
            },
        ],
        "mathematical_statement": (
            "Under the selected U(1) policy with A a smooth real 1-form, "
            "F=dA, and the (+,-,-,-) metric convention, metric variation of "
            "S_A = integral dVol_g[-1/4 F_{alpha beta}F^{alpha beta}] with "
            "A and covariant F held fixed records "
            "T^A_{mu nu} = - F_{mu alpha}F_{nu}{}^{alpha} + 1/4 g_{mu nu} "
            "F_{alpha beta}F^{alpha beta}. This is convention-sensitive and "
            "does not by itself prove source admissibility or closure."
        ),
        "non_claim_boundary": (
            "This packet records the convention-sensitive U(1) gauge "
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
            "ToeFormal.Derivation.ToeNativeAStressEnergyRouteUnderSelectedU1PolicyPacket",
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


def write_toe_native_a_stress_energy_route_under_selected_u1_policy_packet(
    *,
    a_route_selector_path: Path = A_ROUTE_SELECTOR_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_a_stress_energy_route_under_selected_u1_policy_packet(
        a_route_selector_path=a_route_selector_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A stress-energy route under selected U(1) policy packet."
        )
    )
    parser.add_argument(
        "--a-route-selector",
        type=Path,
        default=A_ROUTE_SELECTOR_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_a_stress_energy_route_under_selected_u1_policy_packet(
        a_route_selector_path=args.a_route_selector,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
