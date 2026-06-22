from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_route_selection_after_stress_energy_route_report import (
    A_FIELD_DOMAIN_POLICY,
    CONSUMED_TARGET as A_AFTER_STRESS_SELECTOR_CONSUMED_TARGET,
    DEFAULT_OUT as A_AFTER_STRESS_SELECTOR_PATH,
    F_DEFINITION_POLICY,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    METRIC_SIGNATURE_POLICY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as A_AFTER_STRESS_SELECTOR_OUTCOME,
    PACKET_ID as A_AFTER_STRESS_SELECTOR_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as A_AFTER_STRESS_SELECTOR_SCHEMA_ID,
    SELECTION_RESULT as A_AFTER_STRESS_SELECTION_RESULT,
    SOURCE_ROUTE_STILL_BLOCKED,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
    CURRENT_TARGET_AGGREGATE_PATH,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-21T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_FOR_VACUUM_STRESS_ENERGY_"
    "20260621_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_FOR_VACUUM_STRESS_ENERGY_v0"
PACKET_RESULT = (
    "VACUUM_GAUGE_SOURCE_ADMISSIBILITY_REVIEW_PREPARED_ON_SHELL_NO_CURRENT_"
    "OR_EM_CLOSURE"
)
OUTCOME_ID = (
    "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_FOR_VACUUM_STRESS_ENERGY_"
    "PREPARED_VACUUM_GAUGE_SOURCE_ADMISSIBILITY_REVIEW_ON_SHELL_NO_CURRENT_"
    "OR_EM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "toe_native_A_source_admissibility_review_for_vacuum_stress_energy_prepares_"
    "on_shell_vacuum_gauge_source_review_no_current_or_em_closure"
)

NEXT_TARGET = "review_toe_native_A_source_admissibility_review_for_vacuum_stress_energy_result"
NEXT_TARGET_KIND = (
    "toe_native_A_source_admissibility_review_for_vacuum_stress_energy_result_review"
)

SOURCE_ADMISSIBILITY_CONDITION = "nabla_mu T_A^{mu nu} = 0"
BIANCHI_IDENTITY_ROUTE = "dF = 0 / nabla_[lambda F_{mu nu]} = 0"
STRESS_ENERGY_DIVERGENCE_ROUTE = (
    "nabla_mu T_A^{mu nu} = - F^{nu}{}_{alpha} nabla_mu F^{mu alpha}"
)
ON_SHELL_VACUUM_CONSERVATION_ROUTE = (
    "F=dA, dF=0, nabla_mu F^{mu nu}=0, and metric-compatible Levi-Civita "
    "connection imply nabla_mu T_A^{mu nu}=0"
)
CURRENT_COUPLED_EXCHANGE_CAUTION = (
    "With a current-coupled route the gauge-field stress-energy divergence "
    "would be proportional to -F^{nu}{}_{alpha} J^alpha up to convention and "
    "would require a matter/current exchange policy; that route is not selected."
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_FOR_VACUUM_STRESS_ENERGY_"
    "20260621_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeASourceAdmissibilityReviewForVacuumStressEnergy.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _review_preparation_criteria(selector: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_selected_vacuum_source_admissibility_target",
            "status": "prepared",
            "evidence": CONSUMED_TARGET,
            "assessment": (
                "The active A-source admissibility preparation target is consumed."
            ),
        },
        {
            "row_id": "after_stress_selector_preserved",
            "status": "prepared",
            "evidence": selector.get("selection_result"),
            "assessment": (
                "The after-stress selector is the authorizing input for this packet."
            ),
        },
        {
            "row_id": "selected_u1_policy_preserved",
            "status": "prepared",
            "evidence": [GAUGE_GROUP_POLICY, A_FIELD_DOMAIN_POLICY, F_DEFINITION_POLICY],
            "assessment": (
                "The review remains inside the selected minimal U(1) route."
            ),
        },
        {
            "row_id": "smooth_domain_and_connection_requirements_recorded",
            "status": "prepared",
            "evidence": [
                A_FIELD_DOMAIN_POLICY,
                "smooth A and F domain",
                "metric-compatible Levi-Civita connection",
                METRIC_SIGNATURE_POLICY,
            ],
            "assessment": (
                "The local review states the smoothness, connection, and signature "
                "requirements needed for the divergence calculation."
            ),
        },
        {
            "row_id": "bianchi_identity_route_recorded",
            "status": "prepared",
            "evidence": BIANCHI_IDENTITY_ROUTE,
            "assessment": "F=dA supplies the vacuum Abelian Bianchi route.",
        },
        {
            "row_id": "vacuum_field_equation_route_preserved",
            "status": "prepared",
            "evidence": VACUUM_EULER_LAGRANGE_ROUTE,
            "assessment": "The on-shell condition is the vacuum U(1) equation.",
        },
        {
            "row_id": "stress_energy_route_preserved",
            "status": "prepared",
            "evidence": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
            "assessment": (
                "The convention-sensitive gauge stress-energy expression is the "
                "candidate source object."
            ),
        },
        {
            "row_id": "source_admissibility_condition_recorded",
            "status": "prepared",
            "evidence": SOURCE_ADMISSIBILITY_CONDITION,
            "assessment": (
                "The local source-admissibility check is conservation of the "
                "candidate stress-energy."
            ),
        },
        {
            "row_id": "stress_energy_divergence_route_recorded",
            "status": "prepared",
            "evidence": STRESS_ENERGY_DIVERGENCE_ROUTE,
            "assessment": (
                "The packet records the convention-sensitive divergence route "
                "that the result review must check."
            ),
        },
        {
            "row_id": "on_shell_vacuum_conservation_candidate_recorded",
            "status": "prepared",
            "evidence": ON_SHELL_VACUUM_CONSERVATION_ROUTE,
            "assessment": (
                "The candidate local vacuum source route is prepared only under "
                "the vacuum equation and Bianchi route."
            ),
        },
        {
            "row_id": "current_coupled_exchange_caution_recorded",
            "status": "prepared",
            "evidence": CURRENT_COUPLED_EXCHANGE_CAUTION,
            "assessment": (
                "The packet blocks silent promotion to sourced electromagnetism."
            ),
        },
        {
            "row_id": "ck_closure_and_promotion_boundary_preserved",
            "status": "prepared",
            "evidence": [
                "A_relevant_C_k_rules_constructed=false",
                "em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": (
                "The packet prepares a review surface only and does not construct "
                "C_k rules, closure, or master-action promotion."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_source_admissibility_review_for_vacuum_stress_energy"
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
    }


def build_toe_native_a_source_admissibility_review_for_vacuum_stress_energy(
    *,
    a_after_stress_selector_path: Path = A_AFTER_STRESS_SELECTOR_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector = _read_json(a_after_stress_selector_path)
    criteria = _review_preparation_criteria(selector)
    acceptance_criteria = {
        "consumes_current_source_admissibility_preparation_target": (
            selector.get("schema_id") == A_AFTER_STRESS_SELECTOR_SCHEMA_ID
            and selector.get("packet_id") == A_AFTER_STRESS_SELECTOR_PACKET_ID
            and selector.get("outcome_id") == A_AFTER_STRESS_SELECTOR_OUTCOME
            and selector.get("selected_next_target") == CONSUMED_TARGET
            and selector.get("selection_result") == A_AFTER_STRESS_SELECTION_RESULT
            and selector.get("accepted") is True
        ),
        "selected_u1_context_preserved": (
            selector.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and selector.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and selector.get("F_definition_policy") == F_DEFINITION_POLICY
            and selector.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and selector.get("stress_energy_under_selected_u1_policy")
            == STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
        ),
        "source_admissibility_review_was_selected_by_selector": (
            selector.get("source_admissibility_review_selected") is True
            and selector.get("vacuum_source_admissibility_review_selected") is True
            and selector.get("source_admissibility_review_packet_authorized") is True
        ),
        "current_route_still_blocked": (
            selector.get("source_route_still_blocked") == SOURCE_ROUTE_STILL_BLOCKED
            and selector.get("current_route_derived") is False
            and selector.get("J_nu_derived") is False
        ),
        "review_preparation_criteria_all_recorded": all(
            row["status"] == "prepared" for row in criteria
        ),
        "packet_only_no_admissibility_acceptance_or_closure": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_FOR_VACUUM_STRESS_ENERGY"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_FOR_VACUUM_STRESS_"
            "ENERGY_PREPARATION"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "packet_result": "PREPARED" if prepared else "REQUIRES_REMEDIATION",
        "outcome_id": OUTCOME_ID
        if prepared
        else (
            "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_FOR_VACUUM_STRESS_ENERGY_"
            "REQUIRES_REMEDIATION"
        ),
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_selector_target": A_AFTER_STRESS_SELECTOR_CONSUMED_TARGET,
        "authorized_by_selector_outcome": A_AFTER_STRESS_SELECTOR_OUTCOME,
        "selector_selection_result": A_AFTER_STRESS_SELECTION_RESULT,
        "a_source_admissibility_review_result": PACKET_RESULT,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "metric_signature_policy": METRIC_SIGNATURE_POLICY,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "stress_energy_under_selected_u1_policy": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "candidate_source_object": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "bianchi_identity_route": BIANCHI_IDENTITY_ROUTE,
        "stress_energy_divergence_route": STRESS_ENERGY_DIVERGENCE_ROUTE,
        "on_shell_vacuum_conservation_route": ON_SHELL_VACUUM_CONSERVATION_ROUTE,
        "current_coupled_exchange_caution": CURRENT_COUPLED_EXCHANGE_CAUTION,
        "review_preparation_criteria": criteria,
        "review_preparation_criteria_count": len(criteria),
        "review_preparation_criteria_prepared_count": sum(
            1 for row in criteria if row["status"] == "prepared"
        ),
        "acceptance_criteria": acceptance_criteria,
        "source_admissibility_review_prepared": prepared,
        "vacuum_gauge_source_admissibility_review_prepared": prepared,
        "local_on_shell_source_review_surface_prepared": prepared,
        "local_on_shell_source_route_candidate_recorded": prepared,
        "candidate_source_object_recorded": prepared,
        "source_admissibility_condition_recorded": prepared,
        "bianchi_identity_route_recorded": prepared,
        "stress_energy_divergence_route_recorded": prepared,
        "on_shell_vacuum_conservation_route_recorded": prepared,
        "current_coupled_exchange_caution_recorded": prepared,
        "result_review_authorized": prepared,
        "source_admissibility_review_pending": False,
        "source_admissibility_review_executed": False,
        "source_admissibility_review_completed": False,
        "source_admissibility_executed": False,
        "source_admissibility_proved": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "A_source_admissibility_proved": False,
        "A_source_admissibility_claimed": False,
        "stress_energy_source_admissibility_proved": False,
        "stress_energy_as_gravity_source_authorized": False,
        "A_relevant_C_k_rules_constructed": False,
        "A_relevant_C_k_triads_constructed": False,
        "source_bridge_transport_ck_analogues_constructed": False,
        "current_route_derived": False,
        "current_source_route_constructed": False,
        "matter_current_J_nu_derived": False,
        "J_nu_derived": False,
        "psi_current_route_constructed": False,
        "psi_derived_current": False,
        "external_current_policy_selected": False,
        "external_current_native_derivation_selected": False,
        "current_conservation_proved": False,
        "current_conservation_theorem_claimed": False,
        "maxwell_equation_derived": False,
        "maxwell_equations_derived": False,
        "sourced_maxwell_equation_derived": False,
        "sourced_maxwell_closure_claimed": False,
        "nonabelian_route_selected": False,
        "yang_mills_equations_derived": False,
        "field_equations_derived": False,
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
        "accepted_outcomes_considered": [
            OUTCOME_ID,
            (
                "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_FOR_VACUUM_STRESS_"
                "ENERGY_BLOCKED_BY_MISSING_BIANCHI_OR_VACUUM_EQUATION"
            ),
            (
                "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_FOR_VACUUM_STRESS_"
                "ENERGY_BLOCKED_BY_CURRENT_COUPLED_ROUTE_SCOPE_LEAK"
            ),
        ],
        "critical_gate_fail_conditions": [
            "claim A-source admissibility as proved in the preparation packet",
            "derive J^nu",
            "import psi-current route",
            "select external current as native derivation",
            "prove current conservation theorem",
            "claim sourced Maxwell closure",
            "construct A-relevant C_k triad",
            "claim EM closure",
            "claim QFT-GR closure",
            "authorize semiclassical coupling",
            "promote the working-form master action",
        ],
        "downstream_progression": [
            {
                "stage": "A_vacuum_source_admissibility_review_preparation",
                "status": "PREPARED_FOR_RESULT_REVIEW",
                "decision": OUTCOME_ID,
                "reason": (
                    "The packet records the local on-shell conservation test "
                    "surface for the vacuum U(1) gauge stress-energy route."
                ),
            },
            {
                "stage": "A_vacuum_source_admissibility_result_review",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The next packet may review whether the prepared local "
                    "on-shell route is accepted. This packet does not accept "
                    "source admissibility by itself."
                ),
            },
        ],
        "mathematical_statement": (
            "For the selected U(1) route, the packet prepares the local "
            "source-admissibility review for the candidate source "
            + STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
            + ". The review surface is "
            + SOURCE_ADMISSIBILITY_CONDITION
            + " using "
            + BIANCHI_IDENTITY_ROUTE
            + ", "
            + VACUUM_EULER_LAGRANGE_ROUTE
            + ", metric-compatible Levi-Civita connection, and the "
            + METRIC_SIGNATURE_POLICY
            + " convention. It records the convention-sensitive route "
            + STRESS_ENERGY_DIVERGENCE_ROUTE
            + " and the vacuum on-shell implication "
            + ON_SHELL_VACUUM_CONSERVATION_ROUTE
            + "."
        ),
        "non_claim_boundary": (
            "This packet prepares the vacuum U(1) gauge stress-energy "
            "source-admissibility review only. It records the local on-shell "
            "conservation test surface but does not execute the result review, "
            "does not prove A-source admissibility, does not derive J^nu, does "
            "not construct a psi-current route, does not select an external "
            "current as a native derivation, does not prove a current "
            "conservation theorem, does not claim sourced Maxwell closure, "
            "does not construct A-relevant C_k rules, does not close EM, does "
            "not close QFT-GR, does not authorize semiclassical coupling, does "
            "not claim empirical validation, and does not promote the master "
            "action."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeASourceAdmissibilityReviewForVacuumStressEnergy",
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


def write_toe_native_a_source_admissibility_review_for_vacuum_stress_energy(
    *,
    a_after_stress_selector_path: Path = A_AFTER_STRESS_SELECTOR_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_a_source_admissibility_review_for_vacuum_stress_energy(
        a_after_stress_selector_path=a_after_stress_selector_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A source-admissibility review preparation "
            "packet for vacuum gauge stress-energy."
        )
    )
    parser.add_argument(
        "--a-after-stress-selector",
        type=Path,
        default=A_AFTER_STRESS_SELECTOR_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_a_source_admissibility_review_for_vacuum_stress_energy(
        a_after_stress_selector_path=args.a_after_stress_selector,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
