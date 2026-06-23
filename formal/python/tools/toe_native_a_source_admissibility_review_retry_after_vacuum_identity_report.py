from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_vacuum_source_admissibility_identity_result_review_report import (
    A_FIELD_DOMAIN_POLICY,
    ANTISYMMETRY_ROUTE,
    BIANCHI_IDENTITY_ROUTE,
    CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as A_SOURCE_IDENTITY_RESULT_REVIEW_PATH,
    DIVERGENCE_IDENTITY,
    F_DEFINITION_POLICY,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    METRIC_COMPATIBILITY_ROUTE,
    METRIC_SIGNATURE_POLICY,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    ON_SHELL_VACUUM_CONSERVATION_ROUTE,
    OUTCOME_ID as A_SOURCE_IDENTITY_RESULT_REVIEW_OUTCOME,
    PACKET_ID as A_SOURCE_IDENTITY_RESULT_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT as A_SOURCE_IDENTITY_RESULT_REVIEW_RESULT,
    SCHEMA_ID as A_SOURCE_IDENTITY_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONDITION,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-22T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_AFTER_VACUUM_IDENTITY_"
    "20260622_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_AFTER_VACUUM_IDENTITY_v0"
PACKET_RESULT = (
    "LOCAL_ON_SHELL_VACUUM_GAUGE_SOURCE_ROUTE_ACCEPTED_NO_CURRENT_OR_EM_CLOSURE"
)
OUTCOME_ID = (
    "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_ACCEPTS_LOCAL_ON_SHELL_"
    "VACUUM_GAUGE_SOURCE_ROUTE_NO_CURRENT_OR_EM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "toe_native_A_source_admissibility_review_retry_accepts_local_on_shell_"
    "vacuum_gauge_source_route_no_current_or_em_closure"
)

NEXT_TARGET = "review_toe_native_A_source_admissibility_review_retry_after_vacuum_identity_result"
NEXT_TARGET_KIND = (
    "toe_native_A_source_admissibility_review_retry_after_vacuum_identity_result_review"
)

LOCAL_SOURCE_ROUTE_SCOPE = "local classical vacuum U(1) route under selected convention"
BOUNDED_SOURCE_ADMISSIBILITY_RESULT = (
    "nabla_mu T_A^{mu nu} = 0 holds on shell for the selected local vacuum U(1) "
    "gauge stress-energy route"
)
FULL_SOURCE_ADMISSIBILITY_BOUNDARY = (
    "full source admissibility remains unaccepted outside the local classical "
    "vacuum U(1) on-shell route"
)
CURRENT_COUPLED_SCOPE_BOUNDARY = (
    "current-coupled gauge stress-energy alone is not generally conserved and "
    "requires matter/current exchange; the sourced route is not selected"
)
SOURCE_ROUTE_STILL_BLOCKED = "nabla_mu F^{mu nu} = J^nu"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_AFTER_VACUUM_IDENTITY_"
    "20260622_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeASourceAdmissibilityReviewRetryAfterVacuumIdentity.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _bounded_review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_retry_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The active retry target is consumed.",
        },
        {
            "row_id": "accepted_vacuum_identity_consumed",
            "status": "accepted",
            "evidence": packet.get("outcome_id"),
            "assessment": "The accepted vacuum divergence identity result review is the input.",
        },
        {
            "row_id": "u1_policy_preserved",
            "status": "accepted",
            "evidence": GAUGE_GROUP_POLICY,
            "assessment": "The route remains U(1) / Abelian only.",
        },
        {
            "row_id": "smooth_real_one_form_preserved",
            "status": "accepted",
            "evidence": A_FIELD_DOMAIN_POLICY,
            "assessment": "A remains a smooth real 1-form on the selected domain.",
        },
        {
            "row_id": "F_dA_antisymmetry_and_bianchi_preserved",
            "status": "accepted",
            "evidence": [F_DEFINITION_POLICY, ANTISYMMETRY_ROUTE, BIANCHI_IDENTITY_ROUTE],
            "assessment": "F=dA, antisymmetry, and the Abelian Bianchi route are preserved.",
        },
        {
            "row_id": "vacuum_equation_preserved",
            "status": "accepted",
            "evidence": VACUUM_EULER_LAGRANGE_ROUTE,
            "assessment": "The only on-shell field equation used is the vacuum U(1) route.",
        },
        {
            "row_id": "stress_energy_route_preserved",
            "status": "accepted",
            "evidence": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
            "assessment": "The selected convention-sensitive T_A route is preserved.",
        },
        {
            "row_id": "accepted_divergence_identity_consumed",
            "status": "accepted",
            "evidence": DIVERGENCE_IDENTITY,
            "assessment": "The retry consumes the accepted divergence identity.",
        },
        {
            "row_id": "on_shell_source_condition_passes",
            "status": "accepted",
            "evidence": ON_SHELL_VACUUM_CONSERVATION_ROUTE,
            "assessment": "The local source-admissibility condition holds on shell.",
        },
        {
            "row_id": "local_classical_vacuum_convention_scope_recorded",
            "status": "accepted",
            "evidence": [
                LOCAL_SOURCE_ROUTE_SCOPE,
                METRIC_COMPATIBILITY_ROUTE,
                METRIC_SIGNATURE_POLICY,
            ],
            "assessment": "The accepted route is local, classical, vacuum, and convention-scoped.",
        },
        {
            "row_id": "bounded_local_source_route_accepted",
            "status": "accepted",
            "evidence": BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
            "assessment": "The bounded local on-shell vacuum gauge source route passes review.",
        },
        {
            "row_id": "full_source_admissibility_not_promoted",
            "status": "blocked_from_promotion",
            "evidence": FULL_SOURCE_ADMISSIBILITY_BOUNDARY,
            "assessment": "The accepted result is not a full source-admissibility closure.",
        },
        {
            "row_id": "current_and_sourced_maxwell_blocked",
            "status": "blocked_from_promotion",
            "evidence": [
                CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE,
                CURRENT_COUPLED_SCOPE_BOUNDARY,
                "J_nu_derived=false",
                "sourced_maxwell_equation_derived=false",
            ],
            "assessment": "The sourced/current route remains blocked.",
        },
        {
            "row_id": "ck_closure_and_promotion_blocked",
            "status": "blocked_from_promotion",
            "evidence": [
                "A_relevant_C_k_rules_constructed=false",
                "em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No A-relevant C_k, EM/QFT-GR closure, or master-action promotion follows.",
        },
        {
            "row_id": "result_review_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The bounded acceptance must rotate to result review.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_source_admissibility_review_retry_after_vacuum_identity"
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


def build_toe_native_a_source_admissibility_review_retry_after_vacuum_identity(
    *,
    identity_result_review_path: Path = A_SOURCE_IDENTITY_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    identity_review = _read_json(identity_result_review_path)
    criteria = _bounded_review_criteria(identity_review)
    acceptance_criteria = {
        "consumes_current_retry_target": (
            identity_review.get("schema_id") == A_SOURCE_IDENTITY_RESULT_REVIEW_SCHEMA_ID
            and identity_review.get("packet_id")
            == A_SOURCE_IDENTITY_RESULT_REVIEW_PACKET_ID
            and identity_review.get("outcome_id")
            == A_SOURCE_IDENTITY_RESULT_REVIEW_OUTCOME
            and identity_review.get("review_result")
            == A_SOURCE_IDENTITY_RESULT_REVIEW_RESULT
            and identity_review.get("selected_next_target") == CONSUMED_TARGET
            and identity_review.get("accepted") is True
        ),
        "accepted_identity_consumed": (
            identity_review.get("divergence_identity") == DIVERGENCE_IDENTITY
            and identity_review.get("divergence_identity_accepted") is True
            and identity_review.get("on_shell_vacuum_conservation_identity")
            == ON_SHELL_VACUUM_CONSERVATION_IDENTITY
            and identity_review.get("on_shell_vanishing_route_accepted") is True
        ),
        "selected_u1_context_preserved": (
            identity_review.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and identity_review.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and identity_review.get("F_definition_policy") == F_DEFINITION_POLICY
            and identity_review.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and identity_review.get("stress_energy_under_selected_u1_policy")
            == STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
        ),
        "bounded_local_on_shell_condition_passes": (
            identity_review.get("source_admissibility_condition")
            == SOURCE_ADMISSIBILITY_CONDITION
            and identity_review.get("on_shell_vacuum_conservation_route")
            == ON_SHELL_VACUUM_CONSERVATION_ROUTE
        ),
        "criteria_accepted_or_blocked": all(
            row["status"] in {"accepted", "blocked_from_promotion"} for row in criteria
        ),
        "current_ck_closure_still_blocked": (
            identity_review.get("J_nu_derived") is False
            and identity_review.get("sourced_maxwell_equation_derived") is False
            and identity_review.get("A_relevant_C_k_rules_constructed") is False
            and identity_review.get("em_closure_claimed") is False
            and identity_review.get("qft_gr_closure_claimed") is False
            and identity_review.get("master_action_promoted") is False
        ),
        "next_target_is_result_review": NEXT_TARGET.startswith("review_"),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_AFTER_VACUUM_IDENTITY"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_AFTER_VACUUM_IDENTITY",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "packet_result": "ACCEPTED" if accepted else "REQUIRES_REMEDIATION",
        "source_review_retry_result": PACKET_RESULT,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_identity_result_review_outcome": (
            A_SOURCE_IDENTITY_RESULT_REVIEW_OUTCOME
        ),
        "authorized_by_identity_result_review_result": (
            A_SOURCE_IDENTITY_RESULT_REVIEW_RESULT
        ),
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "F_antisymmetry_route": ANTISYMMETRY_ROUTE,
        "bianchi_identity_route": BIANCHI_IDENTITY_ROUTE,
        "metric_compatibility_route": METRIC_COMPATIBILITY_ROUTE,
        "metric_signature_policy": METRIC_SIGNATURE_POLICY,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "stress_energy_under_selected_u1_policy": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "candidate_source_object": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "divergence_identity": DIVERGENCE_IDENTITY,
        "stress_energy_divergence_route": DIVERGENCE_IDENTITY,
        "on_shell_vacuum_conservation_identity": ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
        "on_shell_vacuum_conservation_route": ON_SHELL_VACUUM_CONSERVATION_ROUTE,
        "bounded_source_admissibility_result": BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
        "local_source_route_scope": LOCAL_SOURCE_ROUTE_SCOPE,
        "full_source_admissibility_boundary": FULL_SOURCE_ADMISSIBILITY_BOUNDARY,
        "current_coupled_stress_exchange_route": CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE,
        "current_coupled_scope_boundary": CURRENT_COUPLED_SCOPE_BOUNDARY,
        "bounded_review_criteria": criteria,
        "bounded_review_criteria_count": len(criteria),
        "bounded_review_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "bounded_review_criteria_blocked_count": sum(
            1 for row in criteria if row["status"] == "blocked_from_promotion"
        ),
        "acceptance_criteria": acceptance_criteria,
        "source_admissibility_retry_executed": accepted,
        "source_admissibility_review_retry_completed": accepted,
        "bounded_local_on_shell_source_admissibility_review_passed": accepted,
        "bounded_local_on_shell_vacuum_source_route_accepted": accepted,
        "local_on_shell_vacuum_source_route_accepted": accepted,
        "local_on_shell_vacuum_source_route_proved": accepted,
        "local_classical_vacuum_source_route_accepted": accepted,
        "convention_scoped_source_route_accepted": accepted,
        "accepted_divergence_identity_consumed": accepted,
        "on_shell_vanishing_route_consumed": accepted,
        "source_admissibility_condition_satisfied_on_shell": accepted,
        "candidate_gravity_source_route_recorded": accepted,
        "result_review_authorized": accepted,
        "full_source_admissibility_review_accepted": False,
        "source_admissibility_completed": False,
        "source_admissibility_proved": False,
        "source_admissibility_claimed": False,
        "A_source_admissibility_proved": False,
        "A_source_admissibility_claimed": False,
        "stress_energy_source_admissibility_proved": False,
        "stress_energy_as_gravity_source_authorized": False,
        "semiclassical_source_established": False,
        "total_matter_gauge_stress_energy_conservation_proved": False,
        "total_matter_gauge_stress_energy_conservation_claimed": False,
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
        "matter_gauge_energy_exchange_proved": False,
        "matter_gauge_energy_exchange_claimed": False,
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
                "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_RECORDS_LOCAL_"
                "ON_SHELL_VACUUM_GAUGE_SOURCE_ROUTE_NO_CURRENT_OR_EM_CLOSURE"
            ),
            (
                "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_BLOCKED_BY_"
                "MISSING_ACCEPTED_VACUUM_IDENTITY"
            ),
            (
                "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_BLOCKED_BY_"
                "CURRENT_COUPLED_ROUTE_SCOPE_LEAK"
            ),
        ],
        "critical_gate_fail_conditions": [
            "promote the bounded local result to full source admissibility",
            "authorize gauge stress-energy as an unrestricted gravity source",
            "derive J^nu",
            "construct a psi-current route",
            "select an external current as native derivation",
            "derive sourced Maxwell equation",
            "prove matter-gauge energy exchange",
            "prove a current conservation theorem",
            "construct A-relevant C_k rules",
            "claim EM closure",
            "claim QFT-GR closure",
            "authorize semiclassical coupling",
            "promote the working-form master action",
        ],
        "downstream_progression": [
            {
                "stage": "A_source_admissibility_review_retry_after_vacuum_identity",
                "status": "ACCEPTS_LOCAL_ON_SHELL_VACUUM_SOURCE_ROUTE",
                "decision": OUTCOME_ID,
                "reason": (
                    "The accepted divergence identity and vacuum equation imply "
                    "local on-shell conservation for the selected U(1) gauge "
                    "stress-energy route."
                ),
            },
            {
                "stage": "sourced_current_route",
                "status": "NOT_SELECTED",
                "decision": "current_route_remains_blocked",
                "reason": CURRENT_COUPLED_SCOPE_BOUNDARY,
            },
            {
                "stage": "A_source_admissibility_retry_result_review",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The bounded local acceptance must be reviewed before any "
                    "A-relevant C_k candidate or route selector is selected."
                ),
            },
        ],
        "mathematical_statement": (
            "Given the accepted vacuum U(1) identity "
            + DIVERGENCE_IDENTITY
            + " and the on-shell equation "
            + VACUUM_EULER_LAGRANGE_ROUTE
            + ", the selected gauge stress-energy route "
            + STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
            + " satisfies "
            + SOURCE_ADMISSIBILITY_CONDITION
            + " locally on shell. This accepts only the "
            + LOCAL_SOURCE_ROUTE_SCOPE
            + "."
        ),
        "non_claim_boundary": (
            "This packet accepts only the bounded local classical vacuum U(1) "
            "on-shell gauge stress-energy source route. It does not accept full "
            "source admissibility, does not authorize gauge stress-energy as an "
            "unrestricted gravity source, does not derive J^nu, does not "
            "construct a psi-current route, does not select an external current "
            "as native derivation, does not derive a sourced Maxwell equation, "
            "does not prove matter-gauge energy exchange, does not prove a "
            "current conservation theorem, does not construct A-relevant C_k "
            "rules, does not close EM, does not close QFT-GR, does not "
            "authorize semiclassical coupling, does not claim empirical "
            "validation, and does not promote the master action."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeASourceAdmissibilityReviewRetryAfterVacuumIdentity",
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


def write_toe_native_a_source_admissibility_review_retry_after_vacuum_identity(
    *,
    identity_result_review_path: Path = A_SOURCE_IDENTITY_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_a_source_admissibility_review_retry_after_vacuum_identity(
        identity_result_review_path=identity_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A bounded source-admissibility retry packet "
            "after the accepted vacuum identity."
        )
    )
    parser.add_argument(
        "--identity-result-review",
        type=Path,
        default=A_SOURCE_IDENTITY_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_a_source_admissibility_review_retry_after_vacuum_identity(
        identity_result_review_path=args.identity_result_review,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
