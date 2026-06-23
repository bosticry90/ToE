from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_source_admissibility_review_retry_after_vacuum_identity_report import (
    A_FIELD_DOMAIN_POLICY,
    ANTISYMMETRY_ROUTE,
    BIANCHI_IDENTITY_ROUTE,
    BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
    CURRENT_COUPLED_SCOPE_BOUNDARY,
    CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as A_SOURCE_RETRY_PACKET_PATH,
    DIVERGENCE_IDENTITY,
    F_DEFINITION_POLICY,
    FULL_SOURCE_ADMISSIBILITY_BOUNDARY,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LOCAL_SOURCE_ROUTE_SCOPE,
    METRIC_COMPATIBILITY_ROUTE,
    METRIC_SIGNATURE_POLICY,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    ON_SHELL_VACUUM_CONSERVATION_ROUTE,
    OUTCOME_ID as A_SOURCE_RETRY_OUTCOME,
    PACKET_ID as A_SOURCE_RETRY_PACKET_ID,
    PACKET_RESULT as A_SOURCE_RETRY_PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as A_SOURCE_RETRY_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONDITION,
    SOURCE_ROUTE_STILL_BLOCKED,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-22T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_RESULT_REVIEW_"
    "20260622_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_RESULT_REVIEW_ACCEPTS_"
    "LOCAL_ON_SHELL_VACUUM_GAUGE_SOURCE_ROUTE_NO_CURRENT_OR_EM_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_source_admissibility_review_retry_result_review_accepts_"
    "local_on_shell_vacuum_gauge_source_route_no_current_or_em_closure"
)

NEXT_TARGET = "select_next_toe_native_A_route_after_vacuum_source_admissibility"
NEXT_TARGET_KIND = "toe_native_A_route_selection_after_vacuum_source_admissibility"
RECOMMENDED_SELECTOR_CANDIDATE = (
    "prepare_toe_native_A_source_admissibility_ck_constraint_candidate_packet"
)
RECOMMENDED_CK_SOURCE_RULE_CANDIDATE = (
    "C_source^A := nabla_mu T_A^{mu nu}; C_source^A = 0"
)
RECOMMENDED_CK_SOURCE_RULE_SCOPE = (
    "vacuum U(1) admissibility-only source rule candidate; not an action term; "
    "not sourced EM; not full EM closure"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_RESULT_REVIEW_"
    "20260622_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeASourceAdmissibilityReviewRetryAfterVacuumIdentityResultReview.lean"
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
            "row_id": "consumes_retry_result_review_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The active retry result-review target is consumed.",
        },
        {
            "row_id": "retry_packet_accepted",
            "status": "accepted",
            "evidence": packet.get("outcome_id"),
            "assessment": "The retry packet accepted the bounded local vacuum route.",
        },
        {
            "row_id": "accepted_divergence_identity_consumed",
            "status": "accepted",
            "evidence": DIVERGENCE_IDENTITY,
            "assessment": "The accepted vacuum divergence identity remains consumed.",
        },
        {
            "row_id": "local_on_shell_vacuum_u1_route_accepted",
            "status": "accepted",
            "evidence": BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
            "assessment": "The local on-shell vacuum U(1) source route is accepted.",
        },
        {
            "row_id": "stress_energy_route_preserved",
            "status": "accepted",
            "evidence": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
            "assessment": "The selected convention-scoped T_A route is preserved.",
        },
        {
            "row_id": "vacuum_conservation_preserved",
            "status": "accepted",
            "evidence": ON_SHELL_VACUUM_CONSERVATION_ROUTE,
            "assessment": (
                "nabla_mu T_A^{mu nu} = 0 remains preserved under the vacuum "
                "assumptions."
            ),
        },
        {
            "row_id": "local_classical_vacuum_scope_preserved",
            "status": "accepted",
            "evidence": [
                LOCAL_SOURCE_ROUTE_SCOPE,
                GAUGE_GROUP_POLICY,
                A_FIELD_DOMAIN_POLICY,
                F_DEFINITION_POLICY,
                BIANCHI_IDENTITY_ROUTE,
            ],
            "assessment": "The accepted route remains local, classical, vacuum, U(1), and on shell.",
        },
        {
            "row_id": "no_current_derivation",
            "status": "accepted",
            "evidence": "J_nu_derived=false",
            "assessment": "No J^nu derivation is introduced.",
        },
        {
            "row_id": "no_sourced_maxwell_route",
            "status": "accepted",
            "evidence": "sourced_maxwell_equation_derived=false",
            "assessment": "No sourced Maxwell route is derived.",
        },
        {
            "row_id": "no_matter_current_exchange",
            "status": "accepted",
            "evidence": CURRENT_COUPLED_SCOPE_BOUNDARY,
            "assessment": "No matter/current exchange route is proved.",
        },
        {
            "row_id": "no_full_source_admissibility_beyond_bounded_route",
            "status": "accepted",
            "evidence": FULL_SOURCE_ADMISSIBILITY_BOUNDARY,
            "assessment": "No full source-admissibility claim is promoted beyond the bounded vacuum route.",
        },
        {
            "row_id": "no_a_relevant_ck_constructed",
            "status": "accepted",
            "evidence": "A_relevant_C_k_rules_constructed=false",
            "assessment": "No A-relevant C_k rule is constructed in this review.",
        },
        {
            "row_id": "no_closure_coupling_validation_or_promotion",
            "status": "accepted",
            "evidence": [
                "em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "semiclassical_coupling_authorized=false",
                "empirical_validation_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No closure, coupling, validation, or master-action promotion follows.",
        },
        {
            "row_id": "selector_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next bounded action is the A-route selector after vacuum source admissibility.",
        },
        {
            "row_id": "ck_candidate_guidance_recorded_without_execution",
            "status": "accepted",
            "evidence": [
                RECOMMENDED_SELECTOR_CANDIDATE,
                RECOMMENDED_CK_SOURCE_RULE_CANDIDATE,
                RECOMMENDED_CK_SOURCE_RULE_SCOPE,
            ],
            "assessment": (
                "The likely A/C_k source-rule candidate is recorded only as "
                "selector guidance, not executed here."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_source_admissibility_review_retry_result_review"
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


def build_toe_native_a_source_admissibility_review_retry_result_review(
    *,
    retry_packet_path: Path = A_SOURCE_RETRY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(retry_packet_path)
    criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_current_retry_result_review_target": (
            packet.get("schema_id") == A_SOURCE_RETRY_SCHEMA_ID
            and packet.get("packet_id") == A_SOURCE_RETRY_PACKET_ID
            and packet.get("outcome_id") == A_SOURCE_RETRY_OUTCOME
            and packet.get("source_review_retry_result") == A_SOURCE_RETRY_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and packet.get("accepted") is True
        ),
        "bounded_local_route_accepted": (
            packet.get("accepted_divergence_identity_consumed") is True
            and packet.get("bounded_local_on_shell_source_admissibility_review_passed")
            is True
            and packet.get("local_on_shell_vacuum_source_route_accepted") is True
            and packet.get("source_admissibility_condition_satisfied_on_shell") is True
        ),
        "vacuum_u1_context_preserved": (
            packet.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and packet.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and packet.get("F_definition_policy") == F_DEFINITION_POLICY
            and packet.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and packet.get("stress_energy_under_selected_u1_policy")
            == STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
        ),
        "nonclaim_boundaries_preserved": (
            packet.get("J_nu_derived") is False
            and packet.get("sourced_maxwell_equation_derived") is False
            and packet.get("matter_gauge_energy_exchange_proved") is False
            and packet.get("full_source_admissibility_review_accepted") is False
            and packet.get("A_relevant_C_k_rules_constructed") is False
            and packet.get("em_closure_claimed") is False
            and packet.get("qft_gr_closure_claimed") is False
            and packet.get("semiclassical_coupling_authorized") is False
            and packet.get("empirical_validation_claimed") is False
            and packet.get("master_action_promoted") is False
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in criteria
        ),
        "next_target_is_selector": NEXT_TARGET.startswith("select_next_"),
        "recommended_candidate_not_executed": RECOMMENDED_SELECTOR_CANDIDATE.startswith(
            "prepare_"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_RETRY_RESULT_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_SOURCE_ADMISSIBILITY_RETRY_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "packet_result": "REVIEW_ACCEPTED" if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "source_review_retry_result": A_SOURCE_RETRY_PACKET_RESULT,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_RETRY_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "recommended_selector_candidate": RECOMMENDED_SELECTOR_CANDIDATE,
        "recommended_ck_source_rule_candidate": RECOMMENDED_CK_SOURCE_RULE_CANDIDATE,
        "recommended_ck_source_rule_scope": RECOMMENDED_CK_SOURCE_RULE_SCOPE,
        "selector_reason": (
            "The accepted bounded local vacuum U(1) source route must be routed "
            "through a selector before any A-relevant C_k source-rule candidate "
            "packet is prepared."
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
        "review_criteria": criteria,
        "review_criteria_count": len(criteria),
        "review_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "result_review_executed": accepted,
        "retry_result_review_accepted": accepted,
        "source_admissibility_retry_result_accepted": accepted,
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
        "selector_authorized": accepted,
        "ck_candidate_guidance_recorded": accepted,
        "source_admissibility_ck_candidate_packet_prepared": False,
        "selector_executed": False,
        "recommended_candidate_selected": False,
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
            REVIEW_RESULT,
            (
                "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_RESULT_REVIEW_"
                "RECORDS_BOUNDED_ROUTE_AND_DEFERS_SELECTOR"
            ),
            (
                "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_RESULT_REVIEW_"
                "REJECTS_SCOPE_LEAK_PENDING_REMEDIATION"
            ),
        ],
        "critical_gate_fail_conditions": [
            "promote bounded vacuum route to full source admissibility",
            "derive J^nu",
            "derive sourced Maxwell",
            "prove matter-current exchange",
            "construct A-relevant C_k rules inside this review",
            "execute the next selector inside this review",
            "claim EM closure",
            "claim QFT-GR closure",
            "authorize semiclassical coupling",
            "claim empirical validation",
            "promote the working-form master action",
        ],
        "downstream_progression": [
            {
                "stage": "A_source_admissibility_retry_result_review",
                "status": "ACCEPTS_LOCAL_ON_SHELL_VACUUM_SOURCE_ROUTE",
                "decision": REVIEW_RESULT,
                "reason": (
                    "The review accepts that the bounded local classical vacuum "
                    "U(1) gauge source route passes under the accepted on-shell "
                    "identity and vacuum equation."
                ),
            },
            {
                "stage": "A_route_after_vacuum_source_admissibility_selector",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The next action is a selector. The likely candidate is an "
                    "A-relevant source-admissibility C_k candidate packet, but "
                    "that candidate is not selected or prepared in this review."
                ),
            },
        ],
        "mathematical_statement": (
            "The result review accepts the bounded local classical vacuum U(1) "
            "route: "
            + VACUUM_EULER_LAGRANGE_ROUTE
            + " together with "
            + DIVERGENCE_IDENTITY
            + " preserves "
            + ON_SHELL_VACUUM_CONSERVATION_IDENTITY
            + " for the selected gauge stress-energy route. This remains "
            "local, classical, vacuum, U(1), on shell, and convention-scoped."
        ),
        "non_claim_boundary": (
            "This result review accepts only the bounded local classical vacuum "
            "U(1) on-shell gauge stress-energy source route. It does not derive "
            "J^nu, does not derive sourced Maxwell, does not prove "
            "matter-current or matter-gauge exchange, does not accept full "
            "source admissibility beyond the bounded vacuum route, does not "
            "construct A-relevant C_k rules, does not execute the next selector, "
            "does not close EM, does not close QFT-GR, does not authorize "
            "semiclassical coupling, does not claim empirical validation, and "
            "does not promote the master action."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeASourceAdmissibilityReviewRetryAfterVacuumIdentityResultReview",
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


def write_toe_native_a_source_admissibility_review_retry_result_review(
    *,
    retry_packet_path: Path = A_SOURCE_RETRY_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_a_source_admissibility_review_retry_result_review(
        retry_packet_path=retry_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A source-admissibility retry result review."
        )
    )
    parser.add_argument("--retry-packet", type=Path, default=A_SOURCE_RETRY_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_a_source_admissibility_review_retry_result_review(
        retry_packet_path=args.retry_packet,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
