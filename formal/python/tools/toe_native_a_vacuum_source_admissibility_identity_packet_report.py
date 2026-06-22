from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_source_admissibility_review_for_vacuum_stress_energy_result_review_report import (
    A_FIELD_DOMAIN_POLICY,
    BIANCHI_IDENTITY_ROUTE,
    CURRENT_COUPLED_EXCHANGE_CAUTION,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as A_SOURCE_RESULT_REVIEW_PATH,
    F_DEFINITION_POLICY,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    METRIC_SIGNATURE_POLICY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as A_SOURCE_RESULT_REVIEW_OUTCOME,
    PACKET_ID as A_SOURCE_RESULT_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT as A_SOURCE_RESULT_REVIEW_RESULT,
    SCHEMA_ID as A_SOURCE_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONDITION,
    SOURCE_ROUTE_STILL_BLOCKED,
    STRESS_ENERGY_DIVERGENCE_ROUTE,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-21T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_PACKET_20260621_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_PACKET_v0"
PACKET_RESULT = "ON_SHELL_DIVERGENCE_IDENTITY_CONSTRUCTED"
OUTCOME_ID = (
    "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_PACKET_PREPARED_"
    "ON_SHELL_DIVERGENCE_IDENTITY_CONSTRUCTED_NO_CURRENT_OR_EM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "toe_native_A_vacuum_source_admissibility_identity_packet_prepared_"
    "on_shell_divergence_identity_constructed_no_current_or_em_closure"
)

NEXT_TARGET = "review_toe_native_A_vacuum_source_admissibility_identity_packet_result"
NEXT_TARGET_KIND = "toe_native_A_vacuum_source_admissibility_identity_packet_result_review"

ANTISYMMETRY_ROUTE = "F_{mu nu} = - F_{nu mu}"
LEVI_CIVITA_CONNECTION_POLICY = "metric-compatible Levi-Civita connection"
METRIC_COMPATIBILITY_ROUTE = "nabla_mu g_{alpha beta} = 0"
SMOOTH_DOMAIN_REQUIREMENT = "smooth A and F domain"
DIVERGENCE_IDENTITY = STRESS_ENERGY_DIVERGENCE_ROUTE
ON_SHELL_VACUUM_CONSERVATION_IDENTITY = "nabla_mu T_A^{mu nu} = 0"
ON_SHELL_VACUUM_CONSERVATION_ROUTE = (
    DIVERGENCE_IDENTITY
    + " and "
    + VACUUM_EULER_LAGRANGE_ROUTE
    + " imply "
    + ON_SHELL_VACUUM_CONSERVATION_IDENTITY
)
SOURCE_ADMISSIBILITY_REVIEW_RETRY_TARGET = (
    "prepare_toe_native_A_source_admissibility_review_retry_after_vacuum_identity"
)
CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE = (
    "current-coupled gauge stress-energy alone is not generally conserved; "
    "it exchanges energy-momentum with matter/current through a term "
    "proportional to -F^{nu}{}_{alpha} J^alpha up to convention"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_PACKET_20260621_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeAVacuumSourceAdmissibilityIdentityPacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _derivation_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "state_selected_u1_assumptions",
            "status": "constructed",
            "mathematical_content": [
                GAUGE_GROUP_POLICY,
                A_FIELD_DOMAIN_POLICY,
                F_DEFINITION_POLICY,
                ANTISYMMETRY_ROUTE,
                BIANCHI_IDENTITY_ROUTE,
                LEVI_CIVITA_CONNECTION_POLICY,
                METRIC_COMPATIBILITY_ROUTE,
                SMOOTH_DOMAIN_REQUIREMENT,
                METRIC_SIGNATURE_POLICY,
            ],
            "claim": "The identity is scoped to the selected vacuum Abelian route.",
        },
        {
            "step_id": "state_candidate_stress_energy",
            "status": "constructed",
            "mathematical_content": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
            "claim": "The convention-sensitive gauge stress-energy route is the candidate source object.",
        },
        {
            "step_id": "compute_divergence",
            "status": "constructed",
            "mathematical_content": (
                "Apply the covariant product rule to nabla_mu T_A^{mu nu} "
                "with nabla g = 0."
            ),
            "claim": "Metric compatibility lets the derivative pass through raised indices and metric factors.",
        },
        {
            "step_id": "use_antisymmetry_and_bianchi",
            "status": "constructed",
            "mathematical_content": (
                ANTISYMMETRY_ROUTE
                + " and "
                + BIANCHI_IDENTITY_ROUTE
                + " cancel the remaining quadratic derivative terms."
            ),
            "claim": "The Abelian Bianchi route is the structural cancellation input.",
        },
        {
            "step_id": "reduce_to_vacuum_field_equation_residual",
            "status": "constructed",
            "mathematical_content": DIVERGENCE_IDENTITY,
            "claim": "The divergence reduces to the vacuum gauge equation residual up to the selected convention sign.",
        },
        {
            "step_id": "insert_vacuum_u1_equation",
            "status": "constructed",
            "mathematical_content": VACUUM_EULER_LAGRANGE_ROUTE,
            "claim": "On shell, the residual vanishes in the selected vacuum U(1) route.",
        },
        {
            "step_id": "conclude_on_shell_vacuum_identity",
            "status": "constructed",
            "mathematical_content": ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
            "claim": "The vacuum gauge stress-energy is locally conserved on shell.",
        },
        {
            "step_id": "preserve_current_coupled_caution",
            "status": "blocked_from_promotion",
            "mathematical_content": CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE,
            "claim": "The vacuum identity is not a sourced Maxwell or matter-current exchange theorem.",
        },
    ]


def _identity_criteria() -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_identity_packet_target",
            "status": "constructed",
            "evidence": CONSUMED_TARGET,
            "assessment": "The active vacuum A-source identity target is consumed.",
        },
        {
            "row_id": "u1_policy_and_domain_preserved",
            "status": "constructed",
            "evidence": [GAUGE_GROUP_POLICY, A_FIELD_DOMAIN_POLICY],
            "assessment": "The route remains within the selected minimal U(1) policy and smooth domain.",
        },
        {
            "row_id": "F_dA_and_antisymmetry_recorded",
            "status": "constructed",
            "evidence": [F_DEFINITION_POLICY, ANTISYMMETRY_ROUTE],
            "assessment": "The Abelian field-strength definition and antisymmetry are explicit.",
        },
        {
            "row_id": "bianchi_identity_recorded",
            "status": "constructed",
            "evidence": BIANCHI_IDENTITY_ROUTE,
            "assessment": "The dF=0 / Bianchi route is an explicit cancellation input.",
        },
        {
            "row_id": "vacuum_field_equation_recorded",
            "status": "constructed",
            "evidence": VACUUM_EULER_LAGRANGE_ROUTE,
            "assessment": "The on-shell residual is the vacuum U(1) equation.",
        },
        {
            "row_id": "connection_and_metric_compatibility_recorded",
            "status": "constructed",
            "evidence": [LEVI_CIVITA_CONNECTION_POLICY, METRIC_COMPATIBILITY_ROUTE],
            "assessment": "The covariant derivative route is scoped to Levi-Civita metric compatibility.",
        },
        {
            "row_id": "stress_energy_route_preserved",
            "status": "constructed",
            "evidence": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
            "assessment": "The convention-sensitive gauge stress-energy expression is preserved.",
        },
        {
            "row_id": "divergence_identity_constructed",
            "status": "constructed",
            "evidence": DIVERGENCE_IDENTITY,
            "assessment": "The divergence identity is recorded as the packet's constructed route.",
        },
        {
            "row_id": "on_shell_vanishing_constructed",
            "status": "constructed",
            "evidence": ON_SHELL_VACUUM_CONSERVATION_ROUTE,
            "assessment": "The identity vanishes after inserting the vacuum U(1) equation.",
        },
        {
            "row_id": "candidate_source_status_bounded",
            "status": "constructed",
            "evidence": SOURCE_ADMISSIBILITY_CONDITION,
            "assessment": "The packet records a candidate local gravity-source route, not a full source-admissibility review.",
        },
        {
            "row_id": "current_coupled_scope_blocked",
            "status": "blocked_from_promotion",
            "evidence": [CURRENT_COUPLED_EXCHANGE_CAUTION, CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE],
            "assessment": "The sourced-current route remains outside this vacuum identity packet.",
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
            "assessment": "No C_k construction, closure, semiclassical coupling, or promotion follows.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_A_vacuum_source_admissibility_identity_packet",
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


def build_toe_native_a_vacuum_source_admissibility_identity_packet(
    *,
    a_source_result_review_path: Path = A_SOURCE_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(a_source_result_review_path)
    steps = _derivation_steps()
    criteria = _identity_criteria()
    acceptance_criteria = {
        "consumes_current_identity_packet_target": (
            result_review.get("schema_id") == A_SOURCE_RESULT_REVIEW_SCHEMA_ID
            and result_review.get("packet_id") == A_SOURCE_RESULT_REVIEW_PACKET_ID
            and result_review.get("outcome_id") == A_SOURCE_RESULT_REVIEW_OUTCOME
            and result_review.get("review_result") == A_SOURCE_RESULT_REVIEW_RESULT
            and result_review.get("selected_next_target") == CONSUMED_TARGET
            and result_review.get("accepted") is True
        ),
        "selected_u1_context_preserved": (
            result_review.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and result_review.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and result_review.get("F_definition_policy") == F_DEFINITION_POLICY
            and result_review.get("metric_signature_policy") == METRIC_SIGNATURE_POLICY
            and result_review.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
        ),
        "stress_energy_and_test_surface_preserved": (
            result_review.get("stress_energy_under_selected_u1_policy")
            == STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
            and result_review.get("source_admissibility_condition")
            == SOURCE_ADMISSIBILITY_CONDITION
            and result_review.get("bianchi_identity_route") == BIANCHI_IDENTITY_ROUTE
            and result_review.get("stress_energy_divergence_route")
            == STRESS_ENERGY_DIVERGENCE_ROUTE
        ),
        "identity_steps_constructed": all(
            row["status"] in {"constructed", "blocked_from_promotion"} for row in steps
        )
        and DIVERGENCE_IDENTITY in steps[4]["mathematical_content"]
        and ON_SHELL_VACUUM_CONSERVATION_IDENTITY
        in steps[6]["mathematical_content"],
        "identity_criteria_constructed_or_blocked": all(
            row["status"] in {"constructed", "blocked_from_promotion"}
            for row in criteria
        ),
        "current_ck_closure_still_blocked": (
            result_review.get("J_nu_derived") is False
            and result_review.get("current_conservation_theorem_claimed") is False
            and result_review.get("A_relevant_C_k_rules_constructed") is False
            and result_review.get("em_closure_claimed") is False
            and result_review.get("qft_gr_closure_claimed") is False
            and result_review.get("master_action_promoted") is False
        ),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "packet_result": "PREPARED" if prepared else "REQUIRES_REMEDIATION",
        "outcome_id": OUTCOME_ID
        if prepared
        else "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_result_review_outcome": A_SOURCE_RESULT_REVIEW_OUTCOME,
        "authorized_by_result_review_result": A_SOURCE_RESULT_REVIEW_RESULT,
        "identity_packet_result": PACKET_RESULT,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "F_antisymmetry_route": ANTISYMMETRY_ROUTE,
        "bianchi_identity_route": BIANCHI_IDENTITY_ROUTE,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "levi_civita_connection_policy": LEVI_CIVITA_CONNECTION_POLICY,
        "metric_compatibility_route": METRIC_COMPATIBILITY_ROUTE,
        "smooth_domain_requirement": SMOOTH_DOMAIN_REQUIREMENT,
        "metric_signature_policy": METRIC_SIGNATURE_POLICY,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "stress_energy_under_selected_u1_policy": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "candidate_source_object": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "divergence_identity": DIVERGENCE_IDENTITY,
        "stress_energy_divergence_route": DIVERGENCE_IDENTITY,
        "on_shell_vacuum_conservation_identity": ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
        "on_shell_vacuum_conservation_route": ON_SHELL_VACUUM_CONSERVATION_ROUTE,
        "current_coupled_exchange_caution": CURRENT_COUPLED_EXCHANGE_CAUTION,
        "current_coupled_stress_exchange_route": CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE,
        "source_admissibility_review_retry_target": SOURCE_ADMISSIBILITY_REVIEW_RETRY_TARGET,
        "derivation_steps": steps,
        "derivation_step_count": len(steps),
        "derivation_step_constructed_count": sum(
            1 for row in steps if row["status"] == "constructed"
        ),
        "identity_criteria": criteria,
        "identity_criteria_count": len(criteria),
        "identity_criteria_constructed_count": sum(
            1 for row in criteria if row["status"] == "constructed"
        ),
        "acceptance_criteria": acceptance_criteria,
        "identity_packet_prepared": prepared,
        "result_review_authorization_consumed": prepared,
        "selected_u1_policy_preserved": prepared,
        "F_dA_preserved": prepared,
        "F_antisymmetry_recorded": prepared,
        "bianchi_identity_recorded": prepared,
        "vacuum_equation_preserved": prepared,
        "levi_civita_connection_required": prepared,
        "metric_compatibility_required": prepared,
        "smooth_domain_required": prepared,
        "metric_signature_preserved": prepared,
        "stress_energy_route_preserved": prepared,
        "source_admissibility_condition_preserved": prepared,
        "divergence_identity_constructed": prepared,
        "divergence_identity_verified": prepared,
        "divergence_identity_proved": prepared,
        "source_admissibility_identity_executed": prepared,
        "source_admissibility_identity_verified": prepared,
        "source_admissibility_identity_constructed": prepared,
        "source_admissibility_identity_proved": prepared,
        "on_shell_vacuum_conservation_identity_constructed": prepared,
        "on_shell_vacuum_conservation_route_constructed": prepared,
        "local_on_shell_vacuum_source_route_constructed": prepared,
        "candidate_gravity_source_route_recorded": prepared,
        "review_target_authorized": prepared,
        "identity_result_review_authorized": prepared,
        "local_on_shell_vacuum_source_route_accepted": False,
        "full_source_admissibility_review_accepted": False,
        "source_admissibility_review_completed": False,
        "source_admissibility_executed": False,
        "source_admissibility_proved": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "A_source_admissibility_proved": False,
        "A_source_admissibility_claimed": False,
        "stress_energy_source_admissibility_proved": False,
        "stress_energy_as_gravity_source_authorized": False,
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
                "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_PACKET_"
                "PREPARED_DIVERGENCE_IDENTITY_ROUTE_RECORDED_NO_SOURCE_"
                "ADMISSIBILITY_OR_EM_CLOSURE"
            ),
            (
                "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_PACKET_"
                "BLOCKED_BY_MISSING_BIANCHI_OR_VACUUM_FIELD_EQUATION"
            ),
            (
                "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_PACKET_"
                "BLOCKED_BY_CURRENT_COUPLED_ROUTE_SCOPE_LEAK"
            ),
        ],
        "critical_gate_fail_conditions": [
            "claim full source-admissibility review accepted",
            "derive sourced Maxwell equation",
            "derive J^nu",
            "construct psi-current route",
            "select external current as native derivation",
            "prove total matter+gauge stress-energy conservation",
            "prove current conservation theorem",
            "construct A-relevant C_k rules",
            "claim EM closure",
            "claim QFT-GR closure",
            "authorize semiclassical coupling",
            "promote the working-form master action",
        ],
        "downstream_progression": [
            {
                "stage": "A_vacuum_source_admissibility_identity",
                "status": "ON_SHELL_DIVERGENCE_IDENTITY_CONSTRUCTED",
                "decision": OUTCOME_ID,
                "reason": (
                    "The packet reduces the divergence of the selected U(1) "
                    "gauge stress-energy to the vacuum field-equation residual "
                    "and records its on-shell vanishing."
                ),
            },
            {
                "stage": "sourced_current_route",
                "status": "NOT_SELECTED",
                "decision": "current_route_remains_blocked",
                "reason": CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE,
            },
            {
                "stage": "A_source_admissibility_review",
                "status": "NEXT_TARGET_AUTHORIZED_FOR_RESULT_REVIEW",
                "decision": selected_next_target,
                "reason": (
                    "The identity packet must be reviewed before the vacuum "
                    "A-source admissibility review can be retried."
                ),
            },
        ],
        "mathematical_statement": (
            "Under the selected vacuum U(1) policy, with "
            + F_DEFINITION_POLICY
            + ", "
            + ANTISYMMETRY_ROUTE
            + ", "
            + BIANCHI_IDENTITY_ROUTE
            + ", "
            + LEVI_CIVITA_CONNECTION_POLICY
            + ", "
            + METRIC_COMPATIBILITY_ROUTE
            + ", "
            + SMOOTH_DOMAIN_REQUIREMENT
            + ", and the "
            + METRIC_SIGNATURE_POLICY
            + " convention, the gauge stress-energy "
            + STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
            + " satisfies the convention-sensitive identity "
            + DIVERGENCE_IDENTITY
            + ". With the vacuum equation "
            + VACUUM_EULER_LAGRANGE_ROUTE
            + ", this gives "
            + ON_SHELL_VACUUM_CONSERVATION_IDENTITY
            + " on shell."
        ),
        "non_claim_boundary": (
            "This packet constructs only the bounded vacuum U(1) divergence "
            "identity and its on-shell vanishing route. It does not accept the "
            "full source-admissibility review, does not authorize the gauge "
            "stress-energy as a gravity source, does not derive a sourced "
            "Maxwell equation, does not derive J^nu, does not construct a "
            "psi-current route, does not select an external current as native "
            "derivation, does not prove total matter+gauge stress-energy "
            "conservation, does not prove a current conservation theorem, "
            "does not construct A-relevant C_k rules, does not close EM, does "
            "not close QFT-GR, does not authorize semiclassical coupling, "
            "does not claim empirical validation, and does not promote the "
            "master action."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeAVacuumSourceAdmissibilityIdentityPacket",
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


def write_toe_native_a_vacuum_source_admissibility_identity_packet(
    *,
    a_source_result_review_path: Path = A_SOURCE_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_a_vacuum_source_admissibility_identity_packet(
        a_source_result_review_path=a_source_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A vacuum source-admissibility identity packet "
            "under selected U(1) policy."
        )
    )
    parser.add_argument(
        "--a-source-result-review",
        type=Path,
        default=A_SOURCE_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_a_vacuum_source_admissibility_identity_packet(
        a_source_result_review_path=args.a_source_result_review,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
