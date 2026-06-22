from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_vacuum_source_admissibility_identity_packet_report import (
    A_FIELD_DOMAIN_POLICY,
    ANTISYMMETRY_ROUTE,
    BIANCHI_IDENTITY_ROUTE,
    CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as A_SOURCE_IDENTITY_PACKET_PATH,
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
    OUTCOME_ID as A_SOURCE_IDENTITY_PACKET_OUTCOME,
    PACKET_ID as A_SOURCE_IDENTITY_PACKET_ID,
    PACKET_RESULT as A_SOURCE_IDENTITY_PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as A_SOURCE_IDENTITY_PACKET_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONDITION,
    SOURCE_ADMISSIBILITY_REVIEW_RETRY_TARGET as NEXT_TARGET,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-21T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_RESULT_REVIEW_"
    "20260621_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_RESULT_REVIEW_ACCEPTS_"
    "ON_SHELL_DIVERGENCE_IDENTITY_NO_CURRENT_OR_EM_CLOSURE"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_vacuum_source_admissibility_identity_result_review_accepts_"
    "on_shell_divergence_identity_no_current_or_em_closure"
)
NEXT_TARGET_KIND = "toe_native_A_source_admissibility_review_retry_after_vacuum_identity"

RETRY_REASON = (
    "The identity result review accepts the bounded on-shell vacuum U(1) "
    "divergence identity. The next packet may retry the local source-"
    "admissibility review, while still blocking current coupling and EM/QFT-GR "
    "closure."
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_RESULT_REVIEW_"
    "20260621_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeAVacuumSourceAdmissibilityIdentityResultReview.lean"
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
            "row_id": "consumes_identity_result_review_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The active A vacuum identity result-review target is consumed.",
        },
        {
            "row_id": "u1_policy_preserved",
            "status": "accepted",
            "evidence": [GAUGE_GROUP_POLICY, A_FIELD_DOMAIN_POLICY],
            "assessment": "The selected U(1) policy and smooth A-domain are preserved.",
        },
        {
            "row_id": "F_dA_and_antisymmetry_preserved",
            "status": "accepted",
            "evidence": [F_DEFINITION_POLICY, ANTISYMMETRY_ROUTE],
            "assessment": "F=dA and the Abelian antisymmetry route are preserved.",
        },
        {
            "row_id": "stress_energy_route_preserved",
            "status": "accepted",
            "evidence": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
            "assessment": "The convention-sensitive T_A route is preserved.",
        },
        {
            "row_id": "divergence_identity_accepted",
            "status": "accepted",
            "evidence": packet.get("divergence_identity"),
            "assessment": "The bounded divergence identity is accepted as constructed.",
        },
        {
            "row_id": "vacuum_field_equation_preserved",
            "status": "accepted",
            "evidence": packet.get("vacuum_euler_lagrange_route"),
            "assessment": "The vacuum U(1) equation remains the on-shell input.",
        },
        {
            "row_id": "on_shell_vanishing_route_accepted",
            "status": "accepted",
            "evidence": packet.get("on_shell_vacuum_conservation_route"),
            "assessment": "The on-shell vanishing route is recorded and accepted.",
        },
        {
            "row_id": "source_admissibility_condition_retained_for_retry",
            "status": "accepted",
            "evidence": SOURCE_ADMISSIBILITY_CONDITION,
            "assessment": "The source-admissibility condition is retained for the retry packet.",
        },
        {
            "row_id": "current_coupled_caution_preserved",
            "status": "accepted",
            "evidence": CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE,
            "assessment": "The sourced-current exchange route remains outside this review.",
        },
        {
            "row_id": "no_current_or_sourced_maxwell",
            "status": "accepted",
            "evidence": ["J_nu_derived=false", "sourced_maxwell_equation_derived=false"],
            "assessment": "No current or sourced Maxwell route is derived.",
        },
        {
            "row_id": "no_full_source_admissibility_acceptance",
            "status": "accepted",
            "evidence": "full_source_admissibility_review_accepted=false",
            "assessment": "The review does not accept the full source-admissibility retry.",
        },
        {
            "row_id": "no_a_relevant_ck_construction",
            "status": "accepted",
            "evidence": "A_relevant_C_k_rules_constructed=false",
            "assessment": "No A-relevant C_k rules are constructed.",
        },
        {
            "row_id": "no_closure_coupling_or_promotion",
            "status": "accepted",
            "evidence": [
                "em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "semiclassical_coupling_authorized=false",
                "master_action_promoted=false",
            ],
            "assessment": "No closure, semiclassical coupling, or promotion follows.",
        },
        {
            "row_id": "retry_target_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": RETRY_REASON,
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_vacuum_source_admissibility_identity_result_review"
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


def build_toe_native_a_vacuum_source_admissibility_identity_result_review(
    *,
    identity_packet_path: Path = A_SOURCE_IDENTITY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(identity_packet_path)
    criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_current_identity_result_review_target": (
            packet.get("schema_id") == A_SOURCE_IDENTITY_PACKET_SCHEMA_ID
            and packet.get("packet_id") == A_SOURCE_IDENTITY_PACKET_ID
            and packet.get("outcome_id") == A_SOURCE_IDENTITY_PACKET_OUTCOME
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "identity_constructed_and_on_shell_route_recorded": (
            packet.get("identity_packet_result") == A_SOURCE_IDENTITY_PACKET_RESULT
            and packet.get("divergence_identity") == DIVERGENCE_IDENTITY
            and packet.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and packet.get("on_shell_vacuum_conservation_identity")
            == ON_SHELL_VACUUM_CONSERVATION_IDENTITY
            and packet.get("on_shell_vacuum_conservation_route")
            == ON_SHELL_VACUUM_CONSERVATION_ROUTE
        ),
        "selected_u1_context_preserved": (
            packet.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and packet.get("F_definition_policy") == F_DEFINITION_POLICY
            and packet.get("stress_energy_under_selected_u1_policy")
            == STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
        ),
        "source_retry_not_already_accepted": (
            packet.get("full_source_admissibility_review_accepted") is False
            and packet.get("source_admissibility_proved") is False
            and packet.get("stress_energy_as_gravity_source_authorized") is False
        ),
        "current_ck_closure_still_blocked": (
            packet.get("J_nu_derived") is False
            and packet.get("sourced_maxwell_equation_derived") is False
            and packet.get("A_relevant_C_k_rules_constructed") is False
            and packet.get("em_closure_claimed") is False
            and packet.get("qft_gr_closure_claimed") is False
            and packet.get("master_action_promoted") is False
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in criteria
        ),
        "next_target_is_source_admissibility_retry": NEXT_TARGET.startswith("prepare_"),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_RESULT_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_VACUUM_SOURCE_IDENTITY_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "packet_result": "REVIEW_ACCEPTED" if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "identity_packet_outcome": A_SOURCE_IDENTITY_PACKET_OUTCOME,
        "identity_packet_result": A_SOURCE_IDENTITY_PACKET_RESULT,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "F_antisymmetry_route": ANTISYMMETRY_ROUTE,
        "bianchi_identity_route": BIANCHI_IDENTITY_ROUTE,
        "metric_compatibility_route": METRIC_COMPATIBILITY_ROUTE,
        "metric_signature_policy": METRIC_SIGNATURE_POLICY,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "stress_energy_under_selected_u1_policy": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "divergence_identity": DIVERGENCE_IDENTITY,
        "stress_energy_divergence_route": DIVERGENCE_IDENTITY,
        "on_shell_vacuum_conservation_identity": ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
        "on_shell_vacuum_conservation_route": ON_SHELL_VACUUM_CONSERVATION_ROUTE,
        "current_coupled_stress_exchange_route": CURRENT_COUPLED_STRESS_EXCHANGE_ROUTE,
        "retry_reason": RETRY_REASON,
        "review_criteria": criteria,
        "review_criteria_count": len(criteria),
        "review_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "result_review_executed": accepted,
        "identity_result_review_executed": accepted,
        "identity_result_review_accepted": accepted,
        "u1_policy_preserved": accepted,
        "F_dA_preserved": accepted,
        "F_antisymmetry_preserved": accepted,
        "stress_energy_route_preserved": accepted,
        "divergence_identity_preserved": accepted,
        "divergence_identity_accepted": accepted,
        "vacuum_maxwell_route_preserved": accepted,
        "on_shell_vanishing_route_recorded": accepted,
        "on_shell_vanishing_route_accepted": accepted,
        "source_admissibility_review_retry_authorized": accepted,
        "local_on_shell_vacuum_source_route_accepted": False,
        "full_source_admissibility_review_accepted": False,
        "source_admissibility_review_completed": False,
        "source_admissibility_executed": False,
        "source_admissibility_proved": False,
        "source_admissibility_claimed": False,
        "A_source_admissibility_proved": False,
        "stress_energy_as_gravity_source_authorized": False,
        "total_matter_gauge_stress_energy_conservation_proved": False,
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
            REVIEW_RESULT,
            (
                "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_RESULT_REVIEW_"
                "REJECTS_IDENTITY_PENDING_REMEDIATION"
            ),
            (
                "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_RESULT_REVIEW_"
                "ACCEPTS_IDENTITY_AND_WRONGLY_PROMOTES_SOURCE_ROUTE"
            ),
        ],
        "critical_gate_fail_conditions": [
            "accept full source admissibility in this review",
            "authorize stress-energy as gravity source before the retry packet",
            "derive J^nu",
            "derive a psi-current route",
            "select an external current as native derivation",
            "derive sourced Maxwell theory",
            "prove a current conservation theorem",
            "construct A-relevant C_k rules",
            "claim EM closure",
            "claim QFT-GR closure",
            "authorize semiclassical coupling",
            "promote the working-form master action",
        ],
        "downstream_progression": [
            {
                "stage": "A_vacuum_source_admissibility_identity_result_review",
                "status": "ACCEPTS_ON_SHELL_DIVERGENCE_IDENTITY",
                "decision": REVIEW_RESULT,
                "reason": (
                    "The review accepts the constructed vacuum U(1) divergence "
                    "identity and its on-shell vanishing route."
                ),
            },
            {
                "stage": "A_source_admissibility_review_retry_after_vacuum_identity",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": RETRY_REASON,
            },
        ],
        "mathematical_statement": (
            "The review accepts the bounded vacuum U(1) identity "
            + DIVERGENCE_IDENTITY
            + " together with "
            + VACUUM_EULER_LAGRANGE_ROUTE
            + ", yielding "
            + ON_SHELL_VACUUM_CONSERVATION_IDENTITY
            + " as an on-shell conservation identity. The retry packet must "
            "still decide whether this is enough for bounded local source "
            "admissibility."
        ),
        "non_claim_boundary": (
            "This result review accepts only the on-shell vacuum U(1) "
            "stress-energy divergence identity. It does not accept the full "
            "source-admissibility review, does not authorize the gauge "
            "stress-energy as a gravity source, does not derive J^nu, does not "
            "construct a psi-current route, does not select an external "
            "current as native derivation, does not prove a current "
            "conservation theorem, does not construct A-relevant C_k rules, "
            "does not claim sourced Maxwell closure, does not close EM, does "
            "not close QFT-GR, does not authorize semiclassical coupling, does "
            "not claim empirical validation, and does not promote the master "
            "action."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeAVacuumSourceAdmissibilityIdentityResultReview",
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


def write_toe_native_a_vacuum_source_admissibility_identity_result_review(
    *,
    identity_packet_path: Path = A_SOURCE_IDENTITY_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_a_vacuum_source_admissibility_identity_result_review(
        identity_packet_path=identity_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A vacuum source-admissibility identity result review."
        )
    )
    parser.add_argument(
        "--identity-packet",
        type=Path,
        default=A_SOURCE_IDENTITY_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_a_vacuum_source_admissibility_identity_result_review(
        identity_packet_path=args.identity_packet,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
