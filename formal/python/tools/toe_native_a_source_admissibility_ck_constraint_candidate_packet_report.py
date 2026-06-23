from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_route_selection_after_vacuum_source_admissibility_report import (
    A_FIELD_DOMAIN_POLICY,
    A_SOURCE_CK_RULE_CANDIDATE,
    A_SOURCE_CK_RULE_CLASSIFICATION,
    A_SOURCE_CK_RULE_INTERPRETATION,
    BIANCHI_IDENTITY_ROUTE,
    BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
    CONSUMED_TARGET as SELECTOR_CONSUMED_TARGET,
    CURRENT_COUPLED_SCOPE_BOUNDARY,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as A_ROUTE_SELECTION_PATH,
    DIVERGENCE_IDENTITY,
    F_DEFINITION_POLICY,
    FULL_SOURCE_ADMISSIBILITY_BOUNDARY,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LOCAL_SOURCE_ROUTE_SCOPE,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    ON_SHELL_VACUUM_CONSERVATION_ROUTE,
    OUTCOME_ID as A_ROUTE_SELECTION_OUTCOME,
    PACKET_ID as A_ROUTE_SELECTION_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as A_ROUTE_SELECTION_SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTION_RESULT as A_ROUTE_SELECTION_RESULT,
    SOURCE_ADMISSIBILITY_CONDITION,
    SOURCE_ROUTE_STILL_BLOCKED,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-22T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_20260622_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_v0"
PACKET_RESULT = (
    "A_SOURCE_ADMISSIBILITY_RULE_RECORDED_AS_VACUUM_CONSERVATION_RESIDUAL_"
    "NO_ACTION_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = (
    "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_PREPARED_"
    + PACKET_RESULT
)
PACKET_CLASSIFICATION = (
    "toe_native_A_source_admissibility_ck_constraint_candidate_packet_records_"
    "vacuum_conservation_residual_no_action_variation_or_promotion"
)

NEXT_TARGET = "review_toe_native_A_source_admissibility_ck_constraint_candidate_packet_result"
NEXT_TARGET_KIND = "toe_native_A_source_admissibility_ck_constraint_candidate_packet_result_review"

CANDIDATE_CONSTRAINT_ID = "A_source_vacuum_conservation_residual_ck_candidate"
CANDIDATE_CONSTRAINT_FORM = A_SOURCE_CK_RULE_CANDIDATE.split("; ")[0]
CANDIDATE_CONSTRAINT_EQUATION = A_SOURCE_CK_RULE_CANDIDATE.split("; ")[1]
CANDIDATE_CONSTRAINT_SHORT_FORM = (
    "C_source^A := nabla_mu T_A^{mu nu}; C_source^A = 0"
)
CANDIDATE_CONSTRAINT_INTERPRETATION = A_SOURCE_CK_RULE_INTERPRETATION
CANDIDATE_CONSTRAINT_CLASSIFICATION = A_SOURCE_CK_RULE_CLASSIFICATION
VACUUM_SUPPORTING_IDENTITY_ID = "A_vacuum_source_admissibility_supporting_identity"
VACUUM_SUPPORTING_IDENTITY_FORM = DIVERGENCE_IDENTITY
VACUUM_ON_SHELL_IMPLICATION_FORM = ON_SHELL_VACUUM_CONSERVATION_ROUTE
RULE_SCOPE = (
    "vacuum U(1) admissibility-only source-rule candidate; not an action term; "
    "not a dynamical law; not sourced Maxwell theory; not EM closure"
)
CANDIDATE_ACTION_INSERTION_FORM = (
    "S_CsourceA[candidate] = integral_M sqrt(-g) lambda_nu "
    "C_source^{A,nu} d^4x"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_20260622_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeASourceAdmissibilityCKConstraintCandidatePacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_shapes() -> list[dict[str, Any]]:
    return [
        {
            "candidate_id": CANDIDATE_CONSTRAINT_ID,
            "candidate_type": "vacuum_conservation_residual_constraint",
            "selection_status": "selected_as_first_A_source_candidate_shape",
            "constraint_form": CANDIDATE_CONSTRAINT_FORM,
            "constraint_equation": CANDIDATE_CONSTRAINT_EQUATION,
            "plain_meaning": (
                "The vacuum U(1) gauge source route is admissible only when "
                "the gauge stress-energy divergence residual vanishes."
            ),
            "requires_new_variation_now": False,
            "fully_concrete_ck_functional_defined": False,
            "physical_law_claimed": False,
        },
        {
            "candidate_id": VACUUM_SUPPORTING_IDENTITY_ID,
            "candidate_type": "vacuum_on_shell_supporting_identity",
            "selection_status": "recorded_as_supporting_route_identity",
            "residual_identity": VACUUM_SUPPORTING_IDENTITY_FORM,
            "on_shell_implication": VACUUM_ON_SHELL_IMPLICATION_FORM,
            "plain_meaning": (
                "The vacuum Maxwell equation makes the selected residual "
                "vanish on shell in the bounded vacuum route."
            ),
            "requires_new_variation_now": False,
            "fully_concrete_ck_functional_defined": False,
            "physical_law_claimed": False,
        },
    ]


def _review_rows(selector: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_expected_candidate_packet_target",
            "status": "accepted",
            "evidence": selector.get("selected_next_target"),
            "assessment": "The selector authorized this A source C_k candidate packet.",
        },
        {
            "row_id": "selected_A_source_ck_family_carried_forward",
            "status": "accepted",
            "evidence": selector.get("selected_A_ck_constraint_family"),
            "assessment": "The packet stays within the A source-admissibility family.",
        },
        {
            "row_id": "vacuum_u1_policy_preserved",
            "status": "accepted",
            "evidence": [
                GAUGE_GROUP_POLICY,
                A_FIELD_DOMAIN_POLICY,
                F_DEFINITION_POLICY,
                BIANCHI_IDENTITY_ROUTE,
            ],
            "assessment": "The selected smooth real U(1) A-field policy is preserved.",
        },
        {
            "row_id": "bounded_vacuum_route_preserved",
            "status": "accepted",
            "evidence": [
                VACUUM_EULER_LAGRANGE_ROUTE,
                STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
                BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
            ],
            "assessment": "The bounded local on-shell vacuum source route is preserved.",
        },
        {
            "row_id": "candidate_residual_recorded",
            "status": "accepted",
            "evidence": [
                CANDIDATE_CONSTRAINT_FORM,
                CANDIDATE_CONSTRAINT_EQUATION,
            ],
            "assessment": "The direct A source-admissibility residual is recorded.",
        },
        {
            "row_id": "supporting_identity_recorded",
            "status": "accepted",
            "evidence": [
                VACUUM_SUPPORTING_IDENTITY_FORM,
                VACUUM_ON_SHELL_IMPLICATION_FORM,
            ],
            "assessment": "The accepted vacuum divergence identity remains the support.",
        },
        {
            "row_id": "candidate_classified_as_admissibility_only",
            "status": "accepted",
            "evidence": CANDIDATE_CONSTRAINT_CLASSIFICATION,
            "assessment": "The candidate is not an action term, dynamical law, sourced EM, or EM closure.",
        },
        {
            "row_id": "candidate_action_insertion_not_executed",
            "status": "accepted",
            "evidence": CANDIDATE_ACTION_INSERTION_FORM,
            "assessment": "A possible action insertion is not selected, defined, or varied here.",
        },
        {
            "row_id": "current_routes_blocked",
            "status": "accepted",
            "evidence": [
                "J_nu_derived=false",
                "psi_current_route_constructed=false",
                "external_current_native_derivation_selected=false",
                "sourced_maxwell_equation_derived=false",
                "matter_current_exchange_route_proved=false",
            ],
            "assessment": "No current or sourced electromagnetism route is introduced.",
        },
        {
            "row_id": "no_closure_promotion_or_empirical_claim",
            "status": "accepted",
            "evidence": [
                "full_em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
                "empirical_validation_claimed=false",
            ],
            "assessment": "The nonpromotion boundary is preserved.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_A_source_admissibility_ck_constraint_candidate_packet",
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


def build_toe_native_a_source_admissibility_ck_constraint_candidate_packet(
    *,
    a_route_selection_path: Path = A_ROUTE_SELECTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector = _read_json(a_route_selection_path)
    candidate_shapes = _candidate_shapes()
    review_rows = _review_rows(selector)
    acceptance_criteria = {
        "consumes_expected_target": (
            selector.get("schema_id") == A_ROUTE_SELECTION_SCHEMA_ID
            and selector.get("packet_id") == A_ROUTE_SELECTION_PACKET_ID
            and selector.get("outcome_id") == A_ROUTE_SELECTION_OUTCOME
            and selector.get("selection_result") == A_ROUTE_SELECTION_RESULT
            and selector.get("selected_next_target") == CONSUMED_TARGET
            and selector.get("accepted") is True
        ),
        "selector_consumed_vacuum_source_selector": (
            selector.get("consumed_target") == SELECTOR_CONSUMED_TARGET
        ),
        "selected_family_matches_A_source_admissibility": (
            selector.get("selected_A_ck_constraint_family")
            == SELECTED_A_CK_CONSTRAINT_FAMILY
            and SELECTED_A_CK_CONSTRAINT_FAMILY
            == "A_source_admissibility_constraint_family"
        ),
        "candidate_shape_matches_selector_guidance": (
            selector.get("source_rule_candidate") == A_SOURCE_CK_RULE_CANDIDATE
            and CANDIDATE_CONSTRAINT_FORM
            == "C_source^{A,nu}[g,A] := nabla_mu T_A^{mu nu}"
            and CANDIDATE_CONSTRAINT_EQUATION == "C_source^{A,nu}[g,A] = 0"
        ),
        "vacuum_route_preserved": (
            selector.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and selector.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and selector.get("divergence_identity") == DIVERGENCE_IDENTITY
            and selector.get("on_shell_vacuum_conservation_identity")
            == ON_SHELL_VACUUM_CONSERVATION_IDENTITY
        ),
        "candidate_shapes_counted": (
            len(candidate_shapes) == 2
            and sum(
                row["selection_status"]
                == "selected_as_first_A_source_candidate_shape"
                for row in candidate_shapes
            )
            == 1
        ),
        "no_ck_action_embedding_or_variation": True,
        "no_current_or_sourced_em_route": True,
        "review_rows_all_accepted": all(
            row["status"] == "accepted" for row in review_rows
        ),
        "next_review_target_selected": (
            NEXT_TARGET
            == "review_toe_native_A_source_admissibility_ck_constraint_candidate_packet_result"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "a_route_selection_outcome": A_ROUTE_SELECTION_OUTCOME,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "candidate_constraint_id": CANDIDATE_CONSTRAINT_ID,
        "candidate_constraint_type": "vacuum_conservation_residual_constraint",
        "candidate_constraint_form": CANDIDATE_CONSTRAINT_FORM,
        "candidate_constraint_equation": CANDIDATE_CONSTRAINT_EQUATION,
        "candidate_constraint_short_form": CANDIDATE_CONSTRAINT_SHORT_FORM,
        "candidate_constraint_interpretation": CANDIDATE_CONSTRAINT_INTERPRETATION,
        "candidate_constraint_classification": CANDIDATE_CONSTRAINT_CLASSIFICATION,
        "rule_scope": RULE_SCOPE,
        "vacuum_supporting_identity_id": VACUUM_SUPPORTING_IDENTITY_ID,
        "vacuum_supporting_identity_form": VACUUM_SUPPORTING_IDENTITY_FORM,
        "vacuum_on_shell_implication_form": VACUUM_ON_SHELL_IMPLICATION_FORM,
        "candidate_action_insertion_form": CANDIDATE_ACTION_INSERTION_FORM,
        "candidate_shapes": candidate_shapes,
        "candidate_shape_count": len(candidate_shapes),
        "candidate_shape_selected_count": sum(
            row["selection_status"] == "selected_as_first_A_source_candidate_shape"
            for row in candidate_shapes
        ),
        "candidate_shape_supporting_count": sum(
            row["selection_status"] == "recorded_as_supporting_route_identity"
            for row in candidate_shapes
        ),
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "bianchi_identity_route": BIANCHI_IDENTITY_ROUTE,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "stress_energy_under_selected_u1_policy": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "divergence_identity": DIVERGENCE_IDENTITY,
        "on_shell_vacuum_conservation_identity": ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
        "on_shell_vacuum_conservation_route": ON_SHELL_VACUUM_CONSERVATION_ROUTE,
        "bounded_source_admissibility_result": BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
        "local_source_route_scope": LOCAL_SOURCE_ROUTE_SCOPE,
        "full_source_admissibility_boundary": FULL_SOURCE_ADMISSIBILITY_BOUNDARY,
        "current_coupled_scope_boundary": CURRENT_COUPLED_SCOPE_BOUNDARY,
        "candidate_packet_prepared": accepted,
        "candidate_constraint_shape_recorded": accepted,
        "vacuum_conservation_residual_candidate_selected": accepted,
        "source_admissibility_rule_candidate_recorded": accepted,
        "on_shell_vacuum_supporting_identity_recorded": accepted,
        "candidate_constraint_is_admissibility_only": accepted,
        "candidate_constraint_is_condition_not_physical_law": accepted,
        "candidate_uses_accepted_vacuum_source_route": accepted,
        "candidate_uses_selected_u1_policy": accepted,
        "source_rule_candidate_promoted_to_action_term": False,
        "source_rule_candidate_promoted_to_dynamical_law": False,
        "source_rule_candidate_treated_as_sourced_em": False,
        "source_rule_candidate_treated_as_em_closure": False,
        "fully_concrete_ck_functional_defined": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "ck_functional_formula_fully_defined": False,
        "ck_functional_formula_selected": False,
        "candidate_not_inserted_into_master_action_variation": True,
        "candidate_action_insertion_executed": False,
        "ck_action_embedding_selected": False,
        "C_k_action_embedding_selected": False,
        "ck_action_embedding_constructed": False,
        "C_k_action_embedding_constructed": False,
        "ck_variation_executed": False,
        "C_k_variation_executed": False,
        "ck_variation_authorized": False,
        "C_k_variation_authorized": False,
        "lambda_variation_executed": False,
        "metric_variation_of_candidate_executed": False,
        "A_variation_of_candidate_executed": False,
        "ck_family_claimed_as_physical_law": False,
        "A_relevant_C_k_rule_candidate_recorded": accepted,
        "A_relevant_C_k_rules_constructed": False,
        "A_relevant_C_k_triads_constructed": False,
        "A_source_C_k_rule_constructed": False,
        "source_bridge_transport_ck_analogues_constructed": False,
        "new_conservation_proof_claimed": False,
        "new_source_admissibility_proof_claimed": False,
        "full_source_admissibility_review_accepted": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "source_admissibility_proved": False,
        "A_source_admissibility_claimed": False,
        "A_source_admissibility_proved": False,
        "stress_energy_source_admissibility_proved": False,
        "stress_energy_as_gravity_source_authorized": False,
        "current_route_derived": False,
        "current_source_route_constructed": False,
        "matter_current_J_nu_derived": False,
        "J_nu_derived": False,
        "psi_current_route_constructed": False,
        "psi_derived_current": False,
        "external_current_policy_selected": False,
        "external_current_native_derivation_selected": False,
        "current_conservation_proved": False,
        "matter_current_exchange_route_proved": False,
        "matter_gauge_energy_exchange_proved": False,
        "matter_gauge_energy_exchange_claimed": False,
        "maxwell_equation_derived": False,
        "maxwell_equations_derived": False,
        "sourced_maxwell_equation_derived": False,
        "sourced_maxwell_closure_claimed": False,
        "nonabelian_route_selected": False,
        "yang_mills_equations_derived": False,
        "field_equations_derived": False,
        "full_em_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_source_established": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "review_rows": review_rows,
        "review_row_count": len(review_rows),
        "review_row_accepted_count": sum(
            1 for row in review_rows if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "A_SOURCE_ADMISSIBILITY_CK_CANDIDATE_SHAPE_RECORDED_ONLY"
        ),
        "mathematical_statement": (
            "For the selected local classical vacuum U(1) route, the first A "
            "source-admissibility C_k candidate is recorded as the conservation "
            "residual "
            + CANDIDATE_CONSTRAINT_FORM
            + ", with candidate condition "
            + CANDIDATE_CONSTRAINT_EQUATION
            + ". The supporting identity is "
            + VACUUM_SUPPORTING_IDENTITY_FORM
            + " and the vacuum on-shell implication is "
            + VACUUM_ON_SHELL_IMPLICATION_FORM
            + ". This records a candidate condition only."
        ),
        "non_claim_boundary": (
            "This packet records only an A source-admissibility C_k candidate "
            "shape as a vacuum conservation residual. It does not select or "
            "define a fully concrete C_k functional, does not embed C_k in the "
            "action, does not execute C_k variation, does not vary lambda_k, "
            "A, or g, does not promote the residual to a dynamical law, does "
            "not derive J^nu, does not derive a psi-current or "
            "external-current native route, does not "
            "derive sourced Maxwell, does not prove matter-current or "
            "matter-gauge exchange, does not accept full source admissibility "
            "beyond the bounded vacuum route, does not construct an A-relevant "
            "C_k rule beyond recording this candidate, does not close EM, does "
            "not close QFT-GR, does not authorize semiclassical coupling, does "
            "not claim empirical validation, and does not promote the master "
            "action."
        ),
        "critical_gate_fail_conditions": [
            "embed C_k in the action",
            "execute C_k variation",
            "execute lambda variation",
            "vary the candidate with respect to A or g",
            "promote the residual to a dynamical law",
            "derive J^nu",
            "derive a psi-current route",
            "derive an external-current native route",
            "derive sourced Maxwell",
            "prove matter-current exchange",
            "claim full EM closure",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation or public readiness",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": "NOT_RUN",
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeASourceAdmissibilityCKConstraintCandidatePacket",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "a_route_selection_file": _ptr(a_route_selection_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A source-admissibility C_k constraint candidate packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_toe_native_a_source_admissibility_ck_constraint_candidate_packet(
        captured_at_utc=args.captured_at_utc
    )
    path = write_packet(packet, args.out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "candidate_constraint_id": packet["candidate_constraint_id"],
                "out": _ptr(path),
                "outcome_id": packet["outcome_id"],
                "selected_next_target": packet["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
