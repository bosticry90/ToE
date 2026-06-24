from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_ck_source_bridge_transport_rule_family_closeout_report import (
    CLOSEOUT_RESULT as A_CK_TRIAD_CLOSEOUT_RESULT,
    DEFAULT_OUT as A_CK_TRIAD_CLOSEOUT_PATH,
    FAMILY_CLASSIFICATION as A_CK_TRIAD_FAMILY_CLASSIFICATION,
    FAMILY_SCOPE as A_CK_TRIAD_SCOPE,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as A_CK_TRIAD_CLOSEOUT_OUTCOME,
    PACKET_ID as A_CK_TRIAD_CLOSEOUT_PACKET_ID,
    RECOMMENDED_INTERACTION_ROUTE,
    RECOMMENDED_NEXT_POLICY_PACKET,
    RULE_FAMILY_CLASSIFICATION as A_CK_TRIAD_RULE_FAMILY_CLASSIFICATION,
    SCHEMA_ID as A_CK_TRIAD_CLOSEOUT_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM as A_SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_RULE_DISPLAY_FORM as A_SOURCE_RULE_DISPLAY_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM as A_TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_RULE_DISPLAY_FORM as A_TRANSPORT_RULE_DISPLAY_FORM,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM as A_BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = "MASTER_ACTION_INTERACTION_SELECTION_AFTER_A_CK_TRIAD_20260624_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "MASTER_ACTION_INTERACTION_SELECTION_AFTER_A_CK_TRIAD_v0"
SELECTION_RESULT = (
    "MASTER_ACTION_INTERACTION_SELECTION_AFTER_A_CK_TRIAD_SELECTS_PSI_A_U1_"
    "CURRENT_AND_EXCHANGE_ROUTE_NO_CURRENT_DERIVATION_OR_EM_QFT_CLOSURE"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "master_action_interaction_selection_after_a_ck_triad_selects_psi_a_u1_"
    "current_and_exchange_route_no_current_derivation_or_em_qft_closure"
)

NEXT_TARGET = "prepare_toe_native_psi_A_u1_current_and_exchange_route_policy_packet"
NEXT_TARGET_KIND = "toe_native_psi_A_u1_current_and_exchange_route_policy_packet_preparation"

SELECTED_INTERACTION_ROUTE = "psi_A_u1_current_and_exchange_route"
SELECTED_ROUTE_LABEL = "psi-A U(1) current and exchange route"
SELECTED_ROUTE_STATUS = "selected_for_policy_packet_preparation"
SELECTED_ROUTE_EXECUTION_STATUS = "not_executed"
SELECTED_INTERACTION_FIELDS = ["psi", "A"]
SELECTED_MATTER_TYPE_SCOPE = "Dirac spinor or finite spinor multiplet"
SELECTED_GAUGE_GROUP = "U(1)"

COVARIANT_DERIVATIVE_POLICY_PREVIEW = "D_mu psi = (nabla_mu + i q A_mu) psi"
MATTER_EQUATION_SHAPE_PREVIEW = "(i gamma^mu D_mu - m) psi = 0"
CURRENT_CANDIDATE_PREVIEW = "J^mu = q psibar gamma^mu psi"
SOURCED_GAUGE_EQUATION_PREVIEW = "nabla_mu F^{mu nu} = J^nu"
GAUGE_EXCHANGE_PREVIEW = "nabla_mu T_A^{mu nu} = - F^nu_alpha J^alpha"
MATTER_EXCHANGE_PREVIEW = "nabla_mu T_psi^{mu nu} = + F^nu_alpha J^alpha"
TOTAL_EXCHANGE_PREVIEW = "nabla_mu (T_A^{mu nu} + T_psi^{mu nu}) = 0"
C_EXCHANGE_CANDIDATE_PREVIEW = (
    "C_exchange^{Apsi,nu} := nabla_mu(T_A^{mu nu} + T_psi^{mu nu})"
)
C_EXCHANGE_CANDIDATE_EQUATION_PREVIEW = "C_exchange^{Apsi,nu} = 0"
X_A_EXCHANGE_PREVIEW = "X_A^nu := nabla_mu T_A^{mu nu} + F^nu_alpha J^alpha"
X_PSI_EXCHANGE_PREVIEW = (
    "X_psi^nu := nabla_mu T_psi^{mu nu} - F^nu_alpha J^alpha"
)

POLICY_PACKET_REQUIRED_PINS = [
    "matter type: Dirac spinor or finite spinor multiplet",
    "gauge group: U(1)",
    "charge convention: q and sign convention",
    "covariant derivative: exact D_mu definition",
    "spin geometry: gamma matrices, tetrad, and spin connection policy",
    "adjoint: definition of psibar",
    "field domains: regularity and boundary conditions for psi and A",
    "gauge transformations: psi and A_mu transformation signs",
    "current policy: J^mu candidate and whether it is derived by A variation",
    "stress-energy policy: T_psi, T_A, and total T",
    "exchange policy: separate-sector versus total conservation",
    "background: flat or curved spacetime scope",
]

BLOCKED_CLAIMS = [
    "J^nu derived",
    "current conservation proved",
    "sourced Maxwell derived",
    "Dirac equation derived",
    "matter-gauge exchange proved",
    "EM-QFT closure",
    "QFT-GR closure",
    "quantized electromagnetism",
    "anomaly cancellation",
    "Standard Model derivation",
    "Phase 2 authorization",
    "empirical validation",
    "master-action promotion",
]

INTERACTION_ROUTE_CANDIDATES = [
    SELECTED_INTERACTION_ROUTE,
    "another_isolated_field_ck_triad",
    "external_current_A_route",
    "nonabelian_or_full_em_qft_route",
    "further_vacuum_ck_rule_elaboration",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MASTER_ACTION_INTERACTION_SELECTION_AFTER_A_CK_TRIAD_20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionInteractionSelectionAfterACKTriad.lean"
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


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _interaction_options() -> list[dict[str, Any]]:
    return [
        {
            "route_option_id": SELECTED_INTERACTION_ROUTE,
            "route_label": SELECTED_ROUTE_LABEL,
            "candidate_target": NEXT_TARGET,
            "status": SELECTED_ROUTE_STATUS,
            "execution_status": SELECTED_ROUTE_EXECUTION_STATUS,
            "fields": SELECTED_INTERACTION_FIELDS,
            "gauge_group": SELECTED_GAUGE_GROUP,
            "selection_reason": (
                "After the phi and vacuum A C_k triads, psi-A U(1) is the "
                "first natural interaction route because it tests whether the "
                "rule system can organize a matter-generated current and "
                "balanced matter-gauge exchange instead of another isolated "
                "field."
            ),
            "policy_packet_preparation_authorized": True,
            "current_derivation_claimed": False,
            "sourced_maxwell_derived": False,
            "exchange_proved": False,
            "em_qft_closure_claimed": False,
        },
        {
            "route_option_id": "another_isolated_field_ck_triad",
            "status": "deferred_not_rejected",
            "execution_status": "not_executed",
            "selection_reason": (
                "Deferred because the branch boundary now requires an "
                "interaction test, not another isolated source-bridge-"
                "transport triad."
            ),
        },
        {
            "route_option_id": "external_current_A_route",
            "status": "deferred_not_selected",
            "execution_status": "not_executed",
            "selection_reason": (
                "Deferred because inserting an unexplained external J^nu would "
                "not test whether the current comes from the matter field psi."
            ),
        },
        {
            "route_option_id": "nonabelian_or_full_em_qft_route",
            "status": "deferred_not_rejected",
            "execution_status": "not_executed",
            "selection_reason": (
                "Deferred because full non-Abelian, quantized, anomaly-aware "
                "closure is too broad before the classical or semiclassical "
                "U(1) psi-A policy surface is pinned."
            ),
        },
        {
            "route_option_id": "further_vacuum_ck_rule_elaboration",
            "status": "deferred_not_rejected",
            "execution_status": "not_executed",
            "selection_reason": (
                "Deferred to avoid extending vacuum-only rule vocabulary "
                "before testing lawful exchange between sectors."
            ),
        },
    ]


def _selection_criteria(closeout: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_consumes_post_a_ck_triad_interaction_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The selector consumes the active post-A/C_k-triad interaction target.",
        },
        {
            "row_id": "a_ck_triad_closed_as_vacuum_template",
            "status": "accepted",
            "evidence": closeout.get("closeout_result"),
            "assessment": (
                "The A/C_k source-bridge-transport triad is closed only as a "
                "vacuum U(1) admissibility template."
            ),
        },
        {
            "row_id": "phi_and_a_triad_reuse_recorded_as_architecture",
            "status": "accepted",
            "evidence": [
                "phi triad closed",
                "A triad closed",
                "source-bridge-transport pattern reusable across isolated scalar and vacuum gauge fields",
            ],
            "assessment": (
                "Reuse of the triad pattern is treated as an architectural "
                "result, not as a new law of nature."
            ),
        },
        {
            "row_id": "psi_a_u1_route_selected_as_first_interaction_test",
            "status": "accepted",
            "evidence": SELECTED_INTERACTION_ROUTE,
            "assessment": (
                "psi-A U(1) is selected because it tests a matter-generated "
                "current and lawful exchange between interacting sectors."
            ),
        },
        {
            "row_id": "external_current_route_deferred",
            "status": "accepted",
            "evidence": "external_current_A_route",
            "assessment": "An unexplained external current is not selected as the native route.",
        },
        {
            "row_id": "policy_packet_only_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next target is a policy packet to pin conventions before "
                "any derivation claim."
            ),
        },
        {
            "row_id": "current_and_exchange_shapes_recorded_as_policy_inputs",
            "status": "accepted",
            "evidence": [
                COVARIANT_DERIVATIVE_POLICY_PREVIEW,
                CURRENT_CANDIDATE_PREVIEW,
                TOTAL_EXCHANGE_PREVIEW,
            ],
            "assessment": (
                "Route shapes are recorded as convention-sensitive policy "
                "inputs, not as derived equations."
            ),
        },
        {
            "row_id": "c_exchange_candidate_recorded_without_definition_or_proof",
            "status": "accepted",
            "evidence": C_EXCHANGE_CANDIDATE_PREVIEW,
            "assessment": (
                "C_exchange is recorded as a likely future rule family to pin, "
                "not as a constructed C_k functional."
            ),
        },
        {
            "row_id": "required_policy_pins_enumerated",
            "status": "accepted",
            "evidence": POLICY_PACKET_REQUIRED_PINS,
            "assessment": "The first psi-A packet must define policy before derivation.",
        },
        {
            "row_id": "no_current_derivation_exchange_proof_closure_or_promotion",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": (
                "The selector blocks derivation, exchange proof, closure, "
                "quantization, anomaly, empirical, Phase 2, and promotion claims."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "master_action_interaction_selection_after_a_ck_triad",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "aggregate_lean_validation_status_allowed_values": ["NOT_RUN"],
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_master_action_interaction_selection_after_a_ck_triad(
    *,
    a_ck_triad_closeout_path: Path = A_CK_TRIAD_CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = _read_json(a_ck_triad_closeout_path)
    interaction_options = _interaction_options()
    selection_criteria = _selection_criteria(closeout)
    acceptance_criteria = {
        "consumes_expected_selector_target": (
            closeout.get("schema_id") == A_CK_TRIAD_CLOSEOUT_SCHEMA_ID
            and closeout.get("packet_id") == A_CK_TRIAD_CLOSEOUT_PACKET_ID
            and closeout.get("outcome_id") == A_CK_TRIAD_CLOSEOUT_OUTCOME
            and closeout.get("closeout_result") == A_CK_TRIAD_CLOSEOUT_RESULT
            and closeout.get("selected_next_target") == CONSUMED_TARGET
            and closeout.get("accepted") is True
        ),
        "a_ck_triad_closed_as_vacuum_template": (
            closeout.get("A_ck_triad_closed") is True
            and closeout.get("source_bridge_transport_family_closed") is True
            and closeout.get("family_classification") == A_CK_TRIAD_FAMILY_CLASSIFICATION
            and closeout.get("family_scope") == A_CK_TRIAD_SCOPE
            and closeout.get("rule_family_classification")
            == A_CK_TRIAD_RULE_FAMILY_CLASSIFICATION
            and closeout.get("source_rule_display_form") == A_SOURCE_RULE_DISPLAY_FORM
            and closeout.get("bridge_admissibility_constraint_form")
            == A_BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
            and A_TRANSPORT_RULE_DISPLAY_FORM
            in closeout.get("rule_family_display_forms", [])
            and closeout.get("source_admissibility_constraint_form")
            == A_SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and closeout.get("transport_admissibility_constraint_form")
            == A_TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "recommended_route_promoted_to_selected_route": (
            closeout.get("recommended_interaction_route") == RECOMMENDED_INTERACTION_ROUTE
            and closeout.get("recommended_next_policy_packet")
            == RECOMMENDED_NEXT_POLICY_PACKET
            and SELECTED_INTERACTION_ROUTE == RECOMMENDED_INTERACTION_ROUTE
            and NEXT_TARGET == RECOMMENDED_NEXT_POLICY_PACKET
        ),
        "interaction_options_exactly_one_selected": (
            sum(
                1
                for row in interaction_options
                if row["status"] == SELECTED_ROUTE_STATUS
            )
            == 1
        ),
        "policy_pins_enumerated": len(POLICY_PACKET_REQUIRED_PINS) == 12,
        "blocked_claims_enumerated": len(BLOCKED_CLAIMS) == 13,
        "selection_criteria_all_accepted": all(
            row["status"] == "accepted" for row in selection_criteria
        ),
        "selector_only_no_route_execution": True,
        "no_current_derivation_or_sourced_maxwell": True,
        "no_exchange_proof_or_em_qft_closure": True,
        "no_master_action_promotion": True,
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_MASTER_ACTION_INTERACTION_SELECTION_AFTER_A_CK_TRIAD"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_MASTER_ACTION_INTERACTION_SELECTION_AFTER_A_CK_TRIAD",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "MASTER_ACTION_INTERACTION_SELECTION_AFTER_A_CK_TRIAD_REQUIRES_REMEDIATION",
        "selection_result": SELECTION_RESULT,
        "route_selection_result": SELECTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "a_ck_triad_closeout_outcome": A_CK_TRIAD_CLOSEOUT_OUTCOME,
        "a_ck_triad_closeout_result": A_CK_TRIAD_CLOSEOUT_RESULT,
        "a_ck_triad_family_classification": A_CK_TRIAD_FAMILY_CLASSIFICATION,
        "a_ck_triad_scope": A_CK_TRIAD_SCOPE,
        "a_ck_triad_rule_family_classification": A_CK_TRIAD_RULE_FAMILY_CLASSIFICATION,
        "a_ck_triad_rule_forms": [
            A_SOURCE_RULE_DISPLAY_FORM,
            A_BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            A_TRANSPORT_RULE_DISPLAY_FORM,
        ],
        "a_ck_triad_reopened": False,
        "phi_ck_triad_reopened": False,
        "source_bridge_transport_pattern_reuse_result": (
            "architectural_reuse_witness_for_isolated_phi_and_vacuum_A"
        ),
        "architectural_result_not_new_law_of_nature": True,
        "interaction_route_candidates": INTERACTION_ROUTE_CANDIDATES,
        "interaction_options": interaction_options,
        "interaction_option_count": len(interaction_options),
        "interaction_options_selected_count": sum(
            1 for row in interaction_options if row["status"] == SELECTED_ROUTE_STATUS
        ),
        "interaction_options_deferred_count": sum(
            1
            for row in interaction_options
            if row["status"] in {"deferred_not_rejected", "deferred_not_selected"}
        ),
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "selected_route_label": SELECTED_ROUTE_LABEL,
        "selected_route_status": SELECTED_ROUTE_STATUS,
        "selected_route_execution_status": SELECTED_ROUTE_EXECUTION_STATUS,
        "selected_route_target": selected_next_target,
        "selected_route_packet_authorized": accepted,
        "selected_route_execution_authorized": False,
        "selected_interaction_fields": SELECTED_INTERACTION_FIELDS,
        "selected_matter_type_scope": SELECTED_MATTER_TYPE_SCOPE,
        "selected_gauge_group": SELECTED_GAUGE_GROUP,
        "policy_packet_target": selected_next_target,
        "policy_packet_kind": NEXT_TARGET_KIND,
        "policy_packet_preparation_authorized": accepted,
        "psi_A_u1_current_and_exchange_route_selected": accepted,
        "psi_A_u1_policy_packet_preparation_selected": accepted,
        "psi_A_u1_policy_packet_prepared": False,
        "covariant_derivative_policy_preview": COVARIANT_DERIVATIVE_POLICY_PREVIEW,
        "matter_equation_shape_preview": MATTER_EQUATION_SHAPE_PREVIEW,
        "current_candidate_preview": CURRENT_CANDIDATE_PREVIEW,
        "sourced_gauge_equation_preview": SOURCED_GAUGE_EQUATION_PREVIEW,
        "gauge_exchange_preview": GAUGE_EXCHANGE_PREVIEW,
        "matter_exchange_preview": MATTER_EXCHANGE_PREVIEW,
        "total_exchange_preview": TOTAL_EXCHANGE_PREVIEW,
        "c_exchange_candidate_preview": C_EXCHANGE_CANDIDATE_PREVIEW,
        "c_exchange_candidate_equation_preview": C_EXCHANGE_CANDIDATE_EQUATION_PREVIEW,
        "x_a_exchange_preview": X_A_EXCHANGE_PREVIEW,
        "x_psi_exchange_preview": X_PSI_EXCHANGE_PREVIEW,
        "c_exchange_rule_family_introduced_as_likely_policy_target": True,
        "c_exchange_functional_defined": False,
        "c_exchange_rule_proved": False,
        "separate_sector_exchange_visible": True,
        "total_conservation_policy_required": True,
        "illegal_loss_vs_legal_transfer_distinction_required": True,
        "policy_packet_required_pins": POLICY_PACKET_REQUIRED_PINS,
        "policy_packet_required_pin_count": len(POLICY_PACKET_REQUIRED_PINS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "selection_criteria": selection_criteria,
        "selection_criteria_count": len(selection_criteria),
        "selection_criteria_accepted_count": sum(
            1 for row in selection_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "selector_target_prepared": accepted,
        "selector_target_accepted": accepted,
        "selection_executed": accepted,
        "master_action_interaction_selection_executed": accepted,
        "another_isolated_field_triad_selected": False,
        "external_current_route_selected": False,
        "nonabelian_or_full_em_qft_route_selected": False,
        "further_vacuum_ck_rule_elaboration_selected": False,
        "current_route_derived": False,
        "current_source_route_constructed": False,
        "matter_current_J_nu_derived": False,
        "J_nu_derived": False,
        "psi_current_route_constructed": False,
        "current_conservation_proved": False,
        "sourced_maxwell_equation_derived": False,
        "sourced_maxwell_route_derived": False,
        "dirac_equation_derived": False,
        "matter_current_exchange_route_proved": False,
        "matter_gauge_energy_exchange_proved": False,
        "matter_gauge_exchange_proved": False,
        "em_qft_closure_claimed": False,
        "full_em_closure_claimed": False,
        "em_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "quantized_electromagnetism_claimed": False,
        "anomaly_cancellation_claimed": False,
        "standard_model_derivation_claimed": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "toe_native_matter_derivation_claimed": False,
        "native_generation_theorem_claimed": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "phase2_readiness_claim": False,
        "phase2_authorized": False,
        "canonical_master_action_promoted": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "critical_gate_fail_conditions": [
            "select another isolated-field triad as the next target",
            "select an external current route as native current derivation",
            "claim J^nu is derived",
            "prove current conservation",
            "derive sourced Maxwell",
            "derive the Dirac equation",
            "prove matter-gauge exchange",
            "define C_exchange as a completed functional",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "claim quantized electromagnetism",
            "claim anomaly cancellation",
            "claim Standard Model derivation",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "downstream_progression": [
            {
                "stage": "master_action_interaction_selection_after_A_ck_triad",
                "status": "SELECTED_PSI_A_U1_CURRENT_AND_EXCHANGE_ROUTE_FOR_POLICY_PACKET",
                "decision": SELECTION_RESULT,
                "reason": (
                    "The first post-triad interaction test should determine "
                    "whether psi can supply a U(1) current and whether A and "
                    "psi can exchange energy-momentum while preserving a total "
                    "rule."
                ),
            },
            {
                "stage": "toe_native_psi_A_u1_current_and_exchange_route_policy_packet",
                "status": "NEXT_TARGET_AUTHORIZED_FOR_PREPARATION_ONLY",
                "decision": selected_next_target,
                "reason": (
                    "The policy packet may pin conventions and domains; it may "
                    "not claim the current, equations, exchange, quantization, "
                    "closure, or promotion by selection alone."
                ),
            },
        ],
        "mathematical_statement": (
            "The selector chooses psi_A_u1_current_and_exchange_route as the "
            "first master-action interaction target after the closed A/C_k "
            "triad and authorizes only preparation of the psi-A U(1) current "
            "and exchange policy packet. The selector records conventional "
            "route shapes for D_mu psi, a candidate J^mu, sourced Maxwell, and "
            "sector exchange as policy inputs, not as derived or proved "
            "results."
        ),
        "non_claim_boundary": (
            "This selector records psi_A_u1_current_and_exchange_route as "
            "selected for policy-packet preparation only. It treats the phi "
            "and A source-bridge-transport triads as bounded isolated-field "
            "architecture and does not reopen either triad. It does not derive "
            "J^nu, does not prove current conservation, does not derive "
            "sourced Maxwell, does not derive the Dirac equation, does not "
            "prove matter-gauge exchange, does not define or prove a completed "
            "C_exchange functional, does not close EM-QFT, does not close "
            "QFT-GR, does not quantize electromagnetism, does not prove "
            "anomaly cancellation, does not derive the Standard Model, does "
            "not authorize Phase 2, does not claim empirical validation, and "
            "does not promote the master action. The full ToeFormal aggregate "
            "is recorded as NOT_RUN for this selector."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.MasterActionInteractionSelectionAfterACKTriad",
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
        "validation_policy": validation_policy,
        **validation_policy,
    }


def write_master_action_interaction_selection_after_a_ck_triad(
    *,
    a_ck_triad_closeout_path: Path = A_CK_TRIAD_CLOSEOUT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_master_action_interaction_selection_after_a_ck_triad(
        a_ck_triad_closeout_path=a_ck_triad_closeout_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the master-action interaction selector after A/C_k triad."
    )
    parser.add_argument(
        "--a-ck-triad-closeout",
        type=Path,
        default=A_CK_TRIAD_CLOSEOUT_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    a_ck_triad_closeout_path = (
        args.a_ck_triad_closeout
        if args.a_ck_triad_closeout.is_absolute()
        else REPO_ROOT / args.a_ck_triad_closeout
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = write_master_action_interaction_selection_after_a_ck_triad(
        a_ck_triad_closeout_path=a_ck_triad_closeout_path,
        out=out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "master_action_interaction_selection_after_a_ck_triad_report: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
