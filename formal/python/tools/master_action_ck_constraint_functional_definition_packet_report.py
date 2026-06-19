from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_phi_ck_variational_content_packet_report import (
    AGGREGATE_TIMEOUT_STATUS,
    DEFAULT_OUT as PHI_CK_PACKET_PATH,
    MASTER_ACTION_CK_SURFACE,
    NEXT_TARGET as PHI_CK_PACKET_NEXT_TARGET,
    OUTCOME_ID as PHI_CK_PACKET_OUTCOME,
    PACKET_ID as PHI_CK_PACKET_ID,
    SCHEMA_ID as PHI_CK_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_v0"
PACKET_RESULT = "CK_CONSTRAINT_FUNCTIONAL_OPTIONS_INDEXED_NO_SELECTION"
OUTCOME_ID = (
    "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_PREPARED_"
    "CK_CONSTRAINT_FUNCTIONAL_OPTIONS_INDEXED_NO_SELECTION"
)
PACKET_CLASSIFICATION = (
    "master_action_ck_constraint_functional_definition_packet_indexes_legal_"
    "constraint_options_no_selection"
)
CONSUMED_TARGET = "prepare_master_action_ck_constraint_functional_definition_packet"
NEXT_TARGET = "review_master_action_ck_constraint_functional_definition_packet_result"
NEXT_TARGET_KIND = "master_action_ck_constraint_functional_definition_packet_result_review"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

CONSTRAINT_ACTION_FORM = (
    "S_C = integral_M d^4x sqrt(-g) sum_k lambda_k "
    "C_k(g, psi, A, phi, rho)"
)
LAMBDA_VARIATION_FORM = (
    "delta S_C/delta lambda_k = C_k(g, psi, A, phi, rho) = 0"
)
PHI_VARIATION_FORM = "delta S_C/delta phi_i = sum_k lambda_k delta C_k/delta phi_i"
METRIC_VARIATION_FORM = (
    "delta S_C/delta g^{mu nu} contributes a constraint stress-energy or "
    "gravity-side stationarity term only when C_k has metric dependence and "
    "a defined variational derivative"
)
MINIMUM_REQUIRED_FIELDS = [
    "constraint_id",
    "mathematical_form",
    "depends_on",
    "codomain",
    "local_or_nonlocal_status",
    "covariance_rule",
    "regularity_domain_assumptions",
    "variation_with_respect_to_phi",
    "variation_with_respect_to_g",
    "equation_role",
    "provenance",
]
OPTION_CLASS_COUNT = 7
PHI_RELEVANT_RECOMMENDED_CLASSES = [
    "source_admissibility_constraint",
    "bridge_admissibility_constraint",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionCKConstraintFunctionalDefinitionPacket.lean"
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
MASTER_ACTION_DOC_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_CANDIDATE_MASTER_ACTION_v0.md"
)
SEAM_REGISTRY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
CLASS_B_INVENTORY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
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


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required text file: {path}")
    return path.read_text(encoding="utf-8")


def _constraint_options() -> list[dict[str, Any]]:
    return [
        {
            "constraint_id": "bridge_admissibility_constraint",
            "class_token": "TOE_CK_CLASS_BRIDGE_ADMISSIBILITY_v0",
            "mathematical_form": (
                "C_bridge_s = B_s[g, psi, A, phi, rho] - B_s^admissible = 0"
            ),
            "depends_on": ["g", "psi", "A", "phi", "rho"],
            "codomain": "scalar functional constraint or finite family of scalar residuals",
            "local_or_nonlocal_status": "may be local or nonlocal depending on bridge witness route; not selected here",
            "covariance_rule": "must be diffeomorphism-covariant or packaged as a covariant scalar density before insertion in S_C",
            "regularity_domain_assumptions": "requires the bridge witness domain, boundary policy, and field regularity to be declared before variation",
            "variation_with_respect_to_phi": "may contribute sum_k lambda_k delta C_k/delta phi_i if the bridge witness depends on phi",
            "variation_with_respect_to_g": "may contribute a metric-side constraint stress term when B_s has metric dependence",
            "equation_role": "can restrict admissibility and may modify equations only after a concrete bridge functional is selected",
            "provenance": "registry_indexed_policy_class_not_selected",
            "phi_relevance": "high",
            "selected_for_definition": False,
        },
        {
            "constraint_id": "conservation_constraint",
            "class_token": "TOE_CK_OPTION_CONSERVATION_v0",
            "mathematical_form": "C_cons = nabla_mu T^{mu nu}_candidate = 0",
            "depends_on": ["g", "psi", "A", "phi", "rho"],
            "codomain": "vector or distributional-vector constraint",
            "local_or_nonlocal_status": "local after a stress-energy candidate and domain are fixed; otherwise blocked",
            "covariance_rule": "must be tensorial and compatible with the selected connection and weak/strong conservation convention",
            "regularity_domain_assumptions": "requires differentiability or weak-pairing domain for T^{mu nu}_candidate",
            "variation_with_respect_to_phi": "not defined until the stress-energy candidate and conservation functional are selected",
            "variation_with_respect_to_g": "not defined until the conservation functional's metric dependence is specified",
            "equation_role": "would restrict admissibility before it can be treated as a dynamical equation modifier",
            "provenance": "candidate_option_from_qft_gr_conservation_obligation_not_selected",
            "phi_relevance": "medium",
            "selected_for_definition": False,
        },
        {
            "constraint_id": "regime_transport_constraint",
            "class_token": "TOE_CK_CLASS_TRANSPORT_CONSISTENCY_v0",
            "mathematical_form": "C_transport_r = T_r[operator_surface] - R_r[residual_surface] = 0",
            "depends_on": ["g", "psi", "A", "phi", "rho"],
            "codomain": "scalar, vector, tensor, or residual-family constraint",
            "local_or_nonlocal_status": "often nonlocal or theorem-route dependent; not selected here",
            "covariance_rule": "must preserve covariance under the source and target regime maps",
            "regularity_domain_assumptions": "requires transport theorem hypotheses and regime-limit domain",
            "variation_with_respect_to_phi": "blocked until the transport operator's phi dependence is declared",
            "variation_with_respect_to_g": "blocked until the regime transport map's metric dependence is declared",
            "equation_role": "primarily restricts allowed transport/regime routes; equation modification is not licensed",
            "provenance": "registry_indexed_policy_class_not_selected",
            "phi_relevance": "medium",
            "selected_for_definition": False,
        },
        {
            "constraint_id": "gauge_current_compatibility_constraint",
            "class_token": "TOE_CK_CLASS_COMPATIBILITY_v0",
            "mathematical_form": "C_gauge = D_mu J^mu[A, psi, phi] = 0 or interface-current residual = 0",
            "depends_on": ["g", "psi", "A", "phi"],
            "codomain": "scalar or Lie-algebra-valued compatibility constraint",
            "local_or_nonlocal_status": "local if current and gauge bundle are fixed; otherwise blocked",
            "covariance_rule": "must be gauge-covariant and diffeomorphism-covariant",
            "regularity_domain_assumptions": "requires current definition, gauge domain, and matter-field regularity",
            "variation_with_respect_to_phi": "only present if phi participates in the current or coupling map",
            "variation_with_respect_to_g": "depends on the current's metric and connection dependence",
            "equation_role": "interface admissibility only until a concrete gauge-current constraint is selected",
            "provenance": "registry_indexed_compatibility_option_not_selected",
            "phi_relevance": "low",
            "selected_for_definition": False,
        },
        {
            "constraint_id": "state_probability_statistical_constraint",
            "class_token": "TOE_CK_OPTION_STATE_PROBABILITY_STATISTICAL_v0",
            "mathematical_form": "C_stat = normalization_or_expectation_consistency[rho, psi, phi, g] = 0",
            "depends_on": ["g", "psi", "phi", "rho"],
            "codomain": "scalar functional or finite expectation constraint family",
            "local_or_nonlocal_status": "usually nonlocal because normalization and expectations integrate over state space",
            "covariance_rule": "must specify the measure and covariance of the state/probability pairing",
            "regularity_domain_assumptions": "requires rho domain, integrability, positivity, and expectation pairing rules",
            "variation_with_respect_to_phi": "blocked until phi-dependence of the state or expectation map is specified",
            "variation_with_respect_to_g": "blocked until the measure and metric dependence are specified",
            "equation_role": "admissibility or normalization restriction only; no dynamics selected",
            "provenance": "candidate_option_from_statistical_information_term_not_selected",
            "phi_relevance": "medium",
            "selected_for_definition": False,
        },
        {
            "constraint_id": "information_correlation_timing_constraint",
            "class_token": "TOE_CK_OPTION_INFORMATION_CORRELATION_TIMING_v0",
            "mathematical_form": "C_info = I_phi[g, psi, A, phi, rho] - I_allowed = 0",
            "depends_on": ["g", "psi", "A", "phi", "rho"],
            "codomain": "scalar functional or admissibility predicate encoded as a scalar residual",
            "local_or_nonlocal_status": "likely nonlocal or window-dependent; not selected here",
            "covariance_rule": "must encode timing windows and correlation consistency in covariant terms",
            "regularity_domain_assumptions": "requires timing-window, correlation, and admissible-state domains",
            "variation_with_respect_to_phi": "blocked until I_phi is mathematically defined",
            "variation_with_respect_to_g": "blocked until causal/timing metric dependence is mathematically defined",
            "equation_role": "could restrict operational admissibility; not licensed as a field-equation modifier",
            "provenance": "candidate_option_from_master_action_information_binding_not_selected",
            "phi_relevance": "medium",
            "selected_for_definition": False,
        },
        {
            "constraint_id": "source_admissibility_constraint",
            "class_token": "TOE_CK_OPTION_SOURCE_ADMISSIBILITY_v0",
            "mathematical_form": "C_source = admissibility[T_{mu nu}^{phi}, g, domain] = 0",
            "depends_on": ["g", "phi"],
            "codomain": "scalar, vector, tensor, or predicate-to-residual functional",
            "local_or_nonlocal_status": "depends on admissibility rule; may be local, weak/distributional, or global finite-action",
            "covariance_rule": "must be tensorial or invariant under diffeomorphisms and compatible with Bianchi obligations",
            "regularity_domain_assumptions": "requires source domain, conservation convention, and boundary/weak-pairing assumptions",
            "variation_with_respect_to_phi": "phi-relevant but blocked until admissibility residual is defined",
            "variation_with_respect_to_g": "metric-relevant but blocked until source-admissibility functional is defined",
            "equation_role": "strong phi-route candidate as an admissibility restriction; not selected as a modifier",
            "provenance": "candidate_option_from_qft_gr_scalar_witness_frontier_not_selected",
            "phi_relevance": "highest",
            "selected_for_definition": False,
        },
    ]


def _packet_criteria(
    *,
    previous_packet: dict[str, Any],
    master_action_doc: str,
    seam_registry: str,
    class_b_inventory: str,
    options: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "previous_ck_packet_consumed",
            "status": "accepted",
            "evidence": previous_packet.get("outcome_id"),
            "assessment": "The packet consumes the C_k variational-content blocker packet.",
        },
        {
            "row_id": "minimum_action_form_recorded",
            "status": "accepted",
            "evidence": CONSTRAINT_ACTION_FORM,
            "assessment": "The generic S_C multiplier action form is recorded.",
        },
        {
            "row_id": "lambda_phi_metric_variation_contract_recorded",
            "status": "accepted",
            "evidence": [
                LAMBDA_VARIATION_FORM,
                PHI_VARIATION_FORM,
                METRIC_VARIATION_FORM,
            ],
            "assessment": "The lambda, phi, and metric variation slots are recorded.",
        },
        {
            "row_id": "existing_registry_classes_reused",
            "status": "accepted",
            "evidence": [
                token
                for token in [
                    "TOE_CK_CLASS_COMPATIBILITY_v0",
                    "TOE_CK_CLASS_BRIDGE_ADMISSIBILITY_v0",
                    "TOE_CK_CLASS_TRANSPORT_CONSISTENCY_v0",
                    "TOE_CK_CLASS_REGIME_INTERFACE_BOUNDEDNESS_v0",
                ]
                if token in seam_registry
            ],
            "assessment": "Existing seam-registry class tokens are used as policy-level anchors.",
        },
        {
            "row_id": "candidate_option_menu_indexed",
            "status": "accepted",
            "evidence": [row["constraint_id"] for row in options],
            "assessment": "The requested seven candidate C_k option classes are indexed.",
        },
        {
            "row_id": "required_fields_populated",
            "status": "accepted",
            "evidence": MINIMUM_REQUIRED_FIELDS,
            "assessment": "Each candidate option carries the required functional metadata fields.",
        },
        {
            "row_id": "phi_relevant_candidates_identified_without_selection",
            "status": "accepted",
            "evidence": PHI_RELEVANT_RECOMMENDED_CLASSES,
            "assessment": "Source- and bridge-admissibility are identified as phi-relevant without selecting either.",
        },
        {
            "row_id": "concrete_functional_family_not_found",
            "status": "accepted",
            "evidence": (
                "Class-B inventory contains seam class tokens but no variational C_k functional formulas"
                if "SEAM-QFT-GR" in class_b_inventory
                else "class-b inventory not available"
            ),
            "assessment": "The repo supplies constraint classes, not concrete C_k variational functionals.",
        },
        {
            "row_id": "no_selection_or_promotion",
            "status": "accepted",
            "evidence": PACKET_RESULT,
            "assessment": "The packet indexes options but selects no C_k family and promotes no action.",
        },
        {
            "row_id": "next_target_review_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The packet result should be reviewed before any family-selection packet.",
        },
        {
            "row_id": "nonclaims_preserved",
            "status": "accepted",
            "evidence": [
                "ck_content_fully_defined=false",
                "phi_generated_by_ck=false",
                "source_conservation_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No derivation, closure, validation, or promotion claim is added.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "master_action_ck_constraint_functional_definition_packet",
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
        "aggregate_lean_validation_status_for_packet": AGGREGATE_TIMEOUT_STATUS,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_master_action_ck_constraint_functional_definition_packet(
    *,
    previous_packet_path: Path = PHI_CK_PACKET_PATH,
    master_action_doc_path: Path = MASTER_ACTION_DOC_PATH,
    seam_registry_path: Path = SEAM_REGISTRY_PATH,
    class_b_inventory_path: Path = CLASS_B_INVENTORY_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    previous_packet = _read_json(previous_packet_path)
    master_action_doc = _read_text(master_action_doc_path)
    seam_registry = _read_text(seam_registry_path)
    class_b_inventory = _read_text(class_b_inventory_path)
    options = _constraint_options()
    criteria = _packet_criteria(
        previous_packet=previous_packet,
        master_action_doc=master_action_doc,
        seam_registry=seam_registry,
        class_b_inventory=class_b_inventory,
        options=options,
    )
    option_ids = {row["constraint_id"] for row in options}
    acceptance_criteria = {
        "consumes_expected_live_target": (
            previous_packet.get("schema_id") == PHI_CK_PACKET_SCHEMA_ID
            and previous_packet.get("packet_id") == PHI_CK_PACKET_ID
            and previous_packet.get("outcome_id") == PHI_CK_PACKET_OUTCOME
            and previous_packet.get("selected_next_target") == CONSUMED_TARGET
            and previous_packet.get("accepted") is True
        ),
        "master_action_ck_surface_present": MASTER_ACTION_CK_SURFACE
        in master_action_doc,
        "seam_registry_policy_classes_present": all(
            token in seam_registry
            for token in [
                "TOE_CK_CLASS_COMPATIBILITY_v0",
                "TOE_CK_CLASS_BRIDGE_ADMISSIBILITY_v0",
                "TOE_CK_CLASS_TRANSPORT_CONSISTENCY_v0",
                "TOE_CK_CLASS_REGIME_INTERFACE_BOUNDEDNESS_v0",
            ]
        ),
        "seven_candidate_options_indexed": option_ids
        == {
            "bridge_admissibility_constraint",
            "conservation_constraint",
            "regime_transport_constraint",
            "gauge_current_compatibility_constraint",
            "state_probability_statistical_constraint",
            "information_correlation_timing_constraint",
            "source_admissibility_constraint",
        },
        "required_fields_populated_for_each_option": all(
            all(field in row and row[field] not in ("", [], None) for field in MINIMUM_REQUIRED_FIELDS)
            for row in options
        ),
        "no_candidate_selected": all(row["selected_for_definition"] is False for row in options),
        "phi_relevant_candidates_identified": all(
            option in option_ids for option in PHI_RELEVANT_RECOMMENDED_CLASSES
        ),
        "criteria_all_accepted": all(row["status"] == "accepted" for row in criteria),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "prior_ck_variational_content_outcome": PHI_CK_PACKET_OUTCOME,
        "prior_ck_variational_content_result": previous_packet.get("packet_result"),
        "master_action_ck_surface": MASTER_ACTION_CK_SURFACE,
        "constraint_action_form": CONSTRAINT_ACTION_FORM,
        "lambda_variation_form": LAMBDA_VARIATION_FORM,
        "phi_variation_form": PHI_VARIATION_FORM,
        "metric_variation_form": METRIC_VARIATION_FORM,
        "minimum_required_fields": MINIMUM_REQUIRED_FIELDS,
        "option_class_count": len(options),
        "constraint_functional_options": options,
        "indexed_constraint_ids": [row["constraint_id"] for row in options],
        "existing_registry_class_tokens": [
            "TOE_CK_CLASS_COMPATIBILITY_v0",
            "TOE_CK_CLASS_BRIDGE_ADMISSIBILITY_v0",
            "TOE_CK_CLASS_TRANSPORT_CONSISTENCY_v0",
            "TOE_CK_CLASS_REGIME_INTERFACE_BOUNDEDNESS_v0",
        ],
        "class_b_inventory_reused": True,
        "concrete_ck_functional_family_found": False,
        "concrete_ck_functional_families_found": [],
        "ck_constraint_functional_options_indexed": True,
        "ck_constraint_functional_family_defined": False,
        "ck_constraint_functional_family_selected": False,
        "ck_phi_relevant_constraint_class_selected": False,
        "ck_definition_blocked_by_lack_of_selection_criteria": False,
        "ck_content_fully_defined": False,
        "legal_constraint_type_menu_defined": True,
        "options_indexed_no_selection": True,
        "source_admissibility_candidate_indexed": True,
        "bridge_admissibility_candidate_indexed": True,
        "source_or_bridge_admissibility_recommended_for_future_selection": True,
        "phi_relevant_recommended_classes": PHI_RELEVANT_RECOMMENDED_CLASSES,
        "review_target_selected": True,
        "post_review_recommended_target": "prepare_ck_constraint_family_selection_for_phi_route",
        "packet_criteria": criteria,
        "packet_criteria_count": len(criteria),
        "packet_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": "CK_CONSTRAINT_OPTION_MENU_INDEXED_NO_FUNCTIONAL_SELECTION",
        "mathematical_statement": (
            "The packet records S_C = integral sqrt(-g) sum_k lambda_k "
            "C_k(g, psi, A, phi, rho), the multiplier constraint "
            "delta S_C/delta lambda_k = C_k = 0, and the formal phi and "
            "metric variation slots. It indexes seven legal C_k option "
            "classes but selects no concrete functional family, so no C_k "
            "content is fully defined."
        ),
        "non_claim_boundary": (
            "This packet defines a legal option menu for C_k constraint "
            "functionals only. It does not fully define C_k content, does "
            "not select a C_k family, does not prove phi is generated by "
            "C_k, does not derive V(phi), does not prove source "
            "admissibility or conservation, does not close QFT-GR, does "
            "not authorize semiclassical coupling, does not promote the "
            "working-form master action, does not claim empirical "
            "validation, and does not authorize public readiness or release "
            "completion."
        ),
        "critical_gate_fail_conditions": [
            "claim C_k content fully defined",
            "claim phi generated by C_k",
            "claim V(phi) derived",
            "claim source admissibility or conservation newly proved",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation",
        ],
        "ck_content_fully_defined_claimed": False,
        "phi_generated_by_ck_claimed": False,
        "derived_v_phi_claimed": False,
        "potential_derived": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "source_conservation_claimed": False,
        "weak_conservation_claimed": False,
        "bianchi_compatibility_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_source_established": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "toe_native_matter_derivation_claimed": False,
        "toe_native_matter_sector_derived": False,
        "toe_native_matter_sector_defined": False,
        "standard_model_derivation_claimed": False,
        "native_generation_theorem_claimed": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": AGGREGATE_TIMEOUT_STATUS,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.MasterActionCKConstraintFunctionalDefinitionPacket",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
        "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
        "release_current_authority_aggregate_file": _ptr(
            RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
        ),
        "master_action_doc_file": _ptr(MASTER_ACTION_DOC_PATH),
        "seam_registry_file": _ptr(SEAM_REGISTRY_PATH),
        "class_b_inventory_file": _ptr(CLASS_B_INVENTORY_PATH),
        "prior_packet_file": _ptr(previous_packet_path),
        "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
    }


def write_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build the master-action C_k constraint-functional definition packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_master_action_ck_constraint_functional_definition_packet(
        captured_at_utc=args.captured_at_utc
    )
    path = write_packet(packet, args.out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "out": _ptr(path),
                "outcome_id": packet["outcome_id"],
                "packet_result": packet["packet_result"],
                "selected_next_target": packet["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
