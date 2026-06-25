from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.master_action_interaction_selection_after_a_ck_triad_report import (
    C_EXCHANGE_CANDIDATE_EQUATION_PREVIEW as SELECTOR_C_EXCHANGE_EQUATION_PREVIEW,
    C_EXCHANGE_CANDIDATE_PREVIEW as SELECTOR_C_EXCHANGE_PREVIEW,
    COVARIANT_DERIVATIVE_POLICY_PREVIEW as SELECTOR_COVARIANT_DERIVATIVE_PREVIEW,
    CURRENT_CANDIDATE_PREVIEW as SELECTOR_CURRENT_CANDIDATE_PREVIEW,
    DEFAULT_OUT as SELECTOR_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_EXCHANGE_PREVIEW as SELECTOR_GAUGE_EXCHANGE_PREVIEW,
    LEAN_VALIDATION_POLICY_ID,
    MATTER_EQUATION_SHAPE_PREVIEW as SELECTOR_MATTER_EQUATION_SHAPE_PREVIEW,
    MATTER_EXCHANGE_PREVIEW as SELECTOR_MATTER_EXCHANGE_PREVIEW,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as SELECTOR_OUTCOME,
    PACKET_ID as SELECTOR_PACKET_ID,
    SCHEMA_ID as SELECTOR_SCHEMA_ID,
    SELECTED_GAUGE_GROUP,
    SELECTED_INTERACTION_FIELDS,
    SELECTED_INTERACTION_ROUTE,
    SELECTED_MATTER_TYPE_SCOPE,
    SOURCED_GAUGE_EQUATION_PREVIEW as SELECTOR_SOURCED_GAUGE_EQUATION_PREVIEW,
    TOTAL_EXCHANGE_PREVIEW as SELECTOR_TOTAL_EXCHANGE_PREVIEW,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-24T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_ROUTE_POLICY_PACKET_20260624_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_ROUTE_POLICY_PACKET_v0"
POLICY_PACKET_RESULT = (
    "TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_ROUTE_POLICY_PACKET_PREPARED_"
    "INTERACTION_POLICY_SELECTED_CURRENT_AND_EXCHANGE_DERIVATION_STILL_BLOCKED"
)
OUTCOME_ID = POLICY_PACKET_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_psi_A_u1_current_and_exchange_route_policy_packet_selects_"
    "interaction_policy_and_blocks_current_exchange_derivation"
)

NEXT_TARGET = "prepare_toe_native_psi_A_u1_current_and_exchange_derivation_obligation_packet"
NEXT_TARGET_KIND = (
    "toe_native_psi_A_u1_current_and_exchange_derivation_obligation_packet_preparation"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_ROUTE_POLICY_PACKET_20260624_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePsiAU1CurrentAndExchangeRoutePolicyPacket.lean"
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

MATTER_SURFACE_POLICY = "psi as Dirac-like spinor or finite spinor multiplet"
GAUGE_GROUP_POLICY = "U(1)"
GAUGE_FIELD_POLICY = "A_mu as smooth real U(1) gauge potential one-form"
FIELD_STRENGTH_POLICY = (
    "F = dA; F_{mu nu} = partial_mu A_nu - partial_nu A_mu"
)
CHARGE_POLICY = "real charge q with plus-sign covariant derivative convention"
COVARIANT_DERIVATIVE_POLICY = "D_mu psi = (nabla_mu + i q A_mu) psi"
ALTERNATE_COVARIANT_DERIVATIVE_REJECTED = (
    "D_mu psi = (nabla_mu - i q A_mu) psi not selected for this packet"
)
GAMMA_MATRIX_POLICY = (
    "gamma^mu = e_a^mu gamma^a with Clifford relation pinned by the selected "
    "metric and signature policy; explicit representation not selected"
)
TETRAD_POLICY = (
    "tetrad/frame required for curved scope; flat scope may take the trivial frame"
)
SPIN_CONNECTION_POLICY = (
    "spin connection included in nabla_mu psi; explicit coefficients not derived"
)
SPIN_GEOMETRY_POLICY = (
    "curved-background capable spin geometry policy requires gamma matrices, "
    "tetrad/frame, and spin connection placeholders"
)
ADJOINT_POLICY = "psibar = psi^dagger gamma^0 under the selected gamma convention"
FIELD_DOMAIN_POLICY = (
    "smooth finite-action psi and A on the selected spacetime domain; singular "
    "and operator-valued quantum domains not selected"
)
BOUNDARY_VARIATION_POLICY = (
    "compact-support or fixed-boundary variations for psi, psibar, and A"
)
GAUGE_TRANSFORMATION_POLICY = (
    "psi -> exp(-i q chi) psi; A_mu -> A_mu + partial_mu chi for the plus-sign "
    "D_mu convention"
)
CURRENT_CANDIDATE_POLICY = (
    "J^mu_candidate = q psibar gamma^mu psi; candidate only, not derived by A "
    "variation"
)
STRESS_ENERGY_POLICY = (
    "T_A, T_psi, and T_total = T_A + T_psi named as policy objects; T_psi not "
    "derived"
)
EXCHANGE_POLICY = (
    "separate-sector exchange may be nonzero; total conservation is the policy "
    "target"
)
BACKGROUND_SCOPE_POLICY = (
    "flat or curved spacetime scope retained; curved route requires tetrad and "
    "spin connection domains"
)

MATTER_EQUATION_SHAPE_POLICY = SELECTOR_MATTER_EQUATION_SHAPE_PREVIEW
CURRENT_CANDIDATE_PREVIEW = SELECTOR_CURRENT_CANDIDATE_PREVIEW
SOURCED_GAUGE_EQUATION_PREVIEW = SELECTOR_SOURCED_GAUGE_EQUATION_PREVIEW
GAUGE_EXCHANGE_PREVIEW = SELECTOR_GAUGE_EXCHANGE_PREVIEW
MATTER_EXCHANGE_PREVIEW = SELECTOR_MATTER_EXCHANGE_PREVIEW
TOTAL_EXCHANGE_PREVIEW = SELECTOR_TOTAL_EXCHANGE_PREVIEW
C_EXCHANGE_POLICY_PREVIEW = SELECTOR_C_EXCHANGE_PREVIEW
C_EXCHANGE_EQUATION_PREVIEW = SELECTOR_C_EXCHANGE_EQUATION_PREVIEW
X_A_POLICY_PREVIEW = "X_A^nu := nabla_mu T_A^{mu nu} + F^nu_alpha J^alpha"
X_PSI_POLICY_PREVIEW = (
    "X_psi^nu := nabla_mu T_psi^{mu nu} - F^nu_alpha J^alpha"
)

POLICY_ITEMS = [
    "matter surface",
    "gauge group",
    "gauge field",
    "field strength",
    "charge sign convention",
    "covariant derivative",
    "alternate derivative convention",
    "gamma matrices",
    "tetrad/frame policy",
    "spin connection",
    "psibar adjoint",
    "field domains",
    "boundary variation",
    "gauge transformations",
    "current candidate",
    "stress-energy policy",
    "exchange policy",
    "background scope",
]

BLOCKED_CLAIMS = [
    "J^nu derivation",
    "current conservation proof",
    "sourced Maxwell derivation",
    "Dirac equation derivation",
    "matter-gauge exchange proof",
    "psi stress-energy derivation",
    "total stress-energy conservation proof",
    "EM-QFT closure",
    "QFT-GR closure",
    "quantized electromagnetism",
    "anomaly cancellation",
    "Standard Model derivation",
    "Phase 2 authorization",
    "empirical validation",
    "master-action promotion",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _policy_rows() -> list[dict[str, Any]]:
    return [
        {
            "policy_id": "matter_surface",
            "status": "selected_for_interaction_policy",
            "decision": MATTER_SURFACE_POLICY,
            "reason": "The current must come from psi, not from an unexplained external source.",
        },
        {
            "policy_id": "gauge_group",
            "status": "selected_for_interaction_policy",
            "decision": GAUGE_GROUP_POLICY,
            "reason": "The first interaction route is the minimal Abelian gauge test.",
        },
        {
            "policy_id": "gauge_field",
            "status": "selected_for_interaction_policy",
            "decision": GAUGE_FIELD_POLICY,
            "reason": "The A route already supplies the vacuum gauge field surface.",
        },
        {
            "policy_id": "field_strength",
            "status": "selected_for_interaction_policy",
            "decision": FIELD_STRENGTH_POLICY,
            "reason": "The U(1) curvature surface remains F = dA.",
        },
        {
            "policy_id": "charge_sign_convention",
            "status": "selected_for_interaction_policy",
            "decision": CHARGE_POLICY,
            "reason": "A stable q and derivative sign are needed before variation is attempted.",
        },
        {
            "policy_id": "covariant_derivative",
            "status": "selected_for_interaction_policy",
            "decision": COVARIANT_DERIVATIVE_POLICY,
            "reason": "The packet selects the plus-sign D_mu convention for psi.",
        },
        {
            "policy_id": "alternate_derivative_convention",
            "status": "blocked_for_this_packet",
            "decision": ALTERNATE_COVARIANT_DERIVATIVE_REJECTED,
            "reason": "The minus-sign convention is not used in this route packet.",
        },
        {
            "policy_id": "gamma_matrices",
            "status": "selected_as_policy_placeholder",
            "decision": GAMMA_MATRIX_POLICY,
            "reason": "The spinor route needs a gamma policy before a Dirac variation.",
        },
        {
            "policy_id": "tetrad_frame_policy",
            "status": "selected_as_policy_placeholder",
            "decision": TETRAD_POLICY,
            "reason": "Curved-scope spinor coupling needs a frame policy.",
        },
        {
            "policy_id": "spin_connection",
            "status": "selected_as_policy_placeholder",
            "decision": SPIN_CONNECTION_POLICY,
            "reason": "nabla_mu psi must include the spin connection policy.",
        },
        {
            "policy_id": "psibar_adjoint",
            "status": "selected_for_interaction_policy",
            "decision": ADJOINT_POLICY,
            "reason": "The current candidate and matter action need psibar fixed.",
        },
        {
            "policy_id": "field_domains",
            "status": "selected_for_interaction_policy",
            "decision": FIELD_DOMAIN_POLICY,
            "reason": "Field regularity and domain scope must be fixed before derivation.",
        },
        {
            "policy_id": "boundary_variation",
            "status": "selected_for_future_variation_attempt",
            "decision": BOUNDARY_VARIATION_POLICY,
            "reason": "The future route needs boundary terms controlled or removed.",
        },
        {
            "policy_id": "gauge_transformations",
            "status": "selected_for_interaction_policy",
            "decision": GAUGE_TRANSFORMATION_POLICY,
            "reason": "The plus-sign D_mu convention fixes the matching gauge transformation signs.",
        },
        {
            "policy_id": "current_candidate",
            "status": "recorded_as_candidate_not_derived",
            "decision": CURRENT_CANDIDATE_POLICY,
            "reason": "J^mu is a candidate only until A-variation is carried out.",
        },
        {
            "policy_id": "stress_energy_policy",
            "status": "recorded_as_policy_not_derived",
            "decision": STRESS_ENERGY_POLICY,
            "reason": "T_psi and total stress-energy are named, not constructed.",
        },
        {
            "policy_id": "exchange_policy",
            "status": "recorded_as_policy_target_not_proved",
            "decision": EXCHANGE_POLICY,
            "reason": "The packet distinguishes legal transfer from illegal loss without proof.",
        },
        {
            "policy_id": "background_scope",
            "status": "selected_for_interaction_policy",
            "decision": BACKGROUND_SCOPE_POLICY,
            "reason": "The route remains compatible with flat and curved downstream scopes.",
        },
    ]


def _review_criteria(selector: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_expected_psi_a_policy_packet_target",
            "status": "accepted",
            "evidence": selector.get("selected_next_target"),
            "assessment": "The selector authorized this policy packet and no route execution.",
        },
        {
            "row_id": "psi_a_u1_route_selected_by_selector",
            "status": "accepted",
            "evidence": selector.get("selected_interaction_route"),
            "assessment": "The packet consumes the selected psi-A U(1) interaction route.",
        },
        {
            "row_id": "matter_surface_selected",
            "status": "accepted",
            "evidence": MATTER_SURFACE_POLICY,
            "assessment": "psi is pinned as Dirac-like matter or a finite spinor multiplet.",
        },
        {
            "row_id": "u1_gauge_policy_selected",
            "status": "accepted",
            "evidence": [GAUGE_GROUP_POLICY, GAUGE_FIELD_POLICY, FIELD_STRENGTH_POLICY],
            "assessment": "The route uses the U(1) A_mu and F = dA surface.",
        },
        {
            "row_id": "plus_sign_covariant_derivative_selected",
            "status": "accepted",
            "evidence": COVARIANT_DERIVATIVE_POLICY,
            "assessment": "The packet chooses the plus-sign D_mu psi convention.",
        },
        {
            "row_id": "minus_sign_derivative_convention_blocked",
            "status": "accepted",
            "evidence": ALTERNATE_COVARIANT_DERIVATIVE_REJECTED,
            "assessment": "The alternate sign is blocked for this packet.",
        },
        {
            "row_id": "spin_geometry_policy_pinned",
            "status": "accepted",
            "evidence": [
                GAMMA_MATRIX_POLICY,
                TETRAD_POLICY,
                SPIN_CONNECTION_POLICY,
                ADJOINT_POLICY,
            ],
            "assessment": "Gamma, tetrad, spin connection, and psibar policies are pinned.",
        },
        {
            "row_id": "domain_boundary_and_gauge_transforms_pinned",
            "status": "accepted",
            "evidence": [
                FIELD_DOMAIN_POLICY,
                BOUNDARY_VARIATION_POLICY,
                GAUGE_TRANSFORMATION_POLICY,
            ],
            "assessment": "The packet fixes field domains, variations, and gauge signs.",
        },
        {
            "row_id": "current_candidate_recorded_not_derived",
            "status": "accepted",
            "evidence": CURRENT_CANDIDATE_POLICY,
            "assessment": "The current is only a candidate until A variation is performed.",
        },
        {
            "row_id": "stress_energy_and_exchange_policy_recorded_not_proved",
            "status": "accepted",
            "evidence": [STRESS_ENERGY_POLICY, EXCHANGE_POLICY],
            "assessment": "Separate-sector exchange and total balance remain policy targets.",
        },
        {
            "row_id": "c_exchange_preview_recorded_without_functional",
            "status": "accepted",
            "evidence": C_EXCHANGE_POLICY_PREVIEW,
            "assessment": "C_exchange is a future rule-family preview, not a completed functional.",
        },
        {
            "row_id": "background_scope_retained",
            "status": "accepted",
            "evidence": BACKGROUND_SCOPE_POLICY,
            "assessment": "Flat and curved downstream scopes remain bounded by spin geometry policy.",
        },
        {
            "row_id": "no_current_exchange_derivation_closure_or_promotion",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "All derivation, closure, empirical, Phase 2, and promotion claims remain blocked.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_psi_A_u1_current_and_exchange_route_policy_packet",
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


def build_toe_native_psi_a_u1_current_and_exchange_route_policy_packet(
    *,
    selector_path: Path = SELECTOR_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector = _read_json(selector_path)
    policy_rows = _policy_rows()
    review_criteria = _review_criteria(selector)
    acceptance_criteria = {
        "consumes_expected_psi_a_policy_packet_target": (
            selector.get("schema_id") == SELECTOR_SCHEMA_ID
            and selector.get("packet_id") == SELECTOR_PACKET_ID
            and selector.get("outcome_id") == SELECTOR_OUTCOME
            and selector.get("selected_next_target") == CONSUMED_TARGET
            and selector.get("selected_interaction_route") == SELECTED_INTERACTION_ROUTE
            and selector.get("accepted") is True
        ),
        "selector_authorized_policy_preparation_only": (
            selector.get("policy_packet_preparation_authorized") is True
            and selector.get("selected_route_execution_authorized") is False
            and selector.get("psi_A_u1_policy_packet_prepared") is False
        ),
        "selected_fields_and_group_preserved": (
            selector.get("selected_interaction_fields") == SELECTED_INTERACTION_FIELDS
            and selector.get("selected_matter_type_scope") == SELECTED_MATTER_TYPE_SCOPE
            and selector.get("selected_gauge_group") == SELECTED_GAUGE_GROUP
        ),
        "policy_rows_complete": len(policy_rows) == 18,
        "blocked_claims_complete": len(BLOCKED_CLAIMS) == 15,
        "plus_sign_derivative_selected": (
            COVARIANT_DERIVATIVE_POLICY == SELECTOR_COVARIANT_DERIVATIVE_PREVIEW
            and "+ i q A_mu" in COVARIANT_DERIVATIVE_POLICY
            and "- i q A_mu" in ALTERNATE_COVARIANT_DERIVATIVE_REJECTED
        ),
        "gauge_transformation_matches_plus_sign_convention": (
            "exp(-i q chi)" in GAUGE_TRANSFORMATION_POLICY
            and "A_mu -> A_mu + partial_mu chi" in GAUGE_TRANSFORMATION_POLICY
        ),
        "current_candidate_recorded_not_derived": (
            "candidate only" in CURRENT_CANDIDATE_POLICY
            and "not derived" in CURRENT_CANDIDATE_POLICY
        ),
        "exchange_policy_recorded_not_proved": (
            "total conservation" in EXCHANGE_POLICY
            and "policy target" in EXCHANGE_POLICY
            and SELECTOR_TOTAL_EXCHANGE_PREVIEW == TOTAL_EXCHANGE_PREVIEW
        ),
        "c_exchange_preview_recorded_without_completed_functional": (
            "C_exchange" in C_EXCHANGE_POLICY_PREVIEW
            and SELECTOR_C_EXCHANGE_PREVIEW == C_EXCHANGE_POLICY_PREVIEW
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "next_target_is_obligation_packet_preparation": NEXT_TARGET
        == "prepare_toe_native_psi_A_u1_current_and_exchange_derivation_obligation_packet",
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_ROUTE_POLICY_PACKET"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_ROUTE_POLICY_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_ROUTE_POLICY_PACKET_REQUIRES_REMEDIATION",
        "policy_packet_result": POLICY_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selector_schema_id": SELECTOR_SCHEMA_ID,
        "selector_packet_id": SELECTOR_PACKET_ID,
        "selector_outcome": SELECTOR_OUTCOME,
        "selector_selected_route": SELECTED_INTERACTION_ROUTE,
        "selected_interaction_route": SELECTED_INTERACTION_ROUTE,
        "selected_interaction_fields": SELECTED_INTERACTION_FIELDS,
        "selected_matter_type_scope": SELECTED_MATTER_TYPE_SCOPE,
        "selected_gauge_group": SELECTED_GAUGE_GROUP,
        "interaction_policy_selected": prepared,
        "psi_A_u1_policy_packet_prepared": prepared,
        "psi_A_u1_current_and_exchange_route_indexed": prepared,
        "policy_status": (
            "psi_A_u1_interaction_policy_selected_current_and_exchange_"
            "derivation_still_blocked"
        ),
        "policy_items": policy_rows,
        "policy_item_count": len(policy_rows),
        "policy_selected_count": sum(
            1 for row in policy_rows if "selected" in row["status"]
        ),
        "policy_blocked_count": sum(
            1 for row in policy_rows if row["status"].startswith("blocked")
        ),
        "policy_items_expected": POLICY_ITEMS,
        "policy_item_expected_count": len(POLICY_ITEMS),
        "matter_surface_policy": MATTER_SURFACE_POLICY,
        "matter_surface_policy_selected": True,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "u1_gauge_group_selected": True,
        "gauge_field_policy": GAUGE_FIELD_POLICY,
        "gauge_field_A_mu_selected": True,
        "field_strength_policy": FIELD_STRENGTH_POLICY,
        "F_equals_dA_selected": True,
        "charge_policy": CHARGE_POLICY,
        "charge_convention_selected": True,
        "covariant_derivative_policy": COVARIANT_DERIVATIVE_POLICY,
        "plus_sign_covariant_derivative_selected": True,
        "minus_sign_covariant_derivative_selected": False,
        "alternate_covariant_derivative_rejected": ALTERNATE_COVARIANT_DERIVATIVE_REJECTED,
        "gamma_matrix_policy": GAMMA_MATRIX_POLICY,
        "gamma_matrices_policy_selected": True,
        "explicit_gamma_representation_selected": False,
        "tetrad_policy": TETRAD_POLICY,
        "tetrad_frame_policy_selected": True,
        "spin_connection_policy": SPIN_CONNECTION_POLICY,
        "spin_connection_policy_selected": True,
        "spin_geometry_policy": SPIN_GEOMETRY_POLICY,
        "spin_geometry_policy_selected": True,
        "adjoint_policy": ADJOINT_POLICY,
        "psibar_adjoint_policy_selected": True,
        "field_domain_policy": FIELD_DOMAIN_POLICY,
        "field_domains_selected": True,
        "operator_valued_quantum_domain_selected": False,
        "boundary_variation_policy": BOUNDARY_VARIATION_POLICY,
        "boundary_variation_policy_selected": True,
        "boundary_terms_controlled": False,
        "gauge_transformation_policy": GAUGE_TRANSFORMATION_POLICY,
        "gauge_transformation_policy_selected": True,
        "current_candidate_policy": CURRENT_CANDIDATE_POLICY,
        "current_candidate_recorded": True,
        "current_candidate_preview": CURRENT_CANDIDATE_PREVIEW,
        "stress_energy_policy": STRESS_ENERGY_POLICY,
        "stress_energy_policy_selected": True,
        "exchange_policy": EXCHANGE_POLICY,
        "exchange_policy_selected": True,
        "background_scope_policy": BACKGROUND_SCOPE_POLICY,
        "background_scope_policy_selected": True,
        "matter_equation_shape_policy": MATTER_EQUATION_SHAPE_POLICY,
        "matter_equation_shape_recorded": True,
        "sourced_gauge_equation_preview": SOURCED_GAUGE_EQUATION_PREVIEW,
        "gauge_exchange_preview": GAUGE_EXCHANGE_PREVIEW,
        "matter_exchange_preview": MATTER_EXCHANGE_PREVIEW,
        "total_exchange_preview": TOTAL_EXCHANGE_PREVIEW,
        "c_exchange_policy_preview": C_EXCHANGE_POLICY_PREVIEW,
        "c_exchange_equation_preview": C_EXCHANGE_EQUATION_PREVIEW,
        "x_a_policy_preview": X_A_POLICY_PREVIEW,
        "x_psi_policy_preview": X_PSI_POLICY_PREVIEW,
        "c_exchange_rule_family_preview_recorded": True,
        "c_exchange_functional_defined": False,
        "c_exchange_rule_proved": False,
        "separate_sector_exchange_visible": True,
        "total_conservation_policy_required": True,
        "illegal_loss_vs_legal_transfer_distinction_required": True,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": prepared,
        "policy_packet_only": True,
        "derivation_packet": False,
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
        "psi_stress_energy_derived": False,
        "T_psi_derived": False,
        "total_stress_energy_conservation_proved": False,
        "T_total_conservation_proved": False,
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
            "treat policy selection as J^nu derivation",
            "claim current conservation",
            "derive sourced Maxwell",
            "derive the Dirac equation",
            "prove matter-gauge exchange",
            "derive T_psi or total stress-energy conservation",
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
                "stage": "toe_native_psi_A_u1_current_and_exchange_route_policy_packet",
                "status": "INTERACTION_POLICY_SELECTED_DERIVATION_STILL_BLOCKED",
                "decision": POLICY_PACKET_RESULT,
                "reason": (
                    "The packet pins the psi-A U(1) convention surface before "
                    "any current, sourced equation, or exchange derivation."
                ),
            },
            {
                "stage": "toe_native_psi_A_u1_current_and_exchange_derivation_obligation_packet",
                "status": "NEXT_TARGET_AUTHORIZED_FOR_PREPARATION_ONLY",
                "decision": selected_next_target,
                "reason": (
                    "The next packet may enumerate the exact derivation "
                    "obligations for current and exchange without closing them "
                    "by policy selection."
                ),
            },
        ],
        "mathematical_statement": (
            "This policy packet selects the first ToE-native psi-A U(1) "
            "interaction policy surface. It pins psi as Dirac-like spinor "
            "matter or a finite spinor multiplet, A_mu as the U(1) gauge "
            "potential, F = dA, real charge q, the plus-sign convention "
            "D_mu psi = (nabla_mu + i q A_mu) psi, matching gauge transforms, "
            "spin-geometry placeholders, psibar, field domains, boundary "
            "variation policy, a current candidate, stress-energy names, and "
            "the total-exchange policy target."
        ),
        "non_claim_boundary": (
            "This policy packet prepares the psi-A U(1) current and exchange "
            "route only as policy. It does not derive J^nu, does not prove "
            "current conservation, does not derive sourced Maxwell, does not "
            "derive the Dirac equation, does not prove matter-gauge exchange, "
            "does not derive psi stress-energy, does not prove total stress-"
            "energy conservation, does not define or prove a completed "
            "C_exchange functional, does not close EM-QFT, does not close "
            "QFT-GR, does not quantize electromagnetism, does not prove "
            "anomaly cancellation, does not derive the Standard Model, does "
            "not authorize Phase 2, records no Phase 2 authorization, does "
            "not claim empirical validation, and does not promote the master "
            "action. The full ToeFormal aggregate is recorded as NOT_RUN for "
            "this packet."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePsiAU1CurrentAndExchangeRoutePolicyPacket",
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


def write_toe_native_psi_a_u1_current_and_exchange_route_policy_packet(
    *,
    selector_path: Path = SELECTOR_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_toe_native_psi_a_u1_current_and_exchange_route_policy_packet(
        selector_path=selector_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the ToE-native psi-A U(1) current and exchange route policy packet."
        )
    )
    parser.add_argument("--selector", type=Path, default=SELECTOR_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    selector_path = args.selector if args.selector.is_absolute() else REPO_ROOT / args.selector
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = write_toe_native_psi_a_u1_current_and_exchange_route_policy_packet(
        selector_path=selector_path,
        out=out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "toe_native_psi_a_u1_current_and_exchange_route_policy_packet_report: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
