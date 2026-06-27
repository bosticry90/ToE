from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.master_action_surface_selection_after_ck_family_gap_review_result_review_report import (
    C_BRIDGE_CLASSIFICATION,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CLASSIFICATION,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_SOURCE_CLASSIFICATION,
    C_TRANSPORT_CLASSIFICATION,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as PRIOR_SELECTOR_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH as PRIOR_SELECTOR_REVIEW_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as PRIOR_SELECTOR_REVIEW_OUTCOME,
    PACKET_ID as PRIOR_SELECTOR_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as PRIOR_SELECTOR_REVIEW_SCHEMA_ID,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-26T00:00:00Z"

SCHEMA_ID = "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_20260626_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_v0"
INDEX_RESULT = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_PREPARED_RULE_FAMILY_"
    "THEOREM_LINKAGE_AND_PROOF_DEBT_ROWS_INDEXED_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = INDEX_RESULT
PACKET_CLASSIFICATION = (
    "ck_family_theorem_linkage_obligation_index_prepared_rule_family_"
    "theorem_linkage_and_proof_debt_rows_indexed_no_action_variation_or_"
    "master_action_promotion"
)

NEXT_TARGET = "review_ck_family_theorem_linkage_obligation_index_result"
NEXT_TARGET_KIND = "ck_family_theorem_linkage_obligation_index_result_review"

OBLIGATION_ROW_IDS = [
    "C_source^phi",
    "C_bridge^phi",
    "C_transport^phi",
    "C_source^A",
    "C_bridge^A",
    "C_transport^A",
    "psi-A current route",
    "psi-A current conservation",
    "psi-A sourced gauge route",
    "psi-A gauge-sector exchange",
    "psi-A matter-sector exchange",
    "psi-A total conservation",
    "C_exchange^{Apsi}",
]

OBLIGATION_ROW_FIELDS = [
    "rule family",
    "field or interaction scope",
    "current evidence pointer",
    "theorem-linkage status",
    "supplied assumptions",
    "open proof debt",
    "functionalization blocker",
    "variation blocker",
    "seam-closure blocker",
    "next possible theorem slice",
]

CONTROLLED_STATUS_LABELS = [
    "THEOREM_LINKED_CONDITIONAL",
    "ROUTE_CONSTRUCTED_UNDER_ASSUMPTIONS",
    "POLICY_LINKED_ADMISSIBILITY_ONLY",
    "SUPPLIED_ASSUMPTION_DEPENDENT",
    "NOT_FUNCTIONALIZED",
    "NOT_VARIED",
    "OPEN_PROOF_DEBT",
]

BLOCKED_CLAIMS = [
    "no GAP-1 through GAP-8 discharge",
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k action variation",
    "no multiplier route",
    "no penalty route",
    "no direct dynamical-law claim",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no Standard Model derivation",
    "no Phase 2 authorization",
    "no empirical validation",
    "no seam closure",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_20260626_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CKFamilyTheoremLinkageObligationIndex.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "C_k_action_embedding_claimed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_authorized": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "ck_action_embedding_claimed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "multiplier_route_selected": False,
        "multiplier_action_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_claimed": False,
        "direct_dynamical_law_interpretation_selected": False,
        "dynamical_law_claimed": False,
        "functional_action_embedding_claimed": False,
        "functionalization_authorized": False,
        "C_exchange_functional_embedding_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "full_em_closure_claimed": False,
        "em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "standard_model_derivation_claimed": False,
        "phase2_authorized": False,
        "phase2_readiness_claim": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "pillar_completion_inferred": False,
        "theorem_linkage_completed": False,
        "assumption_discharge_completed": False,
        "gap_review_closes_any_gap": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "rule_promoted": False,
        "obligation_row_discharged": False,
        "obligation_rows_discharged": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "new_physics_created": False,
        "new_field_or_interaction_expansion_selected": False,
        "immediate_new_field_or_interaction_expansion_selected": False,
    }


def _input_boundary_clear(review: dict[str, Any]) -> bool:
    return all(
        review.get(key) is False
        for key in _false_boundary_flags()
        if key in review
    )


def _row(
    *,
    row_id: str,
    rule_family: str,
    scope: str,
    evidence: str,
    theorem_status: str,
    supplied_assumptions: str,
    open_proof_debt: str,
    functionalization_blocker: str,
    variation_blocker: str,
    seam_closure_blocker: str,
    next_theorem_slice: str,
    supporting_evidence: list[str] | None = None,
    extra_statuses: list[str] | None = None,
) -> dict[str, Any]:
    statuses = [theorem_status]
    if extra_statuses:
        statuses.extend(extra_statuses)
    for status in ["NOT_FUNCTIONALIZED", "NOT_VARIED", "OPEN_PROOF_DEBT"]:
        if status not in statuses:
            statuses.append(status)
    return {
        "row_id": row_id,
        "rule_family": rule_family,
        "field_or_interaction_scope": scope,
        "current_evidence_pointer": evidence,
        "supporting_evidence_pointers": supporting_evidence or [],
        "theorem_linkage_status": theorem_status,
        "controlled_statuses": statuses,
        "supplied_assumptions": supplied_assumptions,
        "open_proof_debt": open_proof_debt,
        "functionalization_blocker": functionalization_blocker,
        "variation_blocker": variation_blocker,
        "seam_closure_blocker": seam_closure_blocker,
        "next_possible_theorem_slice": next_theorem_slice,
        "required_fields_recorded": OBLIGATION_ROW_FIELDS,
        "obligation_index_row_only": True,
        "proof_attempt_executed": False,
        "proof_obligation_discharged": False,
        "gap_discharged": False,
        "rule_promoted": False,
        "functionalized": False,
        "varied": False,
        "seam_closed": False,
    }


def _obligation_rows() -> list[dict[str, Any]]:
    no_functionalization = (
        "NOT_FUNCTIONALIZED: no safe C_k action embedding, multiplier route, "
        "or penalty route has been licensed."
    )
    no_variation = (
        "NOT_VARIED: no C_k variation theorem exists, and the row is not an "
        "Euler-Lagrange or direct dynamical-law claim."
    )
    no_seam_closure = (
        "OPEN_PROOF_DEBT: this row does not close full Maxwell, EM-QFT, QFT-GR, "
        "GR-QM, Standard Model, empirical, or master-action seams."
    )
    phi_assumptions = (
        "Accepted phi route packet and C_k admissibility closeout; domain, "
        "route, bridge, and transport policies remain supplied."
    )
    a_assumptions = (
        "Accepted vacuum U(1) A route packet and C_k admissibility closeout; "
        "gauge policy, stress-energy policy, route, bridge, and transport "
        "assumptions remain supplied."
    )
    psi_a_domain_assumptions = (
        "Selected psi-A U(1) action-block, Dirac/adjoint route, gamma and "
        "spin/tetrad policies, sign conventions, stress-energy policies, "
        "domain assumptions, and boundary assumptions."
    )
    return [
        _row(
            row_id="C_source^phi",
            rule_family="C_source",
            scope="isolated phi field",
            evidence=(
                "formal/toe_formal/ToeFormal/Derivation/"
                "PhiSourceAdmissibilityCKAdmissibilityRuleCloseout.lean"
            ),
            theorem_status="POLICY_LINKED_ADMISSIBILITY_ONLY",
            supplied_assumptions=phi_assumptions,
            open_proof_debt=(
                "Prove a soundness theorem linking the accepted phi source "
                "route to C_source^phi = 0 and classify which assumptions are "
                "mathematical, policy-level, or still supplied."
            ),
            functionalization_blocker=no_functionalization,
            variation_blocker=no_variation,
            seam_closure_blocker=no_seam_closure,
            next_theorem_slice=(
                "C_source^phi route-to-admissibility soundness lemma under "
                "recorded assumptions."
            ),
            extra_statuses=["SUPPLIED_ASSUMPTION_DEPENDENT"],
        ),
        _row(
            row_id="C_bridge^phi",
            rule_family="C_bridge",
            scope="isolated phi field",
            evidence=(
                "formal/toe_formal/ToeFormal/Derivation/"
                "PhiBridgeAdmissibilityCKAdmissibilityRuleCloseout.lean"
            ),
            theorem_status="POLICY_LINKED_ADMISSIBILITY_ONLY",
            supplied_assumptions=phi_assumptions,
            open_proof_debt=(
                "Prove a route-matching theorem for the accepted phi bridge "
                "and separate bridge soundness from policy-level acceptance."
            ),
            functionalization_blocker=no_functionalization,
            variation_blocker=no_variation,
            seam_closure_blocker=no_seam_closure,
            next_theorem_slice=(
                "C_bridge^phi route-equivalence and bridge-soundness lemma."
            ),
            extra_statuses=["SUPPLIED_ASSUMPTION_DEPENDENT"],
        ),
        _row(
            row_id="C_transport^phi",
            rule_family="C_transport",
            scope="isolated phi field",
            evidence=(
                "formal/toe_formal/ToeFormal/Derivation/"
                "PhiTransportConsistencyCKAdmissibilityRuleCloseout.lean"
            ),
            theorem_status="POLICY_LINKED_ADMISSIBILITY_ONLY",
            supplied_assumptions=phi_assumptions,
            open_proof_debt=(
                "Prove that the accepted phi derivation chain preserves meaning "
                "through transport rather than only recording a route check."
            ),
            functionalization_blocker=no_functionalization,
            variation_blocker=no_variation,
            seam_closure_blocker=no_seam_closure,
            next_theorem_slice=(
                "C_transport^phi derivation-chain stability lemma."
            ),
            extra_statuses=["SUPPLIED_ASSUMPTION_DEPENDENT"],
        ),
        _row(
            row_id="C_source^A",
            rule_family="C_source",
            scope="isolated vacuum U(1) A field",
            evidence=(
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativeASourceAdmissibilityCKAdmissibilityRuleCloseout.lean"
            ),
            theorem_status="POLICY_LINKED_ADMISSIBILITY_ONLY",
            supplied_assumptions=a_assumptions,
            open_proof_debt=(
                "Prove a soundness theorem linking the accepted A source route "
                "to C_source^A = 0 and isolate gauge/stress-energy assumptions."
            ),
            functionalization_blocker=no_functionalization,
            variation_blocker=no_variation,
            seam_closure_blocker=no_seam_closure,
            next_theorem_slice=(
                "C_source^A vacuum U(1) source-admissibility soundness lemma."
            ),
            extra_statuses=["SUPPLIED_ASSUMPTION_DEPENDENT"],
        ),
        _row(
            row_id="C_bridge^A",
            rule_family="C_bridge",
            scope="isolated vacuum U(1) A field",
            evidence=(
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativeABridgeAdmissibilityCKAdmissibilityRuleCloseout.lean"
            ),
            theorem_status="POLICY_LINKED_ADMISSIBILITY_ONLY",
            supplied_assumptions=a_assumptions,
            open_proof_debt=(
                "Prove the accepted A route-matching bridge under U(1) policy "
                "without treating the bridge rule as a new field equation."
            ),
            functionalization_blocker=no_functionalization,
            variation_blocker=no_variation,
            seam_closure_blocker=no_seam_closure,
            next_theorem_slice=(
                "C_bridge^A route-equivalence and bridge-soundness lemma."
            ),
            extra_statuses=["SUPPLIED_ASSUMPTION_DEPENDENT"],
        ),
        _row(
            row_id="C_transport^A",
            rule_family="C_transport",
            scope="isolated vacuum U(1) A field",
            evidence=(
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativeATransportConsistencyCKAdmissibilityRuleCloseout.lean"
            ),
            theorem_status="POLICY_LINKED_ADMISSIBILITY_ONLY",
            supplied_assumptions=a_assumptions,
            open_proof_debt=(
                "Prove that the accepted A derivation chain preserves meaning "
                "through transport rather than only passing a route-level check."
            ),
            functionalization_blocker=no_functionalization,
            variation_blocker=no_variation,
            seam_closure_blocker=no_seam_closure,
            next_theorem_slice=(
                "C_transport^A derivation-chain stability lemma."
            ),
            extra_statuses=["SUPPLIED_ASSUMPTION_DEPENDENT"],
        ),
        _row(
            row_id="psi-A current route",
            rule_family="current route",
            scope="psi-A U(1) interaction",
            evidence=(
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1CurrentDerivationFromAVariationPacket.lean"
            ),
            theorem_status="ROUTE_CONSTRUCTED_UNDER_ASSUMPTIONS",
            supplied_assumptions=psi_a_domain_assumptions,
            open_proof_debt=(
                "Convert the A-variation current candidate J^mu = q psibar "
                "gamma^mu psi into a theorem with explicit sign, domain, and "
                "boundary controls."
            ),
            functionalization_blocker=no_functionalization,
            variation_blocker=no_variation,
            seam_closure_blocker=no_seam_closure,
            next_theorem_slice=(
                "A-variation-to-current theorem for J^mu = q psibar gamma^mu psi."
            ),
            supporting_evidence=[
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1CurrentDerivationFromAVariationResultReview.lean"
            ],
            extra_statuses=["SUPPLIED_ASSUMPTION_DEPENDENT"],
        ),
        _row(
            row_id="psi-A current conservation",
            rule_family="current conservation",
            scope="psi-A U(1) interaction",
            evidence=(
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1CurrentConservationFromDiracPairPacket.lean"
            ),
            theorem_status="THEOREM_LINKED_CONDITIONAL",
            supplied_assumptions=psi_a_domain_assumptions,
            open_proof_debt=(
                "Formalize the Dirac-pair cancellation proof for nabla_mu "
                "J^mu = 0 and discharge or explicitly retain every connection, "
                "gamma, domain, and boundary assumption."
            ),
            functionalization_blocker=no_functionalization,
            variation_blocker=no_variation,
            seam_closure_blocker=no_seam_closure,
            next_theorem_slice=(
                "Dirac-pair current-conservation theorem under selected assumptions."
            ),
            supporting_evidence=[
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1CurrentConservationObligationPacket.lean",
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1PsiVariationDiracRoutePacket.lean",
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1AdjointDiracRoutePacket.lean",
            ],
            extra_statuses=["SUPPLIED_ASSUMPTION_DEPENDENT"],
        ),
        _row(
            row_id="psi-A sourced gauge route",
            rule_family="sourced gauge route",
            scope="psi-A U(1) interaction",
            evidence=(
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1SourcedMaxwellRoutePacket.lean"
            ),
            theorem_status="ROUTE_CONSTRUCTED_UNDER_ASSUMPTIONS",
            supplied_assumptions=psi_a_domain_assumptions,
            open_proof_debt=(
                "Prove the sourced gauge route nabla_mu F^{mu nu} = J^nu from "
                "the accepted current and field assumptions without claiming "
                "full Maxwell or EM closure."
            ),
            functionalization_blocker=no_functionalization,
            variation_blocker=no_variation,
            seam_closure_blocker=no_seam_closure,
            next_theorem_slice=(
                "Sourced Maxwell route theorem under the accepted psi-A U(1) policy."
            ),
            extra_statuses=["SUPPLIED_ASSUMPTION_DEPENDENT"],
        ),
        _row(
            row_id="psi-A gauge-sector exchange",
            rule_family="gauge-sector exchange",
            scope="psi-A U(1) interaction",
            evidence=(
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1GaugeSectorExchangeRoutePacket.lean"
            ),
            theorem_status="THEOREM_LINKED_CONDITIONAL",
            supplied_assumptions=psi_a_domain_assumptions,
            open_proof_debt=(
                "Prove nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha with "
                "stress-energy, sign, metric, and boundary assumptions exposed."
            ),
            functionalization_blocker=no_functionalization,
            variation_blocker=no_variation,
            seam_closure_blocker=no_seam_closure,
            next_theorem_slice=(
                "Gauge-sector exchange divergence theorem under selected U(1) policy."
            ),
            supporting_evidence=[
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1GaugeSectorExchangeRouteResultReview.lean"
            ],
            extra_statuses=["SUPPLIED_ASSUMPTION_DEPENDENT"],
        ),
        _row(
            row_id="psi-A matter-sector exchange",
            rule_family="matter-sector exchange",
            scope="psi-A U(1) interaction",
            evidence=(
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1MatterSectorExchangeRoutePacket.lean"
            ),
            theorem_status="THEOREM_LINKED_CONDITIONAL",
            supplied_assumptions=psi_a_domain_assumptions,
            open_proof_debt=(
                "Prove nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha "
                "from the Dirac, adjoint, stress-energy, sign, and boundary "
                "assumptions."
            ),
            functionalization_blocker=no_functionalization,
            variation_blocker=no_variation,
            seam_closure_blocker=no_seam_closure,
            next_theorem_slice=(
                "Matter-sector exchange divergence theorem under selected "
                "psi-A U(1) assumptions."
            ),
            supporting_evidence=[
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1MatterSectorExchangeRouteResultReview.lean"
            ],
            extra_statuses=["SUPPLIED_ASSUMPTION_DEPENDENT"],
        ),
        _row(
            row_id="psi-A total conservation",
            rule_family="total stress-energy conservation",
            scope="psi-A U(1) interaction",
            evidence=(
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1TotalStressEnergyConservationRoutePacket.lean"
            ),
            theorem_status="THEOREM_LINKED_CONDITIONAL",
            supplied_assumptions=psi_a_domain_assumptions,
            open_proof_debt=(
                "Formalize the cancellation of the accepted gauge and matter "
                "exchange halves into nabla_mu T_total^{mu nu} = 0, including "
                "stress-energy object and domain assumptions."
            ),
            functionalization_blocker=no_functionalization,
            variation_blocker=no_variation,
            seam_closure_blocker=no_seam_closure,
            next_theorem_slice=(
                "Total stress-energy conservation theorem from accepted "
                "equal-and-opposite exchange halves."
            ),
            supporting_evidence=[
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1TotalStressEnergyConservationRouteResultReview.lean"
            ],
            extra_statuses=["SUPPLIED_ASSUMPTION_DEPENDENT"],
        ),
        _row(
            row_id="C_exchange^{Apsi}",
            rule_family="C_exchange",
            scope="psi-A U(1) interaction admissibility",
            evidence=(
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1CExchangeAdmissibilityRuleCloseout.lean"
            ),
            theorem_status="POLICY_LINKED_ADMISSIBILITY_ONLY",
            supplied_assumptions=(
                "Accepted total conservation route plus the C_exchange "
                "admissibility-rule closeout; no action embedding, no multiplier "
                "route, no penalty route, and no C_k variation."
            ),
            open_proof_debt=(
                "Prove that the total-conservation route soundly licenses "
                "C_exchange^{Apsi,nu} = 0 as an admissibility rule and determine "
                "what would be required to generalize beyond psi-A U(1)."
            ),
            functionalization_blocker=no_functionalization,
            variation_blocker=no_variation,
            seam_closure_blocker=no_seam_closure,
            next_theorem_slice=(
                "C_exchange route-to-admissibility soundness theorem under "
                "accepted total-conservation assumptions."
            ),
            supporting_evidence=[
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1InteractionExchangeRuleFamilyCloseout.lean",
                "formal/toe_formal/ToeFormal/Derivation/"
                "ToeNativePsiAU1InteractionExchangeRuleFamilyCloseoutResultReview.lean",
            ],
            extra_statuses=[
                "THEOREM_LINKED_CONDITIONAL",
                "SUPPLIED_ASSUMPTION_DEPENDENT",
            ],
        ),
    ]


def _index_criteria(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "all_required_rows_indexed",
            "status": "accepted",
            "evidence": [row["row_id"] for row in rows],
            "assessment": "The 13 required theorem-linkage obligation rows are indexed.",
        },
        {
            "row_id": "required_fields_recorded",
            "status": "accepted",
            "evidence": OBLIGATION_ROW_FIELDS,
            "assessment": "Each row records the required proof-obligation fields.",
        },
        {
            "row_id": "controlled_status_labels_used",
            "status": "accepted",
            "evidence": CONTROLLED_STATUS_LABELS,
            "assessment": "The index uses controlled theorem-linkage status labels.",
        },
        {
            "row_id": "no_gap_discharge",
            "status": "accepted",
            "evidence": "closed_gap_count=0",
            "assessment": "GAP-1 through GAP-8 remain open; none is discharged.",
        },
        {
            "row_id": "no_rule_promotion",
            "status": "accepted",
            "evidence": "rule_promoted=false",
            "assessment": "No C_k rule is promoted by the index.",
        },
        {
            "row_id": "no_functionalization_or_variation",
            "status": "accepted",
            "evidence": ["NOT_FUNCTIONALIZED", "NOT_VARIED"],
            "assessment": "No C_k action embedding, multiplier route, penalty route, or C_k variation occurs.",
        },
        {
            "row_id": "no_seam_empirical_or_master_action_promotion",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "No seam closure, empirical validation, or master-action promotion occurs.",
        },
        {
            "row_id": "full_toeformal_aggregate_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full ToeFormal aggregate is preserved as NOT_RUN.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "ck_family_theorem_linkage_obligation_index_preparation",
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


def build_ck_family_theorem_linkage_obligation_index(
    *,
    selector_review_path: Path = PRIOR_SELECTOR_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector_review = _read_json(selector_review_path)
    rows = _obligation_rows()
    criteria = _index_criteria(rows)
    row_statuses = {
        status for row in rows for status in row["controlled_statuses"]
    }
    acceptance_criteria = {
        "consumes_expected_theorem_linkage_index_preparation_target": (
            selector_review.get("schema_id") == PRIOR_SELECTOR_REVIEW_SCHEMA_ID
            and selector_review.get("packet_id") == PRIOR_SELECTOR_REVIEW_PACKET_ID
            and selector_review.get("outcome_id") == PRIOR_SELECTOR_REVIEW_OUTCOME
            and selector_review.get("review_result") == PRIOR_SELECTOR_REVIEW_OUTCOME
            and selector_review.get("packet_result") == PRIOR_SELECTOR_REVIEW_OUTCOME
            and selector_review.get("selected_next_target") == CONSUMED_TARGET
            and selector_review.get("accepted") is True
        ),
        "thirteen_obligation_rows_indexed": (
            [row["row_id"] for row in rows] == OBLIGATION_ROW_IDS
            and len(rows) == 13
        ),
        "required_fields_indexed": (
            len(OBLIGATION_ROW_FIELDS) == 10
            and all(row["required_fields_recorded"] == OBLIGATION_ROW_FIELDS for row in rows)
        ),
        "controlled_status_labels_preserved": row_statuses.issubset(
            set(CONTROLLED_STATUS_LABELS)
        ),
        "no_row_discharged_or_promoted": all(
            row["proof_obligation_discharged"] is False
            and row["gap_discharged"] is False
            and row["rule_promoted"] is False
            and row["functionalized"] is False
            and row["varied"] is False
            and row["seam_closed"] is False
            for row in rows
        ),
        "rule_architecture_context_preserved": (
            selector_review.get("C_source_classification") == C_SOURCE_CLASSIFICATION
            and selector_review.get("C_bridge_classification") == C_BRIDGE_CLASSIFICATION
            and selector_review.get("C_transport_classification")
            == C_TRANSPORT_CLASSIFICATION
            and selector_review.get("C_exchange_classification")
            == C_EXCHANGE_CLASSIFICATION
            and selector_review.get("C_exchange_admissibility_condition")
            == C_EXCHANGE_ADMISSIBILITY_CONDITION
        ),
        "all_gaps_remain_open": (
            selector_review.get("gap_count") == 8
            and selector_review.get("open_gap_count") == 8
            and selector_review.get("closed_gap_count") == 0
            and selector_review.get("no_gap_discharged") is True
            and selector_review.get("no_gap_closed") is True
        ),
        "no_input_forbidden_claims": _input_boundary_clear(selector_review),
        "index_criteria_all_accepted": all(row["status"] == "accepted" for row in criteria),
        "full_toeformal_aggregate_recorded_not_run": (
            selector_review.get("aggregate_lean_validation_status_for_review")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and selector_review.get("full_toeformal_aggregate_status_for_review")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and selector_review.get("full_toeformal_aggregate_passed") is False
            and selector_review.get("full_toeformal_aggregate_failed") is False
            and selector_review.get("full_toeformal_aggregate_timed_out") is False
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX"
    )
    theorem_status_counts = {
        status: sum(1 for row in rows if row["theorem_linkage_status"] == status)
        for status in CONTROLLED_STATUS_LABELS
    }
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_REQUIRES_REMEDIATION",
        "index_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_INDEX_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_follow_on_target_after_review": NEXT_TARGET,
        "selected_follow_on_target_kind": NEXT_TARGET_KIND,
        "prior_selector_review_schema_id": PRIOR_SELECTOR_REVIEW_SCHEMA_ID,
        "prior_selector_review_packet_id": PRIOR_SELECTOR_REVIEW_PACKET_ID,
        "prior_selector_review_outcome": PRIOR_SELECTOR_REVIEW_OUTCOME,
        "proof_obligation_rows": rows,
        "proof_obligation_row_ids": OBLIGATION_ROW_IDS,
        "proof_obligation_row_count": len(rows),
        "obligation_row_fields": OBLIGATION_ROW_FIELDS,
        "obligation_row_field_count": len(OBLIGATION_ROW_FIELDS),
        "controlled_status_labels": CONTROLLED_STATUS_LABELS,
        "controlled_status_label_count": len(CONTROLLED_STATUS_LABELS),
        "theorem_linkage_status_counts": theorem_status_counts,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "index_criteria": criteria,
        "index_criteria_count": len(criteria),
        "index_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "theorem_linkage_obligation_index_prepared": accepted,
        "theorem_linkage_obligation_index_executed": accepted,
        "theorem_linkage_obligation_index_reviewed": False,
        "obligation_index_prepared": accepted,
        "obligation_index_executed": accepted,
        "obligation_index_reviewed": False,
        "proof_obligation_rows_indexed": accepted,
        "rule_family_theorem_linkage_and_proof_debt_rows_indexed": accepted,
        "row_index_only": accepted,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "obligation_rows_discharged": False,
        "obligation_row_discharged": False,
        "gap_1_through_gap_8_indexed": accepted,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "no_rule_promoted": accepted,
        "no_C_k_functionalization_occurs": accepted,
        "no_C_k_variation_occurs": accepted,
        "no_seam_closure_occurs": accepted,
        "no_master_action_promotion_occurs": accepted,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "all_C_k_families_admissibility_only": accepted,
        "all_summarized_rules_admissibility_only": accepted,
        "all_summarized_rules_not_action_embedded": accepted,
        "all_summarized_rules_not_varied": accepted,
        "all_summarized_rules_not_direct_dynamical_laws": accepted,
        "all_summarized_rules_not_empirical_claims": accepted,
        "C_source_classification": C_SOURCE_CLASSIFICATION,
        "C_bridge_classification": C_BRIDGE_CLASSIFICATION,
        "C_transport_classification": C_TRANSPORT_CLASSIFICATION,
        "C_exchange_classification": C_EXCHANGE_CLASSIFICATION,
        "current_candidate": CURRENT_CANDIDATE,
        "current_conservation_result": CURRENT_CONSERVATION_RESULT,
        "sourced_gauge_route": SOURCED_GAUGE_ROUTE,
        "gauge_sector_exchange_identity": GAUGE_SECTOR_EXCHANGE_IDENTITY,
        "matter_sector_exchange_identity": MATTER_SECTOR_EXCHANGE_IDENTITY,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_constraint_form": C_EXCHANGE_CONSTRAINT_FORM,
        "C_exchange_admissibility_condition": C_EXCHANGE_ADMISSIBILITY_CONDITION,
        "plain_meaning": (
            "The open C_k gaps are converted into a row-by-row theorem-linkage "
            "and proof-debt map. The map does not solve the gaps."
        ),
        "mathematical_statement": (
            "The index records proof-obligation rows for C_source^phi, "
            "C_bridge^phi, C_transport^phi, C_source^A, C_bridge^A, "
            "C_transport^A, psi-A current route, psi-A current conservation, "
            "psi-A sourced gauge route, psi-A gauge-sector exchange, psi-A "
            "matter-sector exchange, psi-A total conservation, and "
            "C_exchange^{Apsi}. It preserves J^mu = q psibar gamma^mu psi, "
            "nabla_mu J^mu = 0, nabla_mu F^{mu nu} = J^nu, the gauge and "
            "matter exchange identities, total conservation, and "
            "C_exchange^{Apsi,nu} = 0 as bounded route context only."
        ),
        "non_claim_boundary": (
            "This packet prepares only the C_k family theorem-linkage obligation "
            "index. It discharges no GAP-1 through GAP-8 item, proves no row, "
            "promotes no C_k rule, embeds no C_k rule in an action, varies no "
            "C_k rule, selects no multiplier route, selects no penalty route, "
            "makes no direct dynamical-law claim, closes no full Maxwell, "
            "EM-QFT, QFT-GR, GR-QM, Standard Model, empirical, or seam target, "
            "and promotes no master action. The master action remains a "
            "working-form, noncanonical, non-promoted organizing surface. The "
            "full ToeFormal aggregate is kept as NOT_RUN."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_ck_family_theorem_linkage_obligation_index",
            "fail to index all 13 required obligation rows",
            "merge psi-A current route and psi-A current conservation into one row",
            "fail to record the ten required row fields",
            "use uncontrolled theorem-linkage statuses",
            "claim any GAP-1 through GAP-8 item is discharged",
            "claim any row proof debt is reduced or discharged",
            "promote any C_k rule",
            "claim any C_k family is action embedded",
            "authorize or execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "claim a direct dynamical-law interpretation",
            "claim full Maxwell closure",
            "claim EM-QFT closure",
            "claim QFT-GR closure",
            "claim GR-QM closure",
            "derive the Standard Model",
            "authorize Phase 2",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.CKFamilyTheoremLinkageObligationIndex",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "prior_selector_review_file": _ptr(selector_review_path),
            "prior_selector_review_lean_file": _ptr(
                PRIOR_SELECTOR_REVIEW_LEAN_PACKET_PATH
            ),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }
    payload.update(_false_boundary_flags())
    return payload


def write_index(index: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(index, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the C_k family theorem-linkage obligation index."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--selector-review", type=Path, default=PRIOR_SELECTOR_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    selector_review_path = (
        args.selector_review
        if args.selector_review.is_absolute()
        else REPO_ROOT / args.selector_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_ck_family_theorem_linkage_obligation_index(
        selector_review_path=selector_review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_index(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "index_result": payload["index_result"],
                "out": _ptr(path),
                "proof_obligation_row_count": payload["proof_obligation_row_count"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
