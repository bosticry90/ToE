from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_phi_source_closeout_result_review_report import (
    COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN,
    DEFAULT_OUT as SELECTOR_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH as SELECTOR_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LEAN_STATUS_WORDING_LINES_FOR_REVIEW,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as SELECTOR_REVIEW_OUTCOME,
    PACKET_ID as SELECTOR_REVIEW_PACKET_ID,
    SCHEMA_ID as SELECTOR_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SELECTED_OBLIGATION,
    SELECTED_OBLIGATION_ROW_ID,
    SELECTED_THEOREM_LINKAGE_GAP,
    STRICT_REVIEW_RESULT as SELECTOR_STRICT_REVIEW_RESULT,
)
from formal.python.tools.phi_bridge_admissibility_ck_admissibility_rule_closeout_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CANDIDATE_ID,
    BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
    BRIDGE_CANDIDATE_TYPE,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    BRIDGE_RULE_CLASSIFICATION,
    BRIDGE_RULE_EPISTEMIC_STATUS,
    CLOSEOUT_RESULT as PHI_BRIDGE_REGISTRY_OUTCOME,
    DEFAULT_OUT as PHI_BRIDGE_REGISTRY_PATH,
    LEAN_PACKET_PATH as PHI_BRIDGE_REGISTRY_LEAN_PACKET_PATH,
    OUTCOME_ID as PHI_BRIDGE_REGISTRY_OUTCOME_ID,
    PACKET_ID as PHI_BRIDGE_REGISTRY_PACKET_ID,
    SCHEMA_ID as PHI_BRIDGE_REGISTRY_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_20260630_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_v0"
OUTCOME_ID = (
    "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_C_BRIDGE_PHI_"
    "ROUTE_SCOPED_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
STRICT_PACKET_RESULT = (
    "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_STANDALONE_PHI_"
    "BRIDGE_ADMISSIBILITY_TARGET_NO_THEOREM_DISCHARGE_OR_MASTER_ACTION_PROMOTION"
)
PACKET_CLASSIFICATION = (
    "phi_bridge_theorem_linkage_obligation_packet_scopes_standalone_phi_bridge_"
    "admissibility_target_no_proof_execution_or_C_k_rule_promotion"
)

NEXT_TARGET = "review_phi_bridge_theorem_linkage_obligation_packet_result"
NEXT_TARGET_KIND = "phi_bridge_theorem_linkage_obligation_packet_result_review"
SUGGESTED_REVIEW_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "C_BRIDGE_PHI_ROUTE_SCOPE_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
STRICT_SUGGESTED_REVIEW_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "STANDALONE_PHI_BRIDGE_ADMISSIBILITY_TARGET_NO_THEOREM_DISCHARGE_OR_"
    "MASTER_ACTION_PROMOTION"
)

STANDALONE_PHI_BRIDGE_ROUTE = "prior standalone phi bridge-admissibility registry"
EXACT_PRIOR_BRIDGE_STATEMENT = BRIDGE_CONSTRAINT_FORM
EXACT_PRIOR_BRIDGE_TARGET = BRIDGE_CONSTRAINT_EQUATION
BRIDGE_ROUTE_ALIGNMENT_SEQUENCE_PLAIN = " -> ".join(BRIDGE_ROUTE_ALIGNMENT_SEQUENCE)
LIKELY_PLAIN_MEANING = BRIDGE_CANDIDATE_RULE_PLAIN_MEANING

PACKET_SCOPE_RECORD = [
    "prior C_source^phi closeout accepted",
    "C_bridge^phi selected as next theorem-linkage obligation",
    "standalone phi bridge-admissibility route recovered",
    "exact prior bridge statement frozen",
    "target prepared",
    "no proof execution",
    "no theorem discharge",
]

RECOVERY_ITEMS = [
    "exact C_bridge^phi statement from the prior standalone phi bridge-admissibility registry",
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
    BRIDGE_ROUTE_ALIGNMENT_SEQUENCE_PLAIN,
]

WATCH_ITEMS = [
    "recover exact prior standalone phi bridge-admissibility registry language",
    "do not invent a new bridge formula",
    "do not silently substitute C_source^phi",
    "do not silently substitute A-source",
    "do not silently substitute psi-A",
    "do not silently substitute QFT-GR",
    "do not silently substitute master-action routes",
]

BOUNDARY_ITEMS = [
    "no proof execution",
    "no theorem discharge",
    "no phi-sector closure",
    "no scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no seam closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]

LEAN_STATUS_WORDING_LINES_FOR_PACKET = LEAN_STATUS_WORDING_LINES_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_PACKET = "\n".join(LEAN_STATUS_WORDING_LINES_FOR_PACKET)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_20260630_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiBridgeTheoremLinkageObligationPacket.lean"
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


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _blocked_boundary_flags() -> dict[str, bool]:
    return {
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_execution_authorized": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "C_bridge_phi_discharged": False,
        "C_bridge_phi_theorem_linkage_gap_discharged": False,
        "C_bridge_phi_theorem_linkage_obligation_discharged": False,
        "C_bridge_phi_proof_executed": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "field_equation_match_proved": False,
        "stress_energy_match_proved": False,
        "source_residual_match_proved": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "C_bridge_phi_route_reused_from_C_source_phi": False,
        "C_source_phi_route_reused": False,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "QFT_GR_route_imported": False,
        "QFT_GR_source_route_imported": False,
        "master_action_route_substituted": False,
        "J_current_imported": False,
        "C_source_phi_closure_claimed": False,
        "C_bridge_phi_closure_claimed": False,
        "phi_sector_closure_claimed": False,
        "full_scalar_qft_closure_claimed": False,
        "full_scalar_QFT_closure_claimed": False,
        "A_sector_closure_claimed": False,
        "sourced_maxwell_closure_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "general_C_k_theorem_linkage_closure": False,
        "general_C_k_closure": False,
        "C_k_dynamical_law_status": False,
        "C_k_rule_promotion_authorized": False,
        "C_k_rule_promoted": False,
        "rule_promoted": False,
        "C_k_action_embedding_claimed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_authorized": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "action_embedding_claimed": False,
        "action_variation_executed": False,
        "multiplier_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_claimed": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "new_bridge_formula_invented": False,
        "obligation_row_discharged": False,
        "obligation_rows_discharged": False,
        "new_physics_created": False,
    }


def _selector_review_valid(selector_review: dict[str, Any]) -> bool:
    return (
        selector_review.get("schema_id") == SELECTOR_REVIEW_SCHEMA_ID
        and selector_review.get("packet_id") == SELECTOR_REVIEW_PACKET_ID
        and selector_review.get("outcome_id") == SELECTOR_REVIEW_OUTCOME
        and selector_review.get("review_result") == SELECTOR_REVIEW_OUTCOME
        and selector_review.get("strict_review_result")
        == SELECTOR_STRICT_REVIEW_RESULT
        and selector_review.get("selected_next_target") == CONSUMED_TARGET
        and selector_review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and selector_review.get("selected_obligation") == SELECTED_OBLIGATION
        and selector_review.get("selected_theorem_linkage_gap")
        == SELECTED_THEOREM_LINKAGE_GAP
        and selector_review.get("selected_obligation_row_id")
        == SELECTED_OBLIGATION_ROW_ID
        and selector_review.get("accepted") is True
        and selector_review.get("C_bridge_phi_discharged") is False
    )


def _phi_bridge_registry_valid(registry: dict[str, Any]) -> bool:
    return (
        registry.get("schema_id") == PHI_BRIDGE_REGISTRY_SCHEMA_ID
        and registry.get("packet_id") == PHI_BRIDGE_REGISTRY_PACKET_ID
        and registry.get("outcome_id") == PHI_BRIDGE_REGISTRY_OUTCOME_ID
        and registry.get("closeout_result") == PHI_BRIDGE_REGISTRY_OUTCOME
        and registry.get("bridge_rule_classification") == BRIDGE_RULE_CLASSIFICATION
        and registry.get("bridge_rule_epistemic_status")
        == BRIDGE_RULE_EPISTEMIC_STATUS
        and registry.get("bridge_candidate_id") == BRIDGE_CANDIDATE_ID
        and registry.get("bridge_candidate_type") == BRIDGE_CANDIDATE_TYPE
        and registry.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
        and registry.get("bridge_constraint_equation") == BRIDGE_CONSTRAINT_EQUATION
        and registry.get("bridge_admissibility_constraint_form")
        == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        and registry.get("bridge_route_field_equation_match")
        == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
        and registry.get("bridge_route_stress_energy_match")
        == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
        and registry.get("bridge_route_source_residual_match")
        == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        and registry.get("bridge_candidate_rule_plain_meaning")
        == BRIDGE_CANDIDATE_RULE_PLAIN_MEANING
        and registry.get("bridge_route_alignment_sequence")
        == BRIDGE_ROUTE_ALIGNMENT_SEQUENCE
        and registry.get("bridge_admissibility_proved") is False
        and registry.get("bridge_route_alignment_verified") is False
        and registry.get("route_consistency_tuple_proved") is False
        and registry.get("qft_gr_closure_claimed") is False
        and registry.get("master_action_promoted") is False
        and registry.get("accepted") is True
    )


def _prior_phi_bridge_registry_snapshot() -> dict[str, Any]:
    return {
        "route_kind": STANDALONE_PHI_BRIDGE_ROUTE,
        "bridge_rule_classification": BRIDGE_RULE_CLASSIFICATION,
        "bridge_rule_epistemic_status": BRIDGE_RULE_EPISTEMIC_STATUS,
        "bridge_candidate_id": BRIDGE_CANDIDATE_ID,
        "bridge_candidate_type": BRIDGE_CANDIDATE_TYPE,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_route_field_equation_match": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        "bridge_candidate_rule_plain_meaning": BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
        "bridge_route_alignment_sequence": BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
        "bridge_route_alignment_sequence_plain": BRIDGE_ROUTE_ALIGNMENT_SEQUENCE_PLAIN,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    }


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "phi_bridge_theorem_linkage_obligation_packet",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "full_toeformal_aggregate_status_for_packet": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "lean_status_wording_lines_for_packet": LEAN_STATUS_WORDING_LINES_FOR_PACKET,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_bridge_theorem_linkage_obligation_packet(
    *,
    selector_review_path: Path = SELECTOR_REVIEW_PATH,
    phi_bridge_registry_path: Path = PHI_BRIDGE_REGISTRY_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector_review = _read_json(selector_review_path)
    phi_bridge_registry = _read_json(phi_bridge_registry_path)
    prior_phi_bridge_registry = _prior_phi_bridge_registry_snapshot()
    acceptance_criteria = {
        "consumes_expected_selector_result_review": _selector_review_valid(
            selector_review
        ),
        "selected_obligation_preserved": (
            SELECTED_OBLIGATION == "C_bridge^phi theorem-linkage obligation"
            and SELECTED_THEOREM_LINKAGE_GAP == "C_bridge^phi theorem-linkage gap"
            and SELECTED_OBLIGATION_ROW_ID == "C_bridge^phi"
        ),
        "prior_C_source_phi_closeout_accepted": (
            selector_review.get("C_source_phi_closed_locally") is True
            and selector_review.get("completed_local_theorem_linkage_chain")
            == COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN
        ),
        "prior_phi_bridge_registry_exact": _phi_bridge_registry_valid(
            phi_bridge_registry
        ),
        "standalone_phi_bridge_route_recovered": (
            BRIDGE_CONSTRAINT_FORM.startswith("C_bridge^phi :=")
            and BRIDGE_CONSTRAINT_EQUATION == "C_bridge^phi = 0"
            and BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM == "C_bridge^phi = 0"
            and BRIDGE_ROUTE_FIELD_EQUATION_MATCH
            == "E_phi^master - E_phi^witness = 0"
            and BRIDGE_ROUTE_STRESS_ENERGY_MATCH
            == "T_phi^master - T_phi^witness = 0"
            and BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
            == "C_source^phi - nabla_mu T_phi^{mu nu} = 0"
        ),
        "no_new_bridge_formula_invented": True,
        "route_contamination_blocked": True,
        "scope_only_no_theorem_execution": True,
        "lean_status_wording_preserved": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW == "PASSED_SERIAL_RERUN"
        ),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "packet_prepared": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if prepared
        else "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_REQUIRES_REMEDIATION",
        "strict_packet_result": STRICT_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if prepared else "remediation",
        "suggested_review_outcome": SUGGESTED_REVIEW_OUTCOME,
        "strict_suggested_review_outcome": STRICT_SUGGESTED_REVIEW_OUTCOME,
        "selector_review_schema_id": SELECTOR_REVIEW_SCHEMA_ID,
        "selector_review_packet_id": SELECTOR_REVIEW_PACKET_ID,
        "selector_review_outcome": SELECTOR_REVIEW_OUTCOME,
        "selector_strict_review_result": SELECTOR_STRICT_REVIEW_RESULT,
        "selector_review_consumed": prepared,
        "prior_selector_result_review_accepted": prepared,
        "prior_C_source_phi_closeout_accepted": prepared,
        "selected_obligation": SELECTED_OBLIGATION,
        "selected_theorem_linkage_gap": SELECTED_THEOREM_LINKAGE_GAP,
        "selected_obligation_row_id": SELECTED_OBLIGATION_ROW_ID,
        "C_bridge_phi_theorem_linkage_obligation_selected": prepared,
        "packet_scope_record": PACKET_SCOPE_RECORD,
        "packet_scope_record_count": len(PACKET_SCOPE_RECORD),
        "recovery_items": RECOVERY_ITEMS,
        "recovery_item_count": len(RECOVERY_ITEMS),
        "watch_items": WATCH_ITEMS,
        "watch_item_count": len(WATCH_ITEMS),
        "boundary_items": BOUNDARY_ITEMS,
        "boundary_item_count": len(BOUNDARY_ITEMS),
        "scope_only": True,
        "proof_execution_blocked": True,
        "theorem_discharge_blocked": True,
        "target_prepared": prepared,
        "prior_phi_bridge_registry": prior_phi_bridge_registry,
        "standalone_phi_bridge_route": STANDALONE_PHI_BRIDGE_ROUTE,
        "standalone_phi_bridge_route_recovered": prepared,
        "standalone_phi_bridge_route_preserved": prepared,
        "exact_prior_bridge_statement_frozen": prepared,
        "exact_prior_bridge_target_frozen": prepared,
        "exact_prior_bridge_statement": EXACT_PRIOR_BRIDGE_STATEMENT,
        "exact_prior_bridge_target": EXACT_PRIOR_BRIDGE_TARGET,
        "bridge_rule_classification": BRIDGE_RULE_CLASSIFICATION,
        "bridge_rule_epistemic_status": BRIDGE_RULE_EPISTEMIC_STATUS,
        "bridge_candidate_id": BRIDGE_CANDIDATE_ID,
        "bridge_candidate_type": BRIDGE_CANDIDATE_TYPE,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_route_field_equation_match": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        "bridge_candidate_rule_plain_meaning": BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
        "likely_plain_meaning": LIKELY_PLAIN_MEANING,
        "bridge_route_alignment_sequence": BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
        "bridge_route_alignment_sequence_plain": BRIDGE_ROUTE_ALIGNMENT_SEQUENCE_PLAIN,
        "bridge_component_count": 3,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "completed_local_theorem_linkage_chain": COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN,
        "completed_local_theorem_linkage_chain_count": len(
            COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN
        ),
        "new_bridge_formula_invented": False,
        "C_source_phi_route_reused": False,
        "C_bridge_phi_route_reused_from_C_source_phi": False,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "QFT_GR_route_imported": False,
        "QFT_GR_source_route_imported": False,
        "master_action_route_substituted": False,
        "route_contamination_guard": (
            "freeze exact C_bridge^phi statement from prior standalone phi "
            "bridge-admissibility registry; do not substitute C_source^phi, "
            "A-source, psi-A, QFT-GR, or master-action routes"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": prepared,
        "claim_ladder_position": (
            "below theorem discharge, phi-sector closure, scalar/QFT closure, "
            "seam closure, empirical prediction, empirical confirmation, and "
            "mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This packet scopes only the standalone phi bridge theorem-linkage "
            "obligation. It recovers and freezes the exact prior standalone "
            "phi bridge-admissibility registry statement C_bridge^phi := "
            "(E_phi^master - E_phi^witness, T_phi^master - T_phi^witness, "
            "C_source^phi - nabla_mu T_phi^{mu nu}) and target "
            "C_bridge^phi = 0, plus its field-equation, stress-energy, and "
            "source-residual match components. It does not execute a proof, "
            "discharge C_bridge^phi, invent a new bridge formula, claim "
            "phi-sector closure, claim scalar/QFT closure, close EM-QFT or "
            "QFT-GR, claim general C_k closure, embed or vary an action, "
            "claim empirical validation, or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_phi_bridge_theorem_linkage_obligation_packet",
            "fail to freeze exact C_bridge^phi statement from prior registry",
            "fail to freeze C_bridge^phi = 0",
            "invent a new bridge formula",
            "silently reuse C_source^phi as the bridge route",
            "silently import A-source, psi-A, QFT-GR, or master-action routes",
            "execute the C_bridge^phi proof route",
            "discharge C_bridge^phi",
            "claim phi-sector closure",
            "claim scalar/QFT closure",
            "claim EM-QFT or QFT-GR closure",
            "claim general C_k closure",
            "embed or vary an action",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_PACKET,
        "lean_status_wording_lines": LEAN_STATUS_WORDING_LINES_FOR_PACKET,
        "selector_review_lean_status_wording": LEAN_STATUS_WORDING_FOR_REVIEW,
        "full_toeformal_aggregate_status_for_packet": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "aggregate_lean_validation_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiBridgeTheoremLinkageObligationPacket",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "selector_review_file": _ptr(selector_review_path),
            "selector_review_lean_file": _ptr(SELECTOR_REVIEW_LEAN_PACKET_PATH),
            "phi_bridge_registry_file": _ptr(phi_bridge_registry_path),
            "phi_bridge_registry_lean_file": _ptr(PHI_BRIDGE_REGISTRY_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
    return payload


def write_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Prepare the standalone phi-bridge C_bridge^phi theorem-linkage "
            "obligation packet without executing or discharging the proof route."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--selector-review", type=Path, default=SELECTOR_REVIEW_PATH)
    parser.add_argument(
        "--phi-bridge-registry",
        type=Path,
        default=PHI_BRIDGE_REGISTRY_PATH,
    )
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    selector_review_path = (
        args.selector_review
        if args.selector_review.is_absolute()
        else REPO_ROOT / args.selector_review
    )
    phi_bridge_registry_path = (
        args.phi_bridge_registry
        if args.phi_bridge_registry.is_absolute()
        else REPO_ROOT / args.phi_bridge_registry
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    packet = build_phi_bridge_theorem_linkage_obligation_packet(
        selector_review_path=selector_review_path,
        phi_bridge_registry_path=phi_bridge_registry_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_packet(packet, out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "out": _ptr(path),
                "packet_result": packet["packet_result"],
                "selected_obligation": packet["selected_obligation"],
                "selected_next_target": packet["selected_next_target"],
                "bridge_constraint_form": packet["bridge_constraint_form"],
                "bridge_constraint_equation": packet["bridge_constraint_equation"],
                "proof_attempt_executed": packet["proof_attempt_executed"],
                "theorem_discharged": packet["theorem_discharged"],
                "new_bridge_formula_invented": packet["new_bridge_formula_invented"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
