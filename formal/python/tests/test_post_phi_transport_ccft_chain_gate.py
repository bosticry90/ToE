from __future__ import annotations

import json
import importlib
from pathlib import Path
from typing import Any

import pytest

from formal.python.tests.strict_physics_state_helpers import (
    README_PATH,
    ROADMAP_PATH,
    STATE_PATH,
    STRICT_MAP_PATH,
    CURRENT_AUTHORITATIVE_SURFACES_PATH,
    REPO_ROOT,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
    loop_registry,
    read_text,
    workstream,
)
from formal.python.tools.post_phi_transport_ccft_chain_reports import (
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_STATUS_WORDING,
    LEAN_STATUS_WORDING_LINES,
    LOCAL_PHI_THEOREM_LINKAGE_TRIAD_LABEL,
    LOCAL_PHI_TRIAD_EQUATIONS,
    ORDERED_STAGE_KEYS,
    SCOPED_LEAN_TARGETS_STATUS,
    STAGES,
    build_stage_payload,
    lean_path,
    release_path,
)


FINAL_LIVE_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_resolution_priority_selection_packet"
)
FINAL_PREVIOUS_TARGET = (
    "review_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_resolution_strategy_packet_result"
)
BASELINE_CONSTRUCTION_OBLIGATION_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_construction_obligation_packet"
)
BASELINE_CONSTRUCTION_OBLIGATION_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_baseline_construction_obligation_packet_result"
)
BASELINE_COMPONENT_EQUATION_SCAFFOLD_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_component_equation_scaffold_packet"
)
BASELINE_COMPONENT_EQUATION_SCAFFOLD_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_baseline_component_equation_scaffold_packet_result"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_component_equation_source_classification_packet"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_baseline_component_equation_source_classification_packet_result"
)
BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_component_equation_source_validation_criteria_packet"
)
BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_baseline_component_equation_source_validation_criteria_packet_result"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_component_equation_source_candidate_registry_packet"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_baseline_component_equation_source_candidate_registry_packet_result"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_review_packet"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_review_packet_result"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_classification_packet"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_classification_packet_result"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_resolution_strategy_packet"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_REVIEW_TARGET = (
    FINAL_PREVIOUS_TARGET
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_PRIORITY_SELECTION_TARGET = (
    FINAL_LIVE_TARGET
)
BASELINE_COMPONENT_INTERACTION_RISK_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_component_interaction_risk_packet"
)
BASELINE_COMPONENT_INTERACTION_RISK_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_baseline_component_interaction_risk_packet_result"
)
MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet_result"
)
MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorMeasurementFeedbackBaselinePressurePacketResultReview.lean"
)
MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_"
    "BASELINE_PRESSURE_PACKET_RESULT_REVIEW_20260703_v0.json"
)
MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet"
)
MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorMeasurementFeedbackBaselinePressurePacket.lean"
)
MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_"
    "BASELINE_PRESSURE_PACKET_20260703_v0.json"
)
MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_KIND = (
    "selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet_result_review"
)
BASELINE_COMPONENT_REGISTRY_PACKET_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentRegistryPacket.lean"
)
BASELINE_COMPONENT_REGISTRY_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_component_registry_packet"
)
BASELINE_COMPONENT_REGISTRY_PACKET_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_"
    "PACKET_20260703_v0.json"
)
BASELINE_COMPONENT_REGISTRY_PACKET_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_registry_packet"
)
BASELINE_COMPONENT_REGISTRY_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_registry_packet_"
    "result_review"
)
BASELINE_COMPONENT_REGISTRY_REVIEW_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentRegistryPacketResultReview.lean"
)
BASELINE_COMPONENT_REGISTRY_REVIEW_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_"
    "PACKET_RESULT_REVIEW_20260703_v0.json"
)
BASELINE_COMPONENT_REGISTRY_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_baseline_component_registry_packet_result"
)
BASELINE_COMPONENT_INTERACTION_RISK_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_interaction_"
    "risk_packet"
)
BASELINE_COMPONENT_INTERACTION_RISK_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_interaction_"
    "risk_packet_result_review"
)
BASELINE_CONSTRUCTION_OBLIGATION_KIND = (
    "selected_ccft_empirical_discriminator_baseline_construction_obligation_packet"
)
BASELINE_CONSTRUCTION_OBLIGATION_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_baseline_construction_obligation_"
    "packet_result_review"
)
BASELINE_COMPONENT_EQUATION_SCAFFOLD_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "scaffold_packet"
)
BASELINE_COMPONENT_EQUATION_SCAFFOLD_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "scaffold_packet_result_review"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "source_classification_packet"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "source_classification_packet_result_review"
)
BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "source_validation_criteria_packet"
)
BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "source_validation_criteria_packet_result_review"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "source_candidate_registry_packet"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "source_candidate_registry_packet_result_review"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "source_applicability_review_packet"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "source_applicability_review_packet_result_review"
)
BASELINE_COMPONENT_EQUATION_SCAFFOLD_PACKET_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationScaffoldPacket.lean"
)
BASELINE_COMPONENT_EQUATION_SCAFFOLD_PACKET_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_"
    "SCAFFOLD_PACKET_20260705_v0.json"
)
BASELINE_COMPONENT_EQUATION_SCAFFOLD_PACKET_OUTCOME = (
    STAGES["baseline_component_equation_scaffold_packet"].outcome_id
)
BASELINE_COMPONENT_EQUATION_SCAFFOLD_PACKET_STRICT_OUTCOME = (
    STAGES["baseline_component_equation_scaffold_packet"].strict_outcome_id
)
BASELINE_COMPONENT_INTERACTION_RISK_PACKET_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentInteractionRiskPacket.lean"
)
BASELINE_COMPONENT_INTERACTION_RISK_PACKET_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_INTERACTION_"
    "RISK_PACKET_20260703_v0.json"
)
BASELINE_COMPONENT_INTERACTION_RISK_REVIEW_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentInteractionRiskPacketResultReview.lean"
)
BASELINE_COMPONENT_INTERACTION_RISK_REVIEW_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_INTERACTION_"
    "RISK_PACKET_RESULT_REVIEW_20260703_v0.json"
)
RESIDUAL_FORMULA_SELECTION_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_residual_formula_selection_packet_result"
)
RESIDUAL_FORMULA_SELECTION_REVIEW_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorResidualFormulaSelectionPacketResultReview.lean"
)
RESIDUAL_FORMULA_SELECTION_REVIEW_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_"
    "PACKET_RESULT_REVIEW_20260703_v0.json"
)
RESIDUAL_FORMULA_SELECTION_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet"
)
RESIDUAL_FORMULA_SELECTION_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_residual_formula_selection_packet"
)
OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_observable_definition_semantics_packet_result"
)
OBSERVABLE_DEFINITION_SEMANTICS_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_observable_definition_semantics_packet"
)
BASELINE_SEMANTICS_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_result"
)
BASELINE_SEMANTICS_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet"
)
TOLERANCE_REGISTRY_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_tolerance_registry_packet_result"
)
TOLERANCE_REGISTRY_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_tolerance_registry_packet"
)
SELECTED_CANDIDATE_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_candidate_packet_result"
)
SELECTED_CANDIDATE_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_candidate_packet"
)
PRIORITY_PACKET_TARGET = (
    "prepare_ccft_empirical_discriminator_candidate_priority_selection_packet"
)
PRIORITY_REVIEW_TARGET = (
    "review_ccft_empirical_discriminator_candidate_priority_selection_packet_result"
)
EMPIRICAL_PACKET_TARGET = "prepare_ccft_empirical_discriminator_candidate_map_packet"
EMPIRICAL_REVIEW_TARGET = "review_ccft_empirical_discriminator_candidate_map_packet_result"
VARIATIONAL_PACKET_TARGET = "prepare_ccft_full_variational_action_program_packet"
VARIATIONAL_REVIEW_TARGET = "review_ccft_full_variational_action_program_packet_result"
BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_PACKET_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceClassificationPacket.lean"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_PACKET_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_"
    "SOURCE_CLASSIFICATION_PACKET_20260705_v0.json"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_PACKET_OUTCOME = (
    STAGES["baseline_component_equation_source_classification_packet"].outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_PACKET_STRICT_OUTCOME = (
    STAGES["baseline_component_equation_source_classification_packet"].strict_outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceClassificationPacketResultReview.lean"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_"
    "SOURCE_CLASSIFICATION_PACKET_RESULT_REVIEW_20260705_v0.json"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_OUTCOME = (
    STAGES["baseline_component_equation_source_classification_review"].outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_STRICT_OUTCOME = (
    STAGES["baseline_component_equation_source_classification_review"].strict_outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_PACKET_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceValidationCriteriaPacket.lean"
)
BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_PACKET_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_"
    "SOURCE_VALIDATION_CRITERIA_PACKET_20260705_v0.json"
)
BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_PACKET_OUTCOME = (
    STAGES["baseline_component_equation_source_validation_criteria_packet"].outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_PACKET_STRICT_OUTCOME = (
    STAGES["baseline_component_equation_source_validation_criteria_packet"].strict_outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceValidationCriteriaPacketResultReview.lean"
)
BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_"
    "SOURCE_VALIDATION_CRITERIA_PACKET_RESULT_REVIEW_20260705_v0.json"
)
BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_OUTCOME = (
    STAGES["baseline_component_equation_source_validation_criteria_review"].outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_STRICT_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_validation_criteria_review"
    ].strict_outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_PACKET_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceCandidateRegistryPacket.lean"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_PACKET_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_"
    "SOURCE_CANDIDATE_REGISTRY_PACKET_20260705_v0.json"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_PACKET_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_candidate_registry_packet"
    ].outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_PACKET_STRICT_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_candidate_registry_packet"
    ].strict_outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceCandidateRegistryPacketResultReview.lean"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_"
    "SOURCE_CANDIDATE_REGISTRY_PACKET_RESULT_REVIEW_20260705_v0.json"
)
BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_candidate_registry_review"
    ].outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_STRICT_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_candidate_registry_review"
    ].strict_outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_PACKET_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceApplicabilityGapClassificationPacket.lean"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_PACKET_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_"
    "SOURCE_APPLICABILITY_GAP_CLASSIFICATION_PACKET_20260705_v0.json"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_PACKET_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_applicability_gap_classification_packet"
    ].outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_PACKET_STRICT_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_applicability_gap_classification_packet"
    ].strict_outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceApplicabilityGapClassificationPacketResultReview.lean"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_"
    "SOURCE_APPLICABILITY_GAP_CLASSIFICATION_PACKET_RESULT_REVIEW_20260705_v0.json"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_applicability_gap_classification_review"
    ].outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_STRICT_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_applicability_gap_classification_review"
    ].strict_outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_PACKET_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceApplicabilityGapResolutionStrategyPacket.lean"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_PACKET_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_"
    "SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_PACKET_20260705_v0.json"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_PACKET_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_applicability_gap_resolution_strategy_packet"
    ].outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_PACKET_STRICT_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_applicability_gap_resolution_strategy_packet"
    ].strict_outcome_id
)
FINAL_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceApplicabilityGapResolutionStrategyPacketResultReview.lean"
)
FINAL_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_"
    "SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_PACKET_RESULT_REVIEW_20260705_v0.json"
)
FINAL_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_applicability_gap_resolution_strategy_review"
    ].outcome_id
)
FINAL_STRICT_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_applicability_gap_resolution_strategy_review"
    ].strict_outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceApplicabilityReviewPacket.lean"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_"
    "SOURCE_APPLICABILITY_REVIEW_PACKET_20260705_v0.json"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_applicability_review_packet"
    ].outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_STRICT_OUTCOME = (
    STAGES[
        "baseline_component_equation_source_applicability_review_packet"
    ].strict_outcome_id
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "source_applicability_gap_classification_packet"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "source_applicability_gap_classification_packet_result_review"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "source_applicability_gap_resolution_strategy_packet"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "source_applicability_gap_resolution_strategy_packet_result_review"
)
BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_PRIORITY_SELECTION_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_equation_"
    "source_applicability_gap_resolution_priority_selection_packet"
)
FINAL_KIND = (
    BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_PRIORITY_SELECTION_KIND
)
NEXT_PACKET_OUTCOME = (
    "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_PREPARED_LAGRANGIAN_"
    "HAMILTONIAN_SOURCE_AND_TRANSPORT_TARGETS_NO_ACTION_EMBEDDING_OR_"
    "MASTER_ACTION_PROMOTION"
)
NEXT_PACKET_STRICT_OUTCOME = (
    "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_PREPARED_AS_REQUIRED_PRE_"
    "DERIVATION_PLAN_NO_CK_VARIATION_OR_CCFT_VALIDATION"
)
LOCAL_PHI_TRIAD_REGISTRY_TEXT = "; ".join(LOCAL_PHI_TRIAD_EQUATIONS)

PUBLIC_SURFACES = (
    README_PATH,
    STATE_PATH,
    ROADMAP_PATH,
    STRICT_MAP_PATH,
    CURRENT_AUTHORITATIVE_SURFACES_PATH,
)

WRAPPER_BY_STAGE = {
    "selector": (
        "formal/python/tools/"
        "ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
        "closeout_report.py"
    ),
    "selector_review": (
        "formal/python/tools/"
        "ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
        "closeout_result_review_report.py"
    ),
    "triad_packet": (
        "formal/python/tools/"
        "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
        "packet_report.py"
    ),
    "triad_review": (
        "formal/python/tools/"
        "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
        "result_review_report.py"
    ),
    "roadmap_packet": (
        "formal/python/tools/coherence_admissibility_bridge_roadmap_rebase_"
        "packet_report.py"
    ),
    "roadmap_review": (
        "formal/python/tools/coherence_admissibility_bridge_roadmap_rebase_"
        "result_review_report.py"
    ),
    "crosswalk_packet": (
        "formal/python/tools/ccft_to_toe_object_crosswalk_packet_report.py"
    ),
    "ck_index_packet": (
        "formal/python/tools/ccft_ck_admissibility_obligation_index_packet_report.py"
    ),
    "ck_index_review": (
        "formal/python/tools/"
        "ccft_ck_admissibility_obligation_index_packet_result_review_report.py"
    ),
    "variational_packet": (
        "formal/python/tools/ccft_full_variational_action_program_packet_report.py"
    ),
    "variational_review": (
        "formal/python/tools/"
        "ccft_full_variational_action_program_packet_result_review_report.py"
    ),
    "empirical_packet": (
        "formal/python/tools/"
        "ccft_empirical_discriminator_candidate_map_packet_report.py"
    ),
    "empirical_review": (
        "formal/python/tools/"
        "ccft_empirical_discriminator_candidate_map_packet_result_review_report.py"
    ),
    "priority_packet": (
        "formal/python/tools/"
        "ccft_empirical_discriminator_candidate_priority_selection_packet_report.py"
    ),
    "priority_review": (
        "formal/python/tools/"
        "ccft_empirical_discriminator_candidate_priority_selection_packet_result_review_report.py"
    ),
    "selected_candidate_packet": (
        "formal/python/tools/selected_ccft_empirical_discriminator_candidate_packet_report.py"
    ),
    "selected_candidate_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_candidate_packet_result_review_report.py"
    ),
    "tolerance_registry_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_tolerance_registry_packet_report.py"
    ),
    "tolerance_registry_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_tolerance_registry_packet_result_review_report.py"
    ),
    "baseline_semantics_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_report.py"
    ),
    "baseline_semantics_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_result_review_report.py"
    ),
    "observable_definition_semantics_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_observable_definition_semantics_packet_report.py"
    ),
    "observable_definition_semantics_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_observable_definition_semantics_packet_result_review_report.py"
    ),
    "residual_formula_selection_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_residual_formula_selection_packet_report.py"
    ),
    "residual_formula_selection_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_residual_formula_selection_packet_result_review_report.py"
    ),
    "measurement_feedback_baseline_pressure_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet_report.py"
    ),
    "measurement_feedback_baseline_pressure_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet_result_review_report.py"
    ),
    "baseline_component_registry_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_registry_packet_report.py"
    ),
    "baseline_component_registry_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_registry_packet_result_review_report.py"
    ),
    "baseline_component_interaction_risk_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_interaction_risk_packet_report.py"
    ),
    "baseline_component_interaction_risk_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_interaction_risk_packet_result_review_report.py"
    ),
    "baseline_construction_obligation_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_construction_obligation_packet_report.py"
    ),
    "baseline_construction_obligation_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_construction_obligation_packet_result_review_report.py"
    ),
    "baseline_component_equation_scaffold_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_scaffold_packet_report.py"
    ),
    "baseline_component_equation_scaffold_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_scaffold_packet_result_review_report.py"
    ),
    "baseline_component_equation_source_classification_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_classification_packet_report.py"
    ),
    "baseline_component_equation_source_classification_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_classification_packet_result_review_report.py"
    ),
    "baseline_component_equation_source_validation_criteria_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_validation_criteria_packet_report.py"
    ),
    "baseline_component_equation_source_validation_criteria_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_validation_criteria_packet_result_review_report.py"
    ),
    "baseline_component_equation_source_candidate_registry_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_candidate_registry_packet_report.py"
    ),
    "baseline_component_equation_source_candidate_registry_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_candidate_registry_packet_result_review_report.py"
    ),
    "baseline_component_equation_source_applicability_review_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_review_packet_report.py"
    ),
    "baseline_component_equation_source_applicability_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_review_packet_result_review_report.py"
    ),
    "baseline_component_equation_source_applicability_gap_classification_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_classification_packet_report.py"
    ),
    "baseline_component_equation_source_applicability_gap_classification_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_classification_packet_result_review_report.py"
    ),
    "baseline_component_equation_source_applicability_gap_resolution_strategy_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_resolution_strategy_packet_report.py"
    ),
    "baseline_component_equation_source_applicability_gap_resolution_strategy_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_resolution_strategy_packet_result_review_report.py"
    ),
}

WRAPPER_BUILD_FUNCTION_BY_STAGE = {
    "selector": (
        "formal.python.tools."
        "ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
        "closeout_report",
        "build_ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
        "closeout",
    ),
    "selector_review": (
        "formal.python.tools."
        "ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
        "closeout_result_review_report",
        "build_ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
        "closeout_result_review",
    ),
    "triad_packet": (
        "formal.python.tools."
        "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
        "packet_report",
        "build_phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
        "packet",
    ),
    "triad_review": (
        "formal.python.tools."
        "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
        "result_review_report",
        "build_phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
        "result_review",
    ),
    "roadmap_packet": (
        "formal.python.tools.coherence_admissibility_bridge_roadmap_rebase_"
        "packet_report",
        "build_coherence_admissibility_bridge_roadmap_rebase_packet",
    ),
    "roadmap_review": (
        "formal.python.tools.coherence_admissibility_bridge_roadmap_rebase_"
        "result_review_report",
        "build_coherence_admissibility_bridge_roadmap_rebase_result_review",
    ),
    "crosswalk_packet": (
        "formal.python.tools.ccft_to_toe_object_crosswalk_packet_report",
        "build_ccft_to_toe_object_crosswalk_packet",
    ),
    "ck_index_packet": (
        "formal.python.tools.ccft_ck_admissibility_obligation_index_packet_report",
        "build_ccft_ck_admissibility_obligation_index_packet",
    ),
    "ck_index_review": (
        "formal.python.tools."
        "ccft_ck_admissibility_obligation_index_packet_result_review_report",
        "build_ccft_ck_admissibility_obligation_index_packet_result_review",
    ),
    "variational_packet": (
        "formal.python.tools.ccft_full_variational_action_program_packet_report",
        "build_ccft_full_variational_action_program_packet",
    ),
    "variational_review": (
        "formal.python.tools."
        "ccft_full_variational_action_program_packet_result_review_report",
        "build_ccft_full_variational_action_program_packet_result_review",
    ),
    "empirical_packet": (
        "formal.python.tools.ccft_empirical_discriminator_candidate_map_packet_report",
        "build_ccft_empirical_discriminator_candidate_map_packet",
    ),
    "empirical_review": (
        "formal.python.tools."
        "ccft_empirical_discriminator_candidate_map_packet_result_review_report",
        "build_ccft_empirical_discriminator_candidate_map_packet_result_review",
    ),
    "priority_packet": (
        "formal.python.tools."
        "ccft_empirical_discriminator_candidate_priority_selection_packet_report",
        "build_ccft_empirical_discriminator_candidate_priority_selection_packet",
    ),
    "priority_review": (
        "formal.python.tools."
        "ccft_empirical_discriminator_candidate_priority_selection_packet_result_review_report",
        "build_ccft_empirical_discriminator_candidate_priority_selection_packet_result_review",
    ),
    "selected_candidate_packet": (
        "formal.python.tools.selected_ccft_empirical_discriminator_candidate_packet_report",
        "build_selected_ccft_empirical_discriminator_candidate_packet",
    ),
    "selected_candidate_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_candidate_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_candidate_packet_result_review",
    ),
    "tolerance_registry_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_tolerance_registry_packet_report",
        "build_selected_ccft_empirical_discriminator_tolerance_registry_packet",
    ),
    "tolerance_registry_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_tolerance_registry_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_tolerance_registry_packet_result_review",
    ),
    "baseline_semantics_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_report",
        "build_selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet",
    ),
    "baseline_semantics_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_result_review",
    ),
    "observable_definition_semantics_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_observable_definition_semantics_packet_report",
        "build_selected_ccft_empirical_discriminator_observable_definition_semantics_packet",
    ),
    "observable_definition_semantics_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_observable_definition_semantics_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_observable_definition_semantics_packet_result_review",
    ),
    "residual_formula_selection_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_residual_formula_selection_packet_report",
        "build_selected_ccft_empirical_discriminator_residual_formula_selection_packet",
    ),
    "residual_formula_selection_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_residual_formula_selection_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_residual_formula_selection_packet_result_review",
    ),
    "measurement_feedback_baseline_pressure_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet_report",
        "build_selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet",
    ),
    "measurement_feedback_baseline_pressure_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet_result_review",
    ),
    "baseline_component_registry_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_registry_packet_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_registry_packet",
    ),
    "baseline_component_registry_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_registry_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_registry_packet_result_review",
    ),
    "baseline_component_interaction_risk_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_interaction_risk_packet_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_interaction_risk_packet",
    ),
    "baseline_component_interaction_risk_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_interaction_risk_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_interaction_risk_packet_result_review",
    ),
    "baseline_construction_obligation_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_construction_obligation_packet_report",
        "build_selected_ccft_empirical_discriminator_baseline_construction_obligation_packet",
    ),
    "baseline_construction_obligation_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_construction_obligation_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_baseline_construction_obligation_packet_result_review",
    ),
    "baseline_component_equation_scaffold_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_scaffold_packet_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_scaffold_packet",
    ),
    "baseline_component_equation_scaffold_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_scaffold_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_scaffold_packet_result_review",
    ),
    "baseline_component_equation_source_classification_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_classification_packet_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_source_classification_packet",
    ),
    "baseline_component_equation_source_classification_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_classification_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_source_classification_packet_result_review",
    ),
    "baseline_component_equation_source_validation_criteria_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_validation_criteria_packet_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_source_validation_criteria_packet",
    ),
    "baseline_component_equation_source_validation_criteria_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_validation_criteria_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_source_validation_criteria_packet_result_review",
    ),
    "baseline_component_equation_source_candidate_registry_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_candidate_registry_packet_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_source_candidate_registry_packet",
    ),
    "baseline_component_equation_source_candidate_registry_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_candidate_registry_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_source_candidate_registry_packet_result_review",
    ),
    "baseline_component_equation_source_applicability_review_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_review_packet_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_review_packet",
    ),
    "baseline_component_equation_source_applicability_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_review_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_review_packet_result_review",
    ),
    "baseline_component_equation_source_applicability_gap_classification_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_classification_packet_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_classification_packet",
    ),
    "baseline_component_equation_source_applicability_gap_classification_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_classification_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_classification_packet_result_review",
    ),
    "baseline_component_equation_source_applicability_gap_resolution_strategy_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_resolution_strategy_packet_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_resolution_strategy_packet",
    ),
    "baseline_component_equation_source_applicability_gap_resolution_strategy_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_resolution_strategy_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_resolution_strategy_packet_result_review",
    ),
}

PAPER_DOCS = (
    "formal/docs/paper/TOE_COHERENCE_ADMISSIBILITY_BRIDGE_HYPOTHESIS_v0.md",
    "formal/docs/paper/TOE_COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_v1.md",
    "formal/docs/paper/CCFT_TO_TOE_OBJECT_CROSSWALK_v0.md",
    "formal/docs/paper/CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0.md",
    "formal/docs/paper/CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0.md",
    "formal/docs/paper/CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0.md",
    "formal/docs/paper/CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_v0.md",
    "formal/docs/paper/CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_INTERACTION_RISK_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_INTERACTION_RISK_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_CONSTRUCTION_OBLIGATION_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_CONSTRUCTION_OBLIGATION_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SCAFFOLD_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SCAFFOLD_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_PACKET_RESULT_REVIEW_v0.md",
)

JSON_FALSE_FLAGS = (
    "proof_execution_authorized",
    "proof_attempt_executed",
    "theorem_discharged",
    "new_theorem_discharge",
    "theorem_linkage_obligation_discharged",
    "gap_discharged",
    "any_gap_discharged",
    "any_gap_closed",
    "phi_sector_closure_claimed",
    "full_scalar_qft_closure_claimed",
    "full_scalar_QFT_closure_claimed",
    "qft_gr_closure_claimed",
    "em_qft_closure_claimed",
    "gr_qm_closure_claimed",
    "sr_cosmo_closure_claimed",
    "qm_stat_closure_claimed",
    "pillar_closure_claim",
    "seam_closure_claim",
    "general_C_k_closure",
    "general_C_k_theorem_linkage_closure",
    "C_k_rule_promoted",
    "rule_promoted",
    "C_k_action_embedding_claimed",
    "C_k_action_variation_executed",
    "action_embedding_claimed",
    "action_variation_executed",
    "empirical_prediction_claimed",
    "empirical_validation_claimed",
    "CCFT_validated",
    "CCFT_fundamental_physics_claimed",
    "CCFT_derivation_from_master_action_claimed",
    "master_action_promoted",
    "master_action_promotion_authorized",
    "historical_20260619_rule_family_artifacts_overwritten",
    "new_triad_called_rule_family_closeout",
    "full_toeformal_aggregate_passed",
    "full_toeformal_aggregate_failed",
    "full_toeformal_aggregate_timed_out",
)


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(read_text(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _assert_registry_nonclaims(row: dict[str, Any]) -> None:
    for flag in JSON_FALSE_FLAGS:
        assert row[flag] == "no", flag


def _assert_gap_resolution_strategy_review_acceptance(row: dict[str, Any]) -> None:
    assert (
        row[
            "baseline_component_equation_source_applicability_gap_resolution_strategy_packet_result_review_consumed"
        ]
        == "yes"
    )
    assert (
        row["baseline_component_equation_source_applicability_gap_resolution_strategy_packet_accepted"]
        == "yes"
    )
    assert row["source_applicability_gap_resolution_strategy_packet_accepted"] == "yes"
    assert row["source_applicability_gap_resolution_strategy_accepted_only"] == "yes"
    assert row["source_applicability_gap_resolution_paths_accepted_only"] == "yes"
    assert (
        row["source_applicability_gap_resolution_strategy_rows_accepted_as_future_paths_only"]
        == "yes"
    )
    assert row["strategy_rows_accepted_as_not_executed"] == "yes"
    assert row["accepted_source_applicability_gap_resolution_strategy_field_count"] == 9
    assert row["accepted_source_applicability_gap_resolution_strategy_row_count"] == 8
    assert row["accepted_source_applicability_gap_resolution_strategy_path_count"] == 8
    assert row["accepted_strategy_path_clarification_needed_count"] == 3
    assert (
        row["accepted_strategy_path_standard_theory_import_work_needed_count"]
        == 3
    )
    assert row["accepted_strategy_path_literature_review_needed_count"] == 3
    assert row["accepted_strategy_path_source_replacement_if_needed_count"] == 3
    assert row["accepted_strategy_path_empirical_fit_design_needed_count"] == 2
    assert row["accepted_strategy_row_applicability_candidate_unclear_count"] == 3
    assert row["accepted_strategy_row_applicability_candidate_blocked_count"] == 5
    assert row["accepted_strategy_row_applicability_candidate_supported_count"] == 0
    assert (
        row["accepted_strategy_row_applicability_candidate_rejected_for_slot_count"]
        == 0
    )
    assert row["strategy_rows_executed_count"] == 0
    assert row["gap_resolution_priority_selection_packet_selected"] == "yes"
    assert (
        row["gap_resolution_priority_selection_required_before_source_validation"]
        == "yes"
    )
    assert row["gap_resolution_priority_selection_required_before_equation_import"] == "yes"
    assert row["gap_resolution_priority_selection_required_before_empirical_fit"] == "yes"
    assert row["gap_resolution_priority_selection_executed"] == "no"
    assert row["gap_resolution_priority_selected"] == "no"
    assert row["first_gap_resolution_candidate_selected"] == "no"
    assert row["source_remediation_execution_authorized"] == "no"
    assert row["source_replacement_execution_authorized"] == "no"
    assert row["source_validation_execution_authorized"] == "no"
    assert row["source_validated"] == "no"
    assert row["source_validation_executed"] == "no"
    assert row["standard_open_system_equations_imported"] == "no"
    assert row["literature_equations_adopted"] == "no"
    assert row["empirical_fit_executed"] == "no"
    assert row["tau_baseline_value_computed"] == "no"
    assert row["baseline_model_completed"] == "no"
    assert row["master_action_promoted"] == "no"


@pytest.mark.parametrize("stage_key", ORDERED_STAGE_KEYS)
def test_post_phi_transport_ccft_json_reports_match_builders(stage_key: str) -> None:
    spec = STAGES[stage_key]
    module_name, build_function_name = WRAPPER_BUILD_FUNCTION_BY_STAGE[stage_key]
    wrapper_builder = getattr(importlib.import_module(module_name), build_function_name)
    assert release_path(spec).exists()
    assert lean_path(spec).exists()
    assert (REPO_ROOT / WRAPPER_BY_STAGE[stage_key]).exists()
    assert wrapper_builder() == build_stage_payload(stage_key)
    assert _read_json(release_path(spec)) == wrapper_builder()


def test_post_phi_transport_ccft_chain_order_and_report_boundaries() -> None:
    previous_spec = None
    for stage_key in ORDERED_STAGE_KEYS:
        spec = STAGES[stage_key]
        report = _read_json(release_path(spec))
        if previous_spec is not None:
            assert previous_spec.selected_next_target == spec.consumed_target
            assert previous_spec.selected_next_target_kind == spec.consumed_target_kind
        previous_spec = spec

        assert report["lean_status_wording"] == LEAN_STATUS_WORDING
        assert report["lean_status_wording_lines"] == LEAN_STATUS_WORDING_LINES
        assert (
            report["full_toeformal_aggregate_status"]
            == FULL_TOEFORMAL_AGGREGATE_STATUS
        )
        assert report["scoped_lean_targets_status"] == SCOPED_LEAN_TARGETS_STATUS
        assert report["local_phi_triad_label"] == (
            LOCAL_PHI_THEOREM_LINKAGE_TRIAD_LABEL
        )
        assert report["local_phi_theorem_linkage_triad"] == LOCAL_PHI_TRIAD_EQUATIONS
        empirical_map_prepared = stage_key in {
            "empirical_packet",
            "empirical_review",
            "priority_packet",
            "priority_review",
            "selected_candidate_packet",
            "selected_candidate_review",
            "tolerance_registry_packet",
            "tolerance_registry_review",
            "baseline_semantics_packet",
            "baseline_semantics_review",
            "observable_definition_semantics_packet",
            "observable_definition_semantics_review",
            "residual_formula_selection_packet",
            "residual_formula_selection_review",
            "measurement_feedback_baseline_pressure_packet",
            "measurement_feedback_baseline_pressure_review",
            "baseline_component_registry_packet",
            "baseline_component_registry_review",
            "baseline_component_interaction_risk_packet",
            "baseline_component_interaction_risk_review",
            "baseline_construction_obligation_packet",
            "baseline_construction_obligation_review",
            "baseline_component_equation_scaffold_packet",
            "baseline_component_equation_scaffold_review",
            "baseline_component_equation_source_classification_packet",
            "baseline_component_equation_source_classification_review",
            "baseline_component_equation_source_validation_criteria_packet",
            "baseline_component_equation_source_validation_criteria_review",
            "baseline_component_equation_source_candidate_registry_packet",
            "baseline_component_equation_source_candidate_registry_review",
            "baseline_component_equation_source_applicability_review_packet",
            "baseline_component_equation_source_applicability_review",
            "baseline_component_equation_source_applicability_gap_classification_packet",
            "baseline_component_equation_source_applicability_gap_classification_review",
            "baseline_component_equation_source_applicability_gap_resolution_strategy_packet",
            "baseline_component_equation_source_applicability_gap_resolution_strategy_review",
        }
        assert (
            report["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"]
            is empirical_map_prepared
        )
        assert report["later_ccft_artifacts_fully_populated"] is empirical_map_prepared
        for flag in JSON_FALSE_FLAGS:
            assert report[flag] is False, flag

    assert STAGES["selector"].consumed_target == (
        "select_next_ck_family_theorem_linkage_obligation_after_phi_transport_"
        "closeout"
    )
    assert STAGES["ck_index_packet"].selected_next_target == (
        "review_ccft_ck_admissibility_obligation_index_packet_result"
    )
    assert STAGES["ck_index_review"].selected_next_target == (
        VARIATIONAL_PACKET_TARGET
    )
    assert STAGES["variational_packet"].selected_next_target == VARIATIONAL_REVIEW_TARGET
    assert STAGES["variational_review"].selected_next_target == EMPIRICAL_PACKET_TARGET
    assert STAGES["empirical_packet"].selected_next_target == EMPIRICAL_REVIEW_TARGET
    assert STAGES["empirical_review"].selected_next_target == PRIORITY_PACKET_TARGET
    assert STAGES["priority_packet"].selected_next_target == PRIORITY_REVIEW_TARGET
    assert (
        STAGES["priority_review"].selected_next_target
        == SELECTED_CANDIDATE_PACKET_TARGET
    )
    assert (
        STAGES["selected_candidate_packet"].selected_next_target
        == SELECTED_CANDIDATE_REVIEW_TARGET
    )
    assert (
        STAGES["selected_candidate_review"].selected_next_target
        == TOLERANCE_REGISTRY_PACKET_TARGET
    )
    assert (
        STAGES["tolerance_registry_packet"].selected_next_target
        == TOLERANCE_REGISTRY_REVIEW_TARGET
    )
    assert (
        STAGES["tolerance_registry_review"].selected_next_target
        == BASELINE_SEMANTICS_PACKET_TARGET
    )
    assert (
        STAGES["baseline_semantics_packet"].selected_next_target
        == BASELINE_SEMANTICS_REVIEW_TARGET
    )
    assert (
        STAGES["baseline_semantics_review"].selected_next_target
        == OBSERVABLE_DEFINITION_SEMANTICS_PACKET_TARGET
    )
    assert (
        STAGES["observable_definition_semantics_packet"].selected_next_target
        == OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_TARGET
    )
    assert (
        STAGES["observable_definition_semantics_review"].selected_next_target
        == RESIDUAL_FORMULA_SELECTION_PACKET_TARGET
    )
    assert (
        STAGES["residual_formula_selection_packet"].selected_next_target
        == RESIDUAL_FORMULA_SELECTION_REVIEW_TARGET
    )
    assert (
        STAGES["residual_formula_selection_review"].selected_next_target
        == MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_TARGET
    )
    assert (
        STAGES["measurement_feedback_baseline_pressure_packet"].selected_next_target
        == MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_TARGET
    )
    assert (
        STAGES["measurement_feedback_baseline_pressure_review"].selected_next_target
        == BASELINE_COMPONENT_REGISTRY_PACKET_TARGET
    )
    assert (
        STAGES["baseline_component_registry_packet"].selected_next_target
        == BASELINE_COMPONENT_REGISTRY_REVIEW_TARGET
    )
    assert (
        STAGES["baseline_component_registry_review"].selected_next_target
        == BASELINE_COMPONENT_INTERACTION_RISK_PACKET_TARGET
    )
    assert (
        STAGES["baseline_component_interaction_risk_packet"].selected_next_target
        == BASELINE_COMPONENT_INTERACTION_RISK_REVIEW_TARGET
    )
    assert (
        STAGES["baseline_component_interaction_risk_review"].selected_next_target
        == BASELINE_CONSTRUCTION_OBLIGATION_PACKET_TARGET
    )
    assert (
        STAGES["baseline_construction_obligation_packet"].selected_next_target
        == BASELINE_CONSTRUCTION_OBLIGATION_REVIEW_TARGET
    )
    assert (
        STAGES["baseline_construction_obligation_review"].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SCAFFOLD_TARGET
    )
    assert (
        STAGES["baseline_component_equation_scaffold_packet"].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SCAFFOLD_REVIEW_TARGET
    )
    assert (
        STAGES["baseline_component_equation_scaffold_review"].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_TARGET
    )
    assert (
        STAGES[
            "baseline_component_equation_source_classification_packet"
        ].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_TARGET
    )
    assert (
        STAGES[
            "baseline_component_equation_source_classification_review"
        ].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_TARGET
    )
    assert (
        STAGES[
            "baseline_component_equation_source_validation_criteria_packet"
        ].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_TARGET
    )
    assert (
        STAGES[
            "baseline_component_equation_source_validation_criteria_review"
        ].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_TARGET
    )
    assert (
        STAGES[
            "baseline_component_equation_source_candidate_registry_packet"
        ].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_TARGET
    )
    assert (
        STAGES[
            "baseline_component_equation_source_candidate_registry_review"
        ].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_TARGET
    )
    assert (
        STAGES[
            "baseline_component_equation_source_applicability_review_packet"
        ].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_TARGET
    )
    assert (
        STAGES[
            "baseline_component_equation_source_applicability_review"
        ].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_TARGET
    )
    assert (
        STAGES[
            "baseline_component_equation_source_applicability_gap_classification_packet"
        ].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_TARGET
    )
    assert (
        STAGES[
            "baseline_component_equation_source_applicability_gap_classification_review"
        ].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_TARGET
    )
    assert (
        STAGES[
            "baseline_component_equation_source_applicability_gap_resolution_strategy_packet"
        ].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_REVIEW_TARGET
    )
    assert (
        STAGES[
            "baseline_component_equation_source_applicability_gap_resolution_strategy_review"
        ].selected_next_target
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_PRIORITY_SELECTION_TARGET
    )


def test_local_phi_triad_and_ccft_roadmap_staging_boundaries() -> None:
    for stage_key in ("triad_packet", "triad_review"):
        report = _read_json(release_path(STAGES[stage_key]))
        assert report["local_phi_theorem_linkage_triad"] == [
            "C_source^phi = 0",
            "C_bridge^phi = 0",
            "C_transport^phi = 0",
        ]
        assert report["local_phi_theorem_linkage_triad_count"] == 3
        assert "not a phi C_k rule-family closeout" in report["triad_boundary"]
        assert report["historical_20260619_rule_family_artifacts_overwritten"] is False
        assert report["new_triad_called_rule_family_closeout"] is False

    for stage_key in ("roadmap_packet", "roadmap_review"):
        report = _read_json(release_path(STAGES[stage_key]))
        assert report["roadmap_rebase_lists_follow_on_artifacts_only"] is True
        assert report["CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared"] is False
        assert report["CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared"] is False
        assert report["CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared"] is False
        assert (
            report["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"]
            is False
        )
        assert report["ccft_role"] == "candidate mesoscopic coherence bridge layer"
        assert report["master_action_role"] == (
            "non-promoted candidate organizing surface"
        )
        assert report["C_k_role"] == "admissibility-only bridge-checking family"
        assert report["phi_triad_role"] == "local theorem-linkage family only"

    crosswalk = _read_json(release_path(STAGES["crosswalk_packet"]))
    assert crosswalk["CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared"] is True
    assert crosswalk["CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared"] is False
    assert crosswalk["CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared"] is False
    assert (
        crosswalk["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"]
        is False
    )

    ck_index = _read_json(release_path(STAGES["ck_index_packet"]))
    assert ck_index["CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared"] is True
    assert ck_index["CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared"] is True
    assert ck_index["CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared"] is False
    assert (
        ck_index["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"]
        is False
    )

    variational = _read_json(release_path(STAGES["variational_packet"]))
    assert variational["CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared"] is True
    assert variational["CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared"] is True
    assert variational["CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared"] is True
    assert (
        variational["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"]
        is False
    )
    assert variational["ccft_full_variational_action_program_target_count"] == 13
    for target in (
        "CCFT full Lagrangian candidate targets",
        "CCFT full Hamiltonian candidate targets",
        "phi-sector variational route targets",
        "chi-sector variational route targets",
        "R/K rotor-curvature variational route targets",
        "CCFT stress-energy/source candidate targets",
        "CCFT C_source derivation targets",
        "CCFT C_bridge derivation targets",
        "CCFT C_transport component-derivation targets",
        "CCFT C_exchange phi-chi exchange-balance targets",
        "required blockers before action embedding",
        "required blockers before C_k variation",
        "required blockers before empirical discriminator claims",
    ):
        assert target in variational["ccft_full_variational_action_program_targets"]
    assert variational["C_k_action_embedding_authorized"] is False
    assert variational["C_k_variation_authorized"] is False
    assert variational["empirical_discriminator_claims_authorized"] is False

    empirical = _read_json(release_path(STAGES["empirical_packet"]))
    assert empirical["CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared"] is True
    assert empirical["CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared"] is True
    assert empirical["CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared"] is True
    assert empirical["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"] is True
    assert empirical["later_ccft_artifacts_fully_populated"] is True
    assert empirical["ccft_empirical_discriminator_candidate_map_target_count"] == 11
    for target in (
        "candidate measurable systems",
        "candidate observables",
        "candidate control variables",
        "candidate baseline models",
        "candidate failure modes",
        "candidate falsifiers",
        "candidate numerical-vs-physical comparison routes",
        "candidate empirical-discriminator questions",
        "required blockers before empirical claim",
        "required blockers before CCFT validation",
        "required blockers before pillar or seam relevance",
    ):
        assert target in empirical["ccft_empirical_discriminator_candidate_map_targets"]
    assert empirical["empirical_claim_authorized"] is False
    assert empirical["pillar_closure_authorized"] is False

    priority = _read_json(release_path(STAGES["priority_packet"]))
    assert priority["CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared"] is True
    assert priority["CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared"] is True
    assert priority["CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared"] is True
    assert priority["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"] is True
    assert priority["later_ccft_artifacts_fully_populated"] is True
    assert (
        priority[
            "ccft_empirical_discriminator_candidate_priority_selection_action_count"
        ]
        == 10
    )
    assert (
        priority[
            "ccft_empirical_discriminator_candidate_priority_selection_criteria_count"
        ]
        == 7
    )
    assert priority["selected_top_candidate_for_future_packet_only"] == (
        "controlled_mesoscopic_coherence_platform_candidate"
    )
    assert priority["future_packet_preparation_only"] is True
    assert priority["empirical_test_executed"] is False
    assert priority["CCFT_validated"] is False


def test_post_phi_transport_ccft_registry_rotation_and_stage_rows() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    payload = loop_registry()
    state = payload["current_target_state"]
    assert state["previous_live_next_target"] == FINAL_PREVIOUS_TARGET
    assert state["live_next_target"] == FINAL_LIVE_TARGET
    assert state["active_lane"] == FINAL_LIVE_TARGET
    assert state["live_next_target_evidence"] == FINAL_EVIDENCE
    assert state["live_next_target_report"] == FINAL_REPORT
    assert state["live_next_target_outcome"] == FINAL_OUTCOME
    assert state["live_next_target_strict_outcome"] == FINAL_STRICT_OUTCOME
    assert state["live_next_target_kind"] == FINAL_KIND
    assert payload["CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0"] == FINAL_STRICT_OUTCOME
    assert payload["CURRENT_LIVE_TARGET_KIND_v0"] == FINAL_KIND

    for stage_key in ORDERED_STAGE_KEYS:
        spec = STAGES[stage_key]
        row = workstream(spec.consumed_target, payload)
        assert row["status"] == "paused"
        assert row["active_lane"] == spec.consumed_target
        assert row["authorized_next_strict_target"] == spec.consumed_target
        assert row["authorized_target"] == spec.consumed_target
        assert row["authorization_evidence"] == _rel(lean_path(spec))
        assert row["report"] == _rel(release_path(spec))
        assert row["packet_result"] == spec.outcome_id
        assert row["strict_packet_result"] == spec.strict_outcome_id
        assert row["selected_next_target"] == spec.selected_next_target
        assert row["selected_next_target_kind"] == spec.selected_next_target_kind
        assert row["local_phi_triad_label"] == (
            LOCAL_PHI_THEOREM_LINKAGE_TRIAD_LABEL
        )
        assert row["local_phi_theorem_linkage_triad"] in (
            LOCAL_PHI_TRIAD_EQUATIONS,
            LOCAL_PHI_TRIAD_REGISTRY_TEXT,
        )
        empirical_map_prepared = (
            "yes"
            if stage_key
            in {
                "empirical_packet",
                "empirical_review",
                "priority_packet",
                "priority_review",
                "selected_candidate_packet",
                "selected_candidate_review",
                "tolerance_registry_packet",
                "tolerance_registry_review",
                "baseline_semantics_packet",
                "baseline_semantics_review",
                "observable_definition_semantics_packet",
                "observable_definition_semantics_review",
                "residual_formula_selection_packet",
                "residual_formula_selection_review",
                "measurement_feedback_baseline_pressure_packet",
                "measurement_feedback_baseline_pressure_review",
                "baseline_component_registry_packet",
                "baseline_component_registry_review",
                "baseline_component_interaction_risk_packet",
                "baseline_component_interaction_risk_review",
                "baseline_construction_obligation_packet",
                "baseline_construction_obligation_review",
                "baseline_component_equation_scaffold_packet",
                "baseline_component_equation_scaffold_review",
                "baseline_component_equation_source_classification_packet",
                "baseline_component_equation_source_classification_review",
                "baseline_component_equation_source_validation_criteria_packet",
                "baseline_component_equation_source_validation_criteria_review",
                    "baseline_component_equation_source_candidate_registry_packet",
                    "baseline_component_equation_source_candidate_registry_review",
                    "baseline_component_equation_source_applicability_review_packet",
                    "baseline_component_equation_source_applicability_review",
                    "baseline_component_equation_source_applicability_gap_classification_packet",
                    "baseline_component_equation_source_applicability_gap_classification_review",
                    "baseline_component_equation_source_applicability_gap_resolution_strategy_packet",
                    "baseline_component_equation_source_applicability_gap_resolution_strategy_review",
                }
                else "no"
            )
        assert row["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"] == (
            empirical_map_prepared
        )
        assert row["later_ccft_artifacts_fully_populated"] == empirical_map_prepared
        if spec.result_kind == "selection":
            assert row["selection_result"] == spec.outcome_id
            assert row["strict_selection_result"] == spec.strict_outcome_id
        if spec.result_kind == "review":
            assert row["review_result"] == spec.outcome_id
            assert row["strict_review_result"] == spec.strict_outcome_id
        _assert_registry_nonclaims(row)

    ck_review = workstream(
        "review_ccft_ck_admissibility_obligation_index_packet_result", payload
    )
    assert ck_review["status"] == "paused"
    assert ck_review["review_result"] == STAGES["ck_index_review"].outcome_id
    assert ck_review["strict_review_result"] == (
        STAGES["ck_index_review"].strict_outcome_id
    )
    assert ck_review["selected_next_target"] == VARIATIONAL_PACKET_TARGET
    assert ck_review["selected_next_target_kind"] == (
        "ccft_full_variational_action_program_packet"
    )
    assert ck_review["prepared_packet_result"] == STAGES["ck_index_packet"].outcome_id
    assert ck_review["prepared_packet_strict_result"] == (
        STAGES["ck_index_packet"].strict_outcome_id
    )
    _assert_registry_nonclaims(ck_review)

    prepared_packet = workstream(VARIATIONAL_PACKET_TARGET, payload)
    assert prepared_packet["status"] == "paused"
    assert prepared_packet["packet_result"] == STAGES["variational_packet"].outcome_id
    assert prepared_packet["strict_packet_result"] == (
        STAGES["variational_packet"].strict_outcome_id
    )
    assert prepared_packet["selected_next_target"] == VARIATIONAL_REVIEW_TARGET
    assert prepared_packet["selected_next_target_kind"] == (
        "ccft_full_variational_action_program_packet_result_review"
    )
    assert prepared_packet["ccft_full_variational_action_program_target_count"] == 13
    assert prepared_packet["C_k_action_embedding_authorized"] == "no"
    assert prepared_packet["C_k_variation_authorized"] == "no"
    assert prepared_packet["empirical_discriminator_claims_authorized"] == "no"
    _assert_registry_nonclaims(prepared_packet)

    variational_review = workstream(VARIATIONAL_REVIEW_TARGET, payload)
    assert variational_review["status"] == "paused"
    assert variational_review["review_result"] == STAGES["variational_review"].outcome_id
    assert variational_review["strict_review_result"] == (
        STAGES["variational_review"].strict_outcome_id
    )
    assert variational_review["prepared_packet_result"] == (
        STAGES["variational_packet"].outcome_id
    )
    assert variational_review["prepared_packet_strict_result"] == (
        STAGES["variational_packet"].strict_outcome_id
    )
    assert variational_review["selected_next_target"] == EMPIRICAL_PACKET_TARGET
    assert variational_review["selected_next_target_kind"] == (
        "ccft_empirical_discriminator_candidate_map_packet"
    )
    assert variational_review[
        "ccft_full_variational_action_program_review_acceptance_item_count"
    ] == 22
    assert "CCFT full Lagrangian candidate targets indexed" in variational_review[
        "ccft_full_variational_action_program_review_acceptance_items"
    ]
    assert variational_review["C_k_action_embedding_authorized"] == "no"
    assert variational_review["C_k_variation_authorized"] == "no"
    assert variational_review["empirical_discriminator_claims_authorized"] == "no"
    _assert_registry_nonclaims(variational_review)

    empirical_packet = workstream(EMPIRICAL_PACKET_TARGET, payload)
    assert empirical_packet["status"] == "paused"
    assert empirical_packet["packet_result"] == STAGES["empirical_packet"].outcome_id
    assert empirical_packet["strict_packet_result"] == (
        STAGES["empirical_packet"].strict_outcome_id
    )
    assert empirical_packet["selected_next_target"] == EMPIRICAL_REVIEW_TARGET
    assert empirical_packet["selected_next_target_kind"] == (
        "ccft_empirical_discriminator_candidate_map_packet_result_review"
    )
    assert (
        empirical_packet["ccft_empirical_discriminator_candidate_map_target_count"]
        == 11
    )
    assert "candidate measurable systems" in empirical_packet[
        "ccft_empirical_discriminator_candidate_map_targets"
    ]
    assert "candidate falsifiers" in empirical_packet[
        "ccft_empirical_discriminator_candidate_map_targets"
    ]
    assert empirical_packet["empirical_claim_authorized"] == "no"
    assert empirical_packet["pillar_closure_authorized"] == "no"
    assert empirical_packet["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"] == "yes"
    assert empirical_packet["later_ccft_artifacts_fully_populated"] == "yes"
    _assert_registry_nonclaims(empirical_packet)

    empirical_review = workstream(EMPIRICAL_REVIEW_TARGET, payload)
    assert empirical_review["status"] == "paused"
    assert empirical_review["review_result"] == STAGES["empirical_review"].outcome_id
    assert empirical_review["strict_review_result"] == (
        STAGES["empirical_review"].strict_outcome_id
    )
    assert empirical_review["prepared_packet_result"] == (
        STAGES["empirical_packet"].outcome_id
    )
    assert empirical_review["prepared_packet_strict_result"] == (
        STAGES["empirical_packet"].strict_outcome_id
    )
    assert empirical_review["selected_next_target"] == PRIORITY_PACKET_TARGET
    assert empirical_review["selected_next_target_kind"] == (
        "ccft_empirical_discriminator_candidate_priority_selection_packet"
    )
    assert (
        empirical_review[
            "ccft_empirical_discriminator_candidate_map_review_acceptance_item_count"
        ]
        == 26
    )
    assert "candidate measurable systems indexed" in empirical_review[
        "ccft_empirical_discriminator_candidate_map_review_acceptance_items"
    ]
    assert "required blockers before CCFT validation preserved" in empirical_review[
        "ccft_empirical_discriminator_candidate_map_review_acceptance_items"
    ]
    assert empirical_review["empirical_claim_authorized"] == "no"
    assert empirical_review["pillar_closure_authorized"] == "no"
    _assert_registry_nonclaims(empirical_review)

    priority_packet = workstream(PRIORITY_PACKET_TARGET, payload)
    assert priority_packet["status"] == "paused"
    assert priority_packet["packet_result"] == STAGES["priority_packet"].outcome_id
    assert priority_packet["strict_packet_result"] == (
        STAGES["priority_packet"].strict_outcome_id
    )
    assert priority_packet["selected_next_target"] == PRIORITY_REVIEW_TARGET
    assert priority_packet["selected_next_target_kind"] == (
        "ccft_empirical_discriminator_candidate_priority_selection_packet_result_review"
    )
    assert priority_packet[
        "ccft_empirical_discriminator_candidate_priority_selection_action_count"
    ] == 10
    assert priority_packet[
        "ccft_empirical_discriminator_candidate_priority_selection_criteria_count"
    ] == 7
    assert priority_packet["selected_top_candidate_for_future_packet_only"] == (
        "controlled_mesoscopic_coherence_platform_candidate"
    )
    assert "rank_1_controlled_mesoscopic_coherence_platform_candidate" in (
        priority_packet["candidate_measurable_system_ranking"]
    )
    assert "risk of overclaim" in priority_packet[
        "ccft_empirical_discriminator_candidate_priority_selection_criteria"
    ]
    assert priority_packet["future_packet_preparation_only"] == "yes"
    assert priority_packet["empirical_test_executed"] == "no"
    assert priority_packet["CCFT_validated"] == "no"
    _assert_registry_nonclaims(priority_packet)

    priority_review = workstream(PRIORITY_REVIEW_TARGET, payload)
    assert priority_review["status"] == "paused"
    assert priority_review["review_result"] == STAGES["priority_review"].outcome_id
    assert priority_review["strict_review_result"] == (
        STAGES["priority_review"].strict_outcome_id
    )
    assert priority_review["prepared_packet_result"] == (
        STAGES["priority_packet"].outcome_id
    )
    assert priority_review["prepared_packet_strict_result"] == (
        STAGES["priority_packet"].strict_outcome_id
    )
    assert priority_review["selected_next_target"] == SELECTED_CANDIDATE_PACKET_TARGET
    assert priority_review["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_candidate_packet"
    )
    assert priority_review[
        "ccft_empirical_discriminator_candidate_priority_selection_review_acceptance_item_count"
    ] == 25
    assert "selected top candidate retained for future packet preparation only" in (
        priority_review[
            "ccft_empirical_discriminator_candidate_priority_selection_review_acceptance_items"
        ]
    )
    assert priority_review[
        "selected_top_discriminator_priority_accepted_for_future_packet_only"
    ] == "yes"
    assert priority_review["selected_candidate_packet_preparation_target"] == (
        SELECTED_CANDIDATE_PACKET_TARGET
    )
    assert priority_review["empirical_execution_authorized"] == "no"
    assert priority_review["empirical_test_executed"] == "no"
    assert priority_review["CCFT_validated"] == "no"
    _assert_registry_nonclaims(priority_review)

    selected_candidate_packet = workstream(SELECTED_CANDIDATE_PACKET_TARGET, payload)
    assert selected_candidate_packet["status"] == "paused"
    assert (
        selected_candidate_packet["packet_result"]
        == STAGES["selected_candidate_packet"].outcome_id
    )
    assert selected_candidate_packet["strict_packet_result"] == (
        STAGES["selected_candidate_packet"].strict_outcome_id
    )
    assert (
        selected_candidate_packet["selected_next_target"]
        == SELECTED_CANDIDATE_REVIEW_TARGET
    )
    assert selected_candidate_packet["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_candidate_packet_result_review"
    )
    assert (
        selected_candidate_packet[
            "selected_ccft_empirical_discriminator_candidate_packet_action_count"
        ]
        == 11
    )
    assert selected_candidate_packet[
        "selected_ccft_empirical_discriminator_candidate_id"
    ] == "controlled_mesoscopic_coherence_platform_candidate"
    assert selected_candidate_packet[
        "selected_ccft_empirical_discriminator_candidate_observable"
    ] == "coherence_lifetime_residual_candidate"
    assert selected_candidate_packet[
        "selected_ccft_empirical_discriminator_candidate_baseline"
    ] == "standard_open_system_decoherence_baseline_comparison"
    assert selected_candidate_packet[
        "selected_ccft_empirical_discriminator_candidate_falsifier"
    ] == "null_separation_from_baseline_with_registered_tolerances"
    assert selected_candidate_packet["priority_selection_result_review_consumed"] == (
        "yes"
    )
    assert selected_candidate_packet[
        "selected_candidate_instantiated_for_future_packet_only"
    ] == "yes"
    assert selected_candidate_packet["selected_observable_bound_as_planning_row"] == (
        "yes"
    )
    assert selected_candidate_packet["selected_baseline_bound_as_planning_row"] == (
        "yes"
    )
    assert selected_candidate_packet["selected_falsifier_bound_as_planning_row"] == (
        "yes"
    )
    assert selected_candidate_packet["empirical_execution_authorized"] == "no"
    assert selected_candidate_packet["empirical_protocol_executed"] == "no"
    assert selected_candidate_packet["selected_candidate_validation_claimed"] == "no"
    assert selected_candidate_packet["empirical_test_executed"] == "no"
    assert selected_candidate_packet["CCFT_validated"] == "no"
    _assert_registry_nonclaims(selected_candidate_packet)

    selected_candidate_review = workstream(SELECTED_CANDIDATE_REVIEW_TARGET, payload)
    assert selected_candidate_review["status"] == "paused"
    assert (
        selected_candidate_review["review_result"]
        == STAGES["selected_candidate_review"].outcome_id
    )
    assert selected_candidate_review["strict_review_result"] == (
        STAGES["selected_candidate_review"].strict_outcome_id
    )
    assert selected_candidate_review["prepared_packet_result"] == (
        STAGES["selected_candidate_packet"].outcome_id
    )
    assert selected_candidate_review["prepared_packet_strict_result"] == (
        STAGES["selected_candidate_packet"].strict_outcome_id
    )
    assert (
        selected_candidate_review["selected_next_target"]
        == TOLERANCE_REGISTRY_PACKET_TARGET
    )
    assert selected_candidate_review["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_tolerance_registry_packet"
    )
    assert (
        selected_candidate_review[
            "selected_ccft_empirical_discriminator_candidate_review_acceptance_item_count"
        ]
        == 29
    )
    assert "registered_tolerances treated as non-executed traceability placeholder only" in (
        selected_candidate_review[
            "selected_ccft_empirical_discriminator_candidate_review_acceptance_items"
        ]
    )
    assert "registered_tolerances not treated as empirically calibrated" in (
        selected_candidate_review[
            "selected_ccft_empirical_discriminator_candidate_review_acceptance_items"
        ]
    )
    assert (
        selected_candidate_review[
            "selected_candidate_packet_accepted_as_future_packet_only"
        ]
        == "yes"
    )
    assert (
        selected_candidate_review["registered_tolerances_traceability_placeholder_only"]
        == "yes"
    )
    assert selected_candidate_review["registered_tolerances_empirically_calibrated"] == (
        "no"
    )
    assert selected_candidate_review["registered_tolerances_execution_authorized"] == (
        "no"
    )
    assert selected_candidate_review[
        "registered_tolerances_empirical_claim_authorized"
    ] == "no"
    assert selected_candidate_review["empirical_protocol_design_authorized"] == "no"
    assert selected_candidate_review["empirical_execution_authorized"] == "no"
    assert selected_candidate_review["empirical_protocol_executed"] == "no"
    assert selected_candidate_review["empirical_test_executed"] == "no"
    assert selected_candidate_review["CCFT_validated"] == "no"
    _assert_registry_nonclaims(selected_candidate_review)

    tolerance_registry_packet = workstream(TOLERANCE_REGISTRY_PACKET_TARGET, payload)
    assert tolerance_registry_packet["status"] == "paused"
    assert (
        tolerance_registry_packet["packet_result"]
        == STAGES["tolerance_registry_packet"].outcome_id
    )
    assert tolerance_registry_packet["strict_packet_result"] == (
        STAGES["tolerance_registry_packet"].strict_outcome_id
    )
    assert tolerance_registry_packet["selected_next_target"] == (
        TOLERANCE_REGISTRY_REVIEW_TARGET
    )
    assert tolerance_registry_packet["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_tolerance_registry_packet_result_review"
    )
    assert (
        tolerance_registry_packet[
            "selected_ccft_empirical_discriminator_tolerance_registry_field_count"
        ]
        == 8
    )
    assert (
        tolerance_registry_packet[
            "selected_ccft_empirical_discriminator_tolerance_registry_row_count"
        ]
        == 1
    )
    assert "TOL-CCFT-MESO-COH-LIFETIME-RESIDUAL-v0" in (
        tolerance_registry_packet[
            "selected_ccft_empirical_discriminator_tolerance_ids"
        ]
    )
    assert tolerance_registry_packet[
        "selected_ccft_empirical_discriminator_tolerance_observable_binding"
    ] == "coherence_lifetime_residual_candidate"
    assert tolerance_registry_packet[
        "selected_ccft_empirical_discriminator_tolerance_baseline_binding"
    ] == "standard_open_system_decoherence_baseline_comparison"
    assert tolerance_registry_packet[
        "selected_ccft_empirical_discriminator_tolerance_null_condition"
    ] == "null_separation_from_baseline_with_registered_tolerances"
    assert tolerance_registry_packet[
        "selected_ccft_empirical_discriminator_tolerance_source_status"
    ] == "placeholder_future_empirical_calibration_needed"
    assert tolerance_registry_packet[
        "selected_ccft_empirical_discriminator_tolerance_execution_status"
    ] == "not_executed"
    assert "confidence_interval_separation_placeholder" in (
        tolerance_registry_packet[
            "selected_ccft_empirical_discriminator_tolerance_comparison_semantics"
        ]
    )
    assert (
        tolerance_registry_packet["registered_tolerances_traceability_placeholder_only"]
        == "yes"
    )
    assert tolerance_registry_packet["registered_tolerances_empirically_calibrated"] == (
        "no"
    )
    assert tolerance_registry_packet["registered_tolerances_statistically_validated"] == (
        "no"
    )
    assert tolerance_registry_packet["registered_tolerances_execution_authorized"] == (
        "no"
    )
    assert tolerance_registry_packet[
        "registered_tolerances_empirical_claim_authorized"
    ] == "no"
    assert tolerance_registry_packet[
        "registered_tolerances_sufficient_for_execution"
    ] == "no"
    assert tolerance_registry_packet[
        "registered_tolerances_distinguish_ccft_from_baseline_claimed"
    ] == "no"
    assert tolerance_registry_packet[
        "registered_tolerances_bound_to_measurement_campaign"
    ] == "no"
    assert tolerance_registry_packet["empirical_methods_section_claimed"] == "no"
    assert tolerance_registry_packet["empirical_protocol_design_authorized"] == "no"
    assert tolerance_registry_packet["empirical_execution_authorized"] == "no"
    assert tolerance_registry_packet["empirical_test_executed"] == "no"
    assert tolerance_registry_packet["CCFT_validated"] == "no"
    _assert_registry_nonclaims(tolerance_registry_packet)

    tolerance_registry_review = workstream(TOLERANCE_REGISTRY_REVIEW_TARGET, payload)
    assert tolerance_registry_review["status"] == "paused"
    assert (
        tolerance_registry_review["review_result"]
        == STAGES["tolerance_registry_review"].outcome_id
    )
    assert tolerance_registry_review["strict_review_result"] == (
        STAGES["tolerance_registry_review"].strict_outcome_id
    )
    assert tolerance_registry_review["prepared_packet_result"] == (
        STAGES["tolerance_registry_packet"].outcome_id
    )
    assert tolerance_registry_review["prepared_packet_strict_result"] == (
        STAGES["tolerance_registry_packet"].strict_outcome_id
    )
    assert tolerance_registry_review["selected_next_target"] == BASELINE_SEMANTICS_PACKET_TARGET
    assert tolerance_registry_review["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet"
    )
    assert (
        tolerance_registry_review[
            "selected_ccft_empirical_discriminator_tolerance_registry_review_acceptance_item_count"
        ]
        == 35
    )
    assert "registered_tolerances not treated as empirically calibrated" in (
        tolerance_registry_review[
            "selected_ccft_empirical_discriminator_tolerance_registry_review_acceptance_items"
        ]
    )
    assert "tolerance row not accepted as a statistical decision rule" in (
        tolerance_registry_review[
            "selected_ccft_empirical_discriminator_tolerance_registry_review_acceptance_items"
        ]
    )
    assert (
        tolerance_registry_review[
            "tolerance_registry_packet_accepted_as_traceability_only"
        ]
        == "yes"
    )
    assert (
        tolerance_registry_review[
            "tolerance_registry_rows_accepted_as_non_executed_only"
        ]
        == "yes"
    )
    assert (
        tolerance_registry_review[
            "comparison_semantics_accepted_as_placeholders_only"
        ]
        == "yes"
    )
    assert tolerance_registry_review["null_condition_retained_as_default"] == "yes"
    assert (
        tolerance_registry_review[
            "future_empirical_calibration_required_before_claim"
        ]
        == "yes"
    )
    assert tolerance_registry_review["tolerance_row_accepted_as_test_protocol"] == (
        "no"
    )
    assert tolerance_registry_review[
        "tolerance_row_accepted_as_effect_size_threshold"
    ] == "no"
    assert tolerance_registry_review[
        "tolerance_row_accepted_as_statistical_decision_rule"
    ] == "no"
    assert tolerance_registry_review["tolerance_row_accepted_as_experimental_design"] == (
        "no"
    )
    assert tolerance_registry_review["registered_tolerances_empirically_calibrated"] == (
        "no"
    )
    assert tolerance_registry_review["registered_tolerances_statistically_validated"] == (
        "no"
    )
    assert tolerance_registry_review["registered_tolerances_sufficient_for_execution"] == (
        "no"
    )
    assert tolerance_registry_review[
        "registered_tolerances_distinguish_ccft_from_baseline_claimed"
    ] == "no"
    assert tolerance_registry_review[
        "registered_tolerances_bound_to_measurement_campaign"
    ] == "no"
    assert tolerance_registry_review["selected_next_planning_packet_target"] == (
        BASELINE_SEMANTICS_PACKET_TARGET
    )
    _assert_registry_nonclaims(tolerance_registry_review)

    baseline_packet = workstream(BASELINE_SEMANTICS_PACKET_TARGET, payload)
    assert baseline_packet["status"] == "paused"
    assert baseline_packet["packet_result"] == STAGES["baseline_semantics_packet"].outcome_id
    assert baseline_packet["strict_packet_result"] == (
        STAGES["baseline_semantics_packet"].strict_outcome_id
    )
    assert baseline_packet["selected_next_target"] == BASELINE_SEMANTICS_REVIEW_TARGET
    assert baseline_packet["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_result_review"
    )
    assert (
        baseline_packet[
            "selected_ccft_empirical_discriminator_baseline_comparison_semantics_field_count"
        ]
        == 10
    )
    assert (
        baseline_packet[
            "selected_ccft_empirical_discriminator_baseline_comparison_semantics_row_count"
        ]
        == 1
    )
    assert "BSEM-CCFT-MESO-COH-LIFETIME-v0" in (
        baseline_packet[
            "selected_ccft_empirical_discriminator_baseline_semantics_ids"
        ]
    )
    assert baseline_packet[
        "selected_ccft_empirical_discriminator_baseline_candidate_binding"
    ] == "controlled_mesoscopic_coherence_platform_candidate"
    assert baseline_packet[
        "selected_ccft_empirical_discriminator_baseline_observable_binding"
    ] == "coherence_lifetime_residual_candidate"
    assert baseline_packet["selected_ccft_empirical_discriminator_baseline_binding"] == (
        "standard_open_system_decoherence_baseline_comparison"
    )
    assert baseline_packet[
        "selected_ccft_empirical_discriminator_baseline_null_default"
    ] == "null_separation_from_baseline_with_registered_tolerances"
    assert baseline_packet[
        "selected_ccft_empirical_discriminator_baseline_tolerance_binding"
    ] == "TOL-CCFT-MESO-COH-LIFETIME-RESIDUAL-v0"
    assert baseline_packet[
        "selected_ccft_empirical_discriminator_residual_definition_status"
    ] == "placeholder_future_refinement_needed"
    assert baseline_packet[
        "selected_ccft_empirical_discriminator_comparison_direction_status"
    ] == "placeholder_direction_not_selected"
    assert baseline_packet["baseline_comparison_semantics_packet_prepared"] == "yes"
    assert baseline_packet["baseline_comparison_semantics_rows_registered"] == "yes"
    assert baseline_packet["baseline_semantics_logic_only"] == "yes"
    assert baseline_packet["baseline_complete_claimed"] == "no"
    assert baseline_packet["baseline_experimentally_fitted"] == "no"
    assert baseline_packet["residual_observed"] == "no"
    assert baseline_packet["tolerance_determines_significance"] == "no"
    assert baseline_packet["ccft_measurable_separation_predicted"] == "no"
    assert baseline_packet["candidate_ready_for_execution"] == "no"
    assert baseline_packet["baseline_separation_claimed"] == "no"
    assert baseline_packet["empirical_protocol_authorized"] == "no"
    assert baseline_packet["empirical_protocol_defined"] == "no"
    assert baseline_packet["statistical_validation_claimed"] == "no"
    assert baseline_packet["statistical_decision_rule_defined"] == "no"
    assert baseline_packet["effect_size_threshold_defined"] == "no"
    assert baseline_packet["execution_readiness_claimed"] == "no"
    _assert_registry_nonclaims(baseline_packet)

    baseline_review = workstream(BASELINE_SEMANTICS_REVIEW_TARGET, payload)
    assert baseline_review["status"] == "paused"
    assert (
        baseline_review["review_result"]
        == STAGES["baseline_semantics_review"].outcome_id
    )
    assert baseline_review["strict_review_result"] == (
        STAGES["baseline_semantics_review"].strict_outcome_id
    )
    assert baseline_review["prepared_packet_result"] == (
        STAGES["baseline_semantics_packet"].outcome_id
    )
    assert baseline_review["prepared_packet_strict_result"] == (
        STAGES["baseline_semantics_packet"].strict_outcome_id
    )
    assert (
        baseline_review["selected_next_target"]
        == OBSERVABLE_DEFINITION_SEMANTICS_PACKET_TARGET
    )
    assert baseline_review["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_observable_definition_semantics_packet"
    )
    assert (
        baseline_review[
            "selected_ccft_empirical_discriminator_baseline_comparison_semantics_review_acceptance_item_count"
        ]
        == 34
    )
    assert "baseline not accepted as complete" in (
        baseline_review[
            "selected_ccft_empirical_discriminator_baseline_comparison_semantics_review_acceptance_items"
        ]
    )
    assert "experimental protocol readiness not accepted" in (
        baseline_review[
            "selected_ccft_empirical_discriminator_baseline_comparison_semantics_review_acceptance_items"
        ]
    )
    assert baseline_review[
        "baseline_comparison_semantics_packet_accepted_as_logic_only"
    ] == "yes"
    assert baseline_review[
        "baseline_semantics_rows_accepted_as_non_executed_only"
    ] == "yes"
    assert baseline_review[
        "residual_definition_status_accepted_as_placeholder_only"
    ] == "yes"
    assert baseline_review[
        "comparison_direction_accepted_as_placeholder_only"
    ] == "yes"
    assert baseline_review["baseline_not_accepted_as_complete"] == "yes"
    assert baseline_review["baseline_adequacy_accepted"] == "no"
    assert baseline_review["baseline_empirical_fit_quality_accepted"] == "no"
    assert baseline_review["statistical_decision_rule_validity_accepted"] == "no"
    assert baseline_review["observed_separation_accepted"] == "no"
    assert baseline_review["ccft_predicted_separation_accepted"] == "no"
    assert baseline_review["experimental_protocol_readiness_accepted"] == "no"
    assert (
        baseline_review["selected_next_planning_packet_target"]
        == OBSERVABLE_DEFINITION_SEMANTICS_PACKET_TARGET
    )
    _assert_registry_nonclaims(baseline_review)

    observable_packet = workstream(OBSERVABLE_DEFINITION_SEMANTICS_PACKET_TARGET, payload)
    assert observable_packet["status"] == "paused"
    assert (
        observable_packet["packet_result"]
        == STAGES["observable_definition_semantics_packet"].outcome_id
    )
    assert (
        observable_packet["strict_packet_result"]
        == STAGES["observable_definition_semantics_packet"].strict_outcome_id
    )
    assert (
        observable_packet["selected_next_target"]
        == OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_TARGET
    )
    assert observable_packet["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_observable_definition_semantics_packet_result_review"
    )
    assert (
        observable_packet[
            "selected_ccft_empirical_discriminator_observable_definition_semantics_field_count"
        ]
        == 9
    )
    assert (
        observable_packet[
            "selected_ccft_empirical_discriminator_observable_definition_semantics_row_count"
        ]
        == 1
    )
    assert "coherence_lifetime_residual_candidate" in (
        observable_packet["selected_ccft_empirical_discriminator_observable_ids"]
    )
    assert observable_packet[
        "selected_ccft_empirical_discriminator_observable_candidate_platform_binding"
    ] == "controlled_mesoscopic_coherence_platform_candidate"
    assert observable_packet[
        "selected_ccft_empirical_discriminator_observable_baseline_binding"
    ] == "standard_open_system_decoherence_baseline_comparison"
    assert observable_packet[
        "selected_ccft_empirical_discriminator_observable_tolerance_binding"
    ] == "TOL-CCFT-MESO-COH-LIFETIME-RESIDUAL-v0"
    assert observable_packet[
        "selected_ccft_empirical_discriminator_observable_null_default"
    ] == "null_separation_from_baseline_with_registered_tolerances"
    assert (
        observable_packet["selected_ccft_empirical_discriminator_observable_execution_status"]
        == "not_executed"
    )
    assert observable_packet["observable_definition_semantics_packet_prepared"] == "yes"
    assert observable_packet["observable_definition_semantics_rows_registered"] == "yes"
    assert observable_packet["observable_semantics_meaning_only"] == "yes"
    assert observable_packet["observable_defined_as_future_comparison_object"] == "yes"
    assert observable_packet["comparison_direction_resolved"] == "no"
    assert observable_packet["observed_empirical_residual_claimed"] == "no"
    assert observable_packet["ccft_predicted_residual_claimed"] == "no"
    assert observable_packet["statistically_significant_deviation_claimed"] == "no"
    assert observable_packet["measurement_protocol_defined"] == "no"
    assert observable_packet["validated_discriminator_claimed"] == "no"
    assert observable_packet["coherence_lifetime_baseline_separation_claimed"] == "no"
    _assert_registry_nonclaims(observable_packet)

    observable_review = workstream(OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_TARGET, payload)
    assert observable_review["status"] == "paused"
    assert (
        observable_review["review_result"]
        == STAGES["observable_definition_semantics_review"].outcome_id
    )
    assert (
        observable_review["strict_review_result"]
        == STAGES["observable_definition_semantics_review"].strict_outcome_id
    )
    assert observable_review["prepared_packet_result"] == (
        STAGES["observable_definition_semantics_packet"].outcome_id
    )
    assert observable_review["prepared_packet_strict_result"] == (
        STAGES["observable_definition_semantics_packet"].strict_outcome_id
    )
    assert (
        observable_review["selected_next_target"]
        == RESIDUAL_FORMULA_SELECTION_PACKET_TARGET
    )
    assert observable_review["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_residual_formula_selection_packet"
    )
    assert (
        observable_review[
            "selected_ccft_empirical_discriminator_observable_definition_semantics_review_acceptance_item_count"
        ]
        == 35
    )
    assert "residual formula remains unselected" in (
        observable_review[
            "selected_ccft_empirical_discriminator_observable_definition_semantics_review_acceptance_items"
        ]
    )
    assert "measurement protocol readiness not accepted" in (
        observable_review[
            "selected_ccft_empirical_discriminator_observable_definition_semantics_review_acceptance_items"
        ]
    )
    assert (
        observable_review[
            "observable_definition_semantics_packet_accepted_as_meaning_only"
        ]
        == "yes"
    )
    assert (
        observable_review[
            "observable_definition_semantics_rows_accepted_as_non_executed_only"
        ]
        == "yes"
    )
    assert (
        observable_review[
            "coherence_lifetime_residual_candidate_accepted_as_future_comparison_object_only"
        ]
        == "yes"
    )
    assert (
        observable_review[
            "registered_tolerance_binding_retained_as_traceability_only"
        ]
        == "yes"
    )
    assert observable_review["residual_formula_selected"] == "no"
    assert observable_review["residual_formula_selection_required_before_protocol"] == (
        "yes"
    )
    assert observable_review["observed_residual_accepted"] == "no"
    assert observable_review["ccft_predicted_residual_accepted"] == "no"
    assert observable_review["statistical_effect_size_accepted"] == "no"
    assert observable_review["measured_coherence_anomaly_accepted"] == "no"
    assert observable_review["baseline_separation_accepted"] == "no"
    assert observable_review["measurement_protocol_readiness_accepted"] == "no"
    assert observable_review["empirical_confirmation_accepted"] == "no"
    assert (
        observable_review["selected_next_planning_packet_target"]
        == RESIDUAL_FORMULA_SELECTION_PACKET_TARGET
    )
    _assert_registry_nonclaims(observable_review)

    residual_packet = workstream(RESIDUAL_FORMULA_SELECTION_PACKET_TARGET, payload)
    assert residual_packet["status"] == "paused"
    assert (
        residual_packet["packet_result"]
        == STAGES["residual_formula_selection_packet"].outcome_id
    )
    assert (
        residual_packet["strict_packet_result"]
        == STAGES["residual_formula_selection_packet"].strict_outcome_id
    )
    assert (
        residual_packet["selected_next_target"]
        == RESIDUAL_FORMULA_SELECTION_REVIEW_TARGET
    )
    assert residual_packet["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_residual_formula_selection_packet_result_review"
    )
    assert (
        residual_packet[
            "observable_definition_semantics_result_review_consumed"
        ]
        == "yes"
    )
    assert residual_packet["observable_definition_semantics_review_result"] == (
        STAGES["observable_definition_semantics_review"].outcome_id
    )
    assert (
        residual_packet[
            "observable_definition_semantics_review_strict_result"
        ]
        == STAGES["observable_definition_semantics_review"].strict_outcome_id
    )
    assert (
        residual_packet[
            "selected_ccft_empirical_discriminator_residual_formula_selection_field_count"
        ]
        == 7
    )
    assert (
        residual_packet[
            "selected_ccft_empirical_discriminator_residual_formula_selection_row_count"
        ]
        == 5
    )
    assert "normalized_lifetime_residual" in (
        residual_packet["selected_ccft_empirical_discriminator_residual_formula_ids"]
    )
    assert residual_packet["selected_primary_residual_formula_id"] == (
        "normalized_lifetime_residual"
    )
    assert residual_packet["selected_primary_residual_formula"] == (
        "r_tau = (tau_candidate - tau_baseline) / tau_baseline"
    )
    assert residual_packet["normalized_lifetime_residual_selected_primary"] == "yes"
    assert residual_packet["absolute_lifetime_difference_selected_primary"] == "no"
    assert residual_packet["lifetime_ratio_selected_primary"] == "no"
    assert residual_packet["decay_rate_difference_selected_primary"] == "no"
    assert (
        residual_packet["decay_rate_difference_retained_for_later_comparison"]
        == "yes"
    )
    assert residual_packet["log_lifetime_ratio_selected_primary"] == "no"
    assert residual_packet["residual_formula_selection_packet_prepared"] == "yes"
    assert residual_packet["residual_formula_candidate_forms_compared"] == "yes"
    assert residual_packet["residual_formula_selected"] == "yes"
    assert residual_packet["residual_formula_selection_only"] == "yes"
    assert residual_packet["formula_selected_for_future_comparison_use_only"] == "yes"
    assert residual_packet["residual_formula_execution_status"] == "not_executed"
    assert (
        residual_packet[
            "selected_ccft_empirical_discriminator_residual_formula_selection_item_count"
        ]
        == 36
    )
    assert "normalized lifetime residual selected as primary future comparison formula" in (
        residual_packet[
            "selected_ccft_empirical_discriminator_residual_formula_selection_items"
        ]
    )
    assert residual_packet["observed_residual_accepted"] == "no"
    assert residual_packet["ccft_predicted_residual_accepted"] == "no"
    assert residual_packet["statistical_effect_size_accepted"] == "no"
    assert residual_packet["measured_coherence_anomaly_accepted"] == "no"
    assert residual_packet["baseline_separation_accepted"] == "no"
    assert residual_packet["measurement_protocol_readiness_accepted"] == "no"
    assert residual_packet["empirical_confirmation_accepted"] == "no"
    assert residual_packet["measurement_protocol_defined"] == "no"
    assert residual_packet["statistical_validation_claimed"] == "no"
    assert (
        residual_packet["selected_next_planning_packet_target"]
        == RESIDUAL_FORMULA_SELECTION_REVIEW_TARGET
    )
    _assert_registry_nonclaims(residual_packet)

    residual_review = workstream(RESIDUAL_FORMULA_SELECTION_REVIEW_TARGET, payload)
    assert residual_review["status"] == "paused"
    assert residual_review["authorization_evidence"] == (
        RESIDUAL_FORMULA_SELECTION_REVIEW_EVIDENCE
    )
    assert residual_review["report"] == RESIDUAL_FORMULA_SELECTION_REVIEW_REPORT
    assert residual_review["review_result"] == (
        STAGES["residual_formula_selection_review"].outcome_id
    )
    assert residual_review["strict_review_result"] == (
        STAGES["residual_formula_selection_review"].strict_outcome_id
    )
    assert (
        residual_review["selected_next_target"]
        == MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_TARGET
    )
    assert residual_review["selected_next_target_kind"] == (
        RESIDUAL_FORMULA_SELECTION_REVIEW_KIND
    )
    assert residual_review["prepared_packet_result"] == (
        STAGES["residual_formula_selection_packet"].outcome_id
    )
    assert residual_review["prepared_packet_strict_result"] == (
        STAGES["residual_formula_selection_packet"].strict_outcome_id
    )
    assert (
        residual_review["residual_formula_selection_packet_accepted"]
        == "yes"
    )
    assert (
        residual_review["tau_baseline_positive_nonzero_precondition_recorded"]
        == "yes"
    )
    assert residual_review["tau_candidate_observed_value_accepted"] == "no"
    assert residual_review["tau_candidate_ccft_derived_prediction_accepted"] == "no"
    assert residual_review["r_tau_dimensionless"] == "yes"
    assert (
        residual_review[
            "r_tau_zero_means_no_lifetime_separation_if_later_measured_or_derived"
        ]
        == "yes"
    )
    assert (
        residual_review[
            "r_tau_positive_means_longer_candidate_lifetime_if_later_measured_or_derived"
        ]
        == "yes"
    )
    assert (
        residual_review[
            "r_tau_negative_means_shorter_candidate_lifetime_if_later_measured_or_derived"
        ]
        == "yes"
    )
    assert residual_review["r_tau_sign_semantics_count_as_current_evidence"] == "no"
    assert (
        residual_review["external_source_treated_as_baseline_pressure_only"]
        == "yes"
    )
    assert residual_review["external_source_treated_as_ccft_validation"] == "no"
    assert residual_review["external_source_treated_as_toe_truth_claim"] == "no"
    assert (
        residual_review["measurement_feedback_baseline_pressure_source"]["arxiv_id"]
        == "2503.13615"
    )
    assert (
        "feedback Hamiltonian control"
        in residual_review["measurement_feedback_baseline_pressure_components"]
    )
    _assert_registry_nonclaims(residual_review)

    measurement_packet = workstream(
        MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_TARGET, payload
    )
    assert measurement_packet["status"] == "paused"
    assert measurement_packet["authorization_evidence"] == (
        MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_EVIDENCE
    )
    assert measurement_packet["report"] == (
        MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_REPORT
    )
    assert measurement_packet["packet_result"] == (
        STAGES["measurement_feedback_baseline_pressure_packet"].outcome_id
    )
    assert measurement_packet["strict_packet_result"] == (
        STAGES["measurement_feedback_baseline_pressure_packet"].strict_outcome_id
    )
    assert (
        measurement_packet["selected_next_target"]
        == MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_TARGET
    )
    assert measurement_packet["selected_next_target_kind"] == (
        MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_KIND
    )
    assert (
        measurement_packet["residual_formula_selection_result_review_consumed"]
        == "yes"
    )
    assert measurement_packet["residual_formula_selection_review_result"] == (
        STAGES["residual_formula_selection_review"].outcome_id
    )
    assert (
        measurement_packet["residual_formula_selection_review_strict_result"]
        == STAGES["residual_formula_selection_review"].strict_outcome_id
    )
    assert measurement_packet["measurement_feedback_baseline_pressure_only"] == "yes"
    assert (
        measurement_packet["measurement_feedback_baseline_pressure_row_count"]
        == 8
    )
    assert (
        measurement_packet["measurement_feedback_baseline_pressure_component_count"]
        == 8
    )
    assert (
        measurement_packet["measurement_feedback_baseline_pressure_source"][
            "arxiv_id"
        ]
        == "2503.13615"
    )
    assert (
        "feedback Hamiltonian control"
        in measurement_packet["measurement_feedback_baseline_pressure_components"]
    )
    assert (
        "quantum thermodynamic accounting"
        in measurement_packet["future_tau_baseline_components"]
    )
    assert (
        measurement_packet["external_source_treated_as_baseline_pressure_only"]
        == "yes"
    )
    assert measurement_packet["external_source_treated_as_toe_evidence"] == "no"
    assert measurement_packet["external_source_treated_as_ccft_evidence"] == "no"
    assert (
        measurement_packet["external_source_treated_as_empirical_validation"]
        == "no"
    )
    assert (
        measurement_packet["external_source_treated_as_master_action_support"]
        == "no"
    )
    assert (
        measurement_packet[
            "future_tau_baseline_must_include_measurement_feedback_effects"
        ]
        == "yes"
    )
    assert (
        measurement_packet[
            "future_residual_claims_must_beat_measurement_feedback_baseline"
        ]
        == "yes"
    )
    assert (
        measurement_packet["residual_formula_changed_by_baseline_pressure_packet"]
        == "no"
    )
    _assert_registry_nonclaims(measurement_packet)

    measurement_review = workstream(
        MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_TARGET, payload
    )
    assert measurement_review["status"] == "paused"
    assert (
        measurement_review["authorization_evidence"]
        == MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_EVIDENCE
    )
    assert (
        measurement_review["report"]
        == MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_REPORT
    )
    assert measurement_review["review_result"] == (
        STAGES["measurement_feedback_baseline_pressure_review"].outcome_id
    )
    assert measurement_review["strict_review_result"] == (
        STAGES["measurement_feedback_baseline_pressure_review"].strict_outcome_id
    )
    assert measurement_review["prepared_packet_result"] == (
        STAGES["measurement_feedback_baseline_pressure_packet"].outcome_id
    )
    assert measurement_review["prepared_packet_strict_result"] == (
        STAGES["measurement_feedback_baseline_pressure_packet"].strict_outcome_id
    )
    assert (
        measurement_review["selected_next_target"]
        == BASELINE_COMPONENT_REGISTRY_PACKET_TARGET
    )
    assert (
        measurement_review["selected_next_target_kind"]
        == BASELINE_COMPONENT_REGISTRY_PACKET_KIND
    )
    assert (
        measurement_review[
            "measurement_feedback_baseline_pressure_packet_accepted_as_baseline_hardening_only"
        ]
        == "yes"
    )
    assert (
        measurement_review[
            "arxiv_2503_13615_accepted_as_literature_baseline_pressure_only"
        ]
        == "yes"
    )
    assert measurement_review["external_source_treated_as_toe_evidence"] == "no"
    assert measurement_review["external_source_treated_as_ccft_evidence"] == "no"
    assert (
        measurement_review["external_source_treated_as_observed_residual_evidence"]
        == "no"
    )
    assert measurement_review["external_source_treated_as_baseline_separation"] == (
        "no"
    )
    assert measurement_review["external_source_treated_as_protocol_readiness"] == (
        "no"
    )
    assert (
        measurement_review["external_source_treated_as_statistical_validation"]
        == "no"
    )
    assert (
        measurement_review["external_source_treated_as_master_action_support"]
        == "no"
    )
    assert measurement_review["future_baseline_component_registry_selected"] == (
        "yes"
    )
    assert (
        measurement_review["residual_formula_changed_by_baseline_pressure_review"]
        == "no"
    )
    _assert_registry_nonclaims(measurement_review)

    baseline_packet = workstream(BASELINE_COMPONENT_REGISTRY_PACKET_TARGET, payload)
    assert baseline_packet["status"] == "paused"
    assert baseline_packet["authorization_evidence"] == (
        BASELINE_COMPONENT_REGISTRY_PACKET_EVIDENCE
    )
    assert baseline_packet["report"] == BASELINE_COMPONENT_REGISTRY_PACKET_REPORT
    assert baseline_packet["packet_result"] == (
        STAGES["baseline_component_registry_packet"].outcome_id
    )
    assert baseline_packet["strict_packet_result"] == (
        STAGES["baseline_component_registry_packet"].strict_outcome_id
    )
    assert baseline_packet["selected_next_target"] == (
        BASELINE_COMPONENT_REGISTRY_REVIEW_TARGET
    )
    assert baseline_packet["selected_next_target_kind"] == (
        BASELINE_COMPONENT_REGISTRY_REVIEW_KIND
    )
    assert (
        baseline_packet["measurement_feedback_baseline_pressure_result_review_consumed"]
        == "yes"
    )
    assert baseline_packet["baseline_component_registry_packet_prepared"] == "yes"
    assert baseline_packet["baseline_component_registry_traceability_only"] == "yes"
    assert baseline_packet["tau_baseline_component_registry_prepared"] == "yes"
    assert baseline_packet["tau_baseline_future_comparison_baseline_only"] == "yes"
    assert baseline_packet["tau_baseline_value_computed"] == "no"
    assert baseline_packet["tau_baseline_completed_model_claimed"] == "no"
    assert baseline_packet["baseline_component_completeness_claimed"] == "no"
    assert baseline_packet["baseline_component_registry_row_count"] == 8
    assert baseline_packet["registered_tau_baseline_component_count"] == 8
    assert (
        "feedback Hamiltonian control"
        in baseline_packet["registered_tau_baseline_components"]
    )
    assert (
        "thermodynamic and energy accounting"
        in baseline_packet["registered_tau_baseline_components"]
    )
    assert (
        baseline_packet["residual_formula_changed_by_baseline_component_registry"]
        == "no"
    )
    assert baseline_packet["selected_primary_residual_formula"] == (
        "r_tau = (tau_candidate - tau_baseline) / tau_baseline"
    )
    _assert_registry_nonclaims(baseline_packet)

    baseline_review = workstream(BASELINE_COMPONENT_REGISTRY_REVIEW_TARGET, payload)
    assert baseline_review["status"] == "paused"
    assert baseline_review["authorization_evidence"] == (
        BASELINE_COMPONENT_REGISTRY_REVIEW_EVIDENCE
    )
    assert baseline_review["report"] == BASELINE_COMPONENT_REGISTRY_REVIEW_REPORT
    assert baseline_review["review_result"] == (
        STAGES["baseline_component_registry_review"].outcome_id
    )
    assert baseline_review["strict_review_result"] == (
        STAGES["baseline_component_registry_review"].strict_outcome_id
    )
    assert baseline_review["prepared_packet_result"] == (
        STAGES["baseline_component_registry_packet"].outcome_id
    )
    assert baseline_review["prepared_packet_strict_result"] == (
        STAGES["baseline_component_registry_packet"].strict_outcome_id
    )
    assert baseline_review["selected_next_target"] == (
        BASELINE_COMPONENT_INTERACTION_RISK_PACKET_TARGET
    )
    assert baseline_review["selected_next_target_kind"] == (
        BASELINE_COMPONENT_INTERACTION_RISK_KIND
    )
    assert (
        baseline_review["baseline_component_registry_packet_result_review_consumed"]
        == "yes"
    )
    assert baseline_review["baseline_component_registry_packet_accepted"] == "yes"
    assert (
        baseline_review["baseline_component_registry_packet_accepted_as_traceability_only"]
        == "yes"
    )
    assert (
        baseline_review[
            "future_tau_baseline_component_traceability_only_accepted"
        ]
        == "yes"
    )
    assert baseline_review["tau_baseline_value_computation_accepted"] == "no"
    assert baseline_review["tau_baseline_completed_model_accepted"] == "no"
    assert baseline_review["baseline_component_completeness_accepted"] == "no"
    assert baseline_review["baseline_component_independence_claimed"] == "no"
    assert baseline_review["baseline_component_interaction_risks_preserved"] == "yes"
    assert baseline_review["baseline_component_interaction_risk_packet_selected"] == (
        "yes"
    )
    assert (
        baseline_review[
            "measurement_back_action_detector_efficiency_feedback_delay_control_coupling_risk_recorded"
        ]
        == "yes"
    )
    assert baseline_review["registered_tau_baseline_component_count"] == 8
    assert (
        baseline_review["residual_formula_changed_by_baseline_component_registry_review"]
        == "no"
    )
    _assert_registry_nonclaims(baseline_review)

    interaction_packet = workstream(
        BASELINE_COMPONENT_INTERACTION_RISK_PACKET_TARGET, payload
    )
    assert interaction_packet["status"] == "paused"
    assert interaction_packet["active_lane"] == (
        BASELINE_COMPONENT_INTERACTION_RISK_PACKET_TARGET
    )
    assert interaction_packet["authorization_evidence"] == (
        BASELINE_COMPONENT_INTERACTION_RISK_PACKET_EVIDENCE
    )
    assert interaction_packet["report"] == (
        BASELINE_COMPONENT_INTERACTION_RISK_PACKET_REPORT
    )
    assert interaction_packet["packet_result"] == (
        STAGES["baseline_component_interaction_risk_packet"].outcome_id
    )
    assert interaction_packet["strict_packet_result"] == (
        STAGES["baseline_component_interaction_risk_packet"].strict_outcome_id
    )
    assert interaction_packet["consumed_target"] == (
        BASELINE_COMPONENT_INTERACTION_RISK_PACKET_TARGET
    )
    assert interaction_packet["consumed_target_kind"] == (
        BASELINE_COMPONENT_INTERACTION_RISK_KIND
    )
    assert (
        interaction_packet["selected_next_target"]
        == BASELINE_COMPONENT_INTERACTION_RISK_REVIEW_TARGET
    )
    assert interaction_packet["selected_next_target_kind"] == (
        BASELINE_COMPONENT_INTERACTION_RISK_REVIEW_KIND
    )
    assert (
        interaction_packet["baseline_component_registry_result_review_consumed"]
        == "yes"
    )
    assert interaction_packet["baseline_component_interaction_risk_traceability_only"] == (
        "yes"
    )
    assert interaction_packet["tau_baseline_component_interaction_risks_mapped"] == (
        "yes"
    )
    assert (
        interaction_packet["interaction_risks_recorded_as_baseline_warnings_only"]
        == "yes"
    )
    assert interaction_packet["baseline_component_interaction_risk_id_count"] == 8
    assert "measurement_back_action_coupling" in (
        interaction_packet["baseline_component_interaction_risk_ids"]
    )
    assert "delay_energy_accounting_coupling" in (
        interaction_packet["baseline_component_interaction_risk_ids"]
    )
    assert interaction_packet["component_independence_claimed"] == "no"
    assert interaction_packet["baseline_component_independence_claimed"] == "no"
    assert interaction_packet["interaction_model_completed"] == "no"
    assert interaction_packet["interaction_coupling_terms_computed"] == "no"
    assert interaction_packet["baseline_model_completed"] == "no"
    assert (
        interaction_packet["residual_formula_changed_by_interaction_risk_packet"]
        == "no"
    )
    _assert_registry_nonclaims(interaction_packet)

    interaction_review = workstream(BASELINE_COMPONENT_INTERACTION_RISK_REVIEW_TARGET, payload)
    assert interaction_review["status"] == "paused"
    assert interaction_review["active_lane"] == (
        BASELINE_COMPONENT_INTERACTION_RISK_REVIEW_TARGET
    )
    assert interaction_review["authorization_evidence"] == (
        BASELINE_COMPONENT_INTERACTION_RISK_REVIEW_EVIDENCE
    )
    assert interaction_review["report"] == (
        BASELINE_COMPONENT_INTERACTION_RISK_REVIEW_REPORT
    )
    assert interaction_review["review_result"] == (
        STAGES["baseline_component_interaction_risk_review"].outcome_id
    )
    assert interaction_review["strict_review_result"] == (
        STAGES["baseline_component_interaction_risk_review"].strict_outcome_id
    )
    assert interaction_review["prepared_packet_result"] == (
        STAGES["baseline_component_interaction_risk_packet"].outcome_id
    )
    assert interaction_review["prepared_packet_strict_result"] == (
        STAGES["baseline_component_interaction_risk_packet"].strict_outcome_id
    )
    assert interaction_review["consumed_target"] == (
        BASELINE_COMPONENT_INTERACTION_RISK_REVIEW_TARGET
    )
    assert interaction_review["consumed_target_kind"] == (
        BASELINE_COMPONENT_INTERACTION_RISK_REVIEW_KIND
    )
    assert interaction_review["selected_next_target"] == (
        BASELINE_CONSTRUCTION_OBLIGATION_PACKET_TARGET
    )
    assert interaction_review["selected_next_target_kind"] == (
        BASELINE_CONSTRUCTION_OBLIGATION_KIND
    )
    assert (
        interaction_review[
            "baseline_component_interaction_risk_packet_result_review_consumed"
        ]
        == "yes"
    )
    assert (
        interaction_review[
            "interaction_risk_map_accepted_as_traceability_only"
        ]
        == "yes"
    )
    assert (
        interaction_review[
            "tau_baseline_component_interaction_risk_traceability_only_accepted"
        ]
        == "yes"
    )
    assert (
        interaction_review[
            "eight_interaction_risk_rows_accepted_as_baseline_warnings_only"
        ]
        == "yes"
    )
    assert interaction_review["component_independence_claim_accepted"] == "no"
    assert interaction_review["baseline_completeness_claim_accepted"] == "no"
    assert interaction_review["interaction_model_accepted"] == "no"
    assert interaction_review["tau_baseline_value_computation_accepted"] == "no"
    assert interaction_review["baseline_construction_obligation_packet_selected"] == (
        "yes"
    )
    _assert_registry_nonclaims(interaction_review)

    construction_packet = workstream(
        BASELINE_CONSTRUCTION_OBLIGATION_PACKET_TARGET, payload
    )
    assert construction_packet["status"] == "paused"
    assert (
        construction_packet["active_lane"]
        == BASELINE_CONSTRUCTION_OBLIGATION_PACKET_TARGET
    )
    assert construction_packet["authorization_evidence"] == _rel(
        lean_path(STAGES["baseline_construction_obligation_packet"])
    )
    assert construction_packet["report"] == _rel(
        release_path(STAGES["baseline_construction_obligation_packet"])
    )
    assert construction_packet["packet_result"] == (
        STAGES["baseline_construction_obligation_packet"].outcome_id
    )
    assert construction_packet["strict_packet_result"] == (
        STAGES["baseline_construction_obligation_packet"].strict_outcome_id
    )
    assert construction_packet["consumed_target"] == (
        BASELINE_CONSTRUCTION_OBLIGATION_PACKET_TARGET
    )
    assert construction_packet["consumed_target_kind"] == (
        BASELINE_CONSTRUCTION_OBLIGATION_KIND
    )
    assert (
        construction_packet["selected_next_target"]
        == BASELINE_CONSTRUCTION_OBLIGATION_REVIEW_TARGET
    )
    assert construction_packet["selected_next_target_kind"] == (
        BASELINE_CONSTRUCTION_OBLIGATION_REVIEW_KIND
    )
    assert construction_packet[
        "baseline_component_interaction_risk_result_review_consumed"
    ] == "yes"
    assert construction_packet["baseline_construction_obligation_index_only"] == (
        "yes"
    )
    assert construction_packet["tau_baseline_construction_requirements_listed"] == (
        "yes"
    )
    assert construction_packet["baseline_construction_obligation_row_count"] == 8
    assert "TBASE-OBL-COMPONENT-EQUATIONS-v0" in construction_packet[
        "baseline_construction_obligation_ids"
    ]
    assert "TBASE-OBL-UNCERTAINTY-HANDLING-v0" in construction_packet[
        "baseline_construction_obligation_ids"
    ]
    assert construction_packet["component_equations_obligation_recorded"] == "yes"
    assert construction_packet["coupling_assumptions_obligation_recorded"] == "yes"
    assert (
        construction_packet["independence_dependence_rules_obligation_recorded"]
        == "yes"
    )
    assert construction_packet["units_dimensions_obligation_recorded"] == "yes"
    assert construction_packet["parameter_sources_obligation_recorded"] == "yes"
    assert construction_packet["uncertainty_handling_obligation_recorded"] == "yes"
    assert (
        construction_packet["boundary_initial_conditions_obligation_recorded"]
        == "yes"
    )
    assert construction_packet["review_failure_gates_obligation_recorded"] == "yes"
    assert construction_packet["tau_baseline_construction_allowed"] == "no"
    assert construction_packet["tau_baseline_value_computed"] == "no"
    assert construction_packet["tau_baseline_completed_model_claimed"] == "no"
    assert construction_packet["baseline_model_completed"] == "no"
    assert construction_packet["component_equations_specified"] == "no"
    assert construction_packet["coupling_assumptions_specified"] == "no"
    assert construction_packet["independence_dependence_rules_specified"] == "no"
    assert construction_packet["parameter_sources_specified"] == "no"
    assert construction_packet["uncertainty_handling_specified"] == "no"
    assert construction_packet["boundary_initial_conditions_specified"] == "no"
    _assert_registry_nonclaims(construction_packet)

    construction_review = workstream(BASELINE_CONSTRUCTION_OBLIGATION_REVIEW_TARGET, payload)
    assert construction_review["status"] == "paused"
    assert construction_review["active_lane"] == BASELINE_CONSTRUCTION_OBLIGATION_REVIEW_TARGET
    assert construction_review["authorization_evidence"] == _rel(
        lean_path(STAGES["baseline_construction_obligation_review"])
    )
    assert construction_review["report"] == _rel(
        release_path(STAGES["baseline_construction_obligation_review"])
    )
    assert construction_review["review_result"] == (
        STAGES["baseline_construction_obligation_review"].outcome_id
    )
    assert construction_review["strict_review_result"] == (
        STAGES["baseline_construction_obligation_review"].strict_outcome_id
    )
    assert construction_review["prepared_packet_result"] == (
        STAGES["baseline_construction_obligation_packet"].outcome_id
    )
    assert construction_review["prepared_packet_strict_result"] == (
        STAGES["baseline_construction_obligation_packet"].strict_outcome_id
    )
    assert (
        construction_review["consumed_target"]
        == BASELINE_CONSTRUCTION_OBLIGATION_REVIEW_TARGET
    )
    assert construction_review["consumed_target_kind"] == (
        BASELINE_CONSTRUCTION_OBLIGATION_REVIEW_KIND
    )
    assert (
        construction_review["selected_next_target"]
        == BASELINE_COMPONENT_EQUATION_SCAFFOLD_TARGET
    )
    assert construction_review["selected_next_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SCAFFOLD_KIND
    )
    assert construction_review[
        "baseline_construction_obligation_packet_result_review_consumed"
    ] == "yes"
    assert (
        construction_review[
            "baseline_construction_obligation_packet_accepted_as_index_only"
        ]
        == "yes"
    )
    assert (
        construction_review["tau_baseline_construction_requirements_index_accepted"]
        == "yes"
    )
    assert construction_review["component_equations_obligation_accepted"] == "yes"
    assert construction_review["coupling_assumptions_obligation_accepted"] == "yes"
    assert (
        construction_review["independence_dependence_rules_obligation_accepted"]
        == "yes"
    )
    assert construction_review["uncertainty_handling_obligation_accepted"] == "yes"
    assert (
        construction_review["baseline_component_equation_scaffold_packet_selected"]
        == "yes"
    )
    assert construction_review["tau_baseline_construction_allowed"] == "no"
    assert construction_review["tau_baseline_value_computation_accepted"] == "no"
    assert construction_review["baseline_model_accepted"] == "no"
    assert construction_review["component_equations_accepted_as_specified"] == "no"
    assert construction_review["measurement_protocol_readiness_accepted"] == "no"
    assert construction_review["statistical_validation_accepted"] == "no"
    assert construction_review["ccft_validation_accepted"] == "no"
    assert construction_review["master_action_support_accepted"] == "no"
    _assert_registry_nonclaims(construction_review)

    scaffold_packet = workstream(BASELINE_COMPONENT_EQUATION_SCAFFOLD_TARGET, payload)
    assert scaffold_packet["status"] == "paused"
    assert scaffold_packet["active_lane"] == BASELINE_COMPONENT_EQUATION_SCAFFOLD_TARGET
    assert (
        scaffold_packet["authorization_evidence"]
        == BASELINE_COMPONENT_EQUATION_SCAFFOLD_PACKET_EVIDENCE
    )
    assert scaffold_packet["report"] == BASELINE_COMPONENT_EQUATION_SCAFFOLD_PACKET_REPORT
    assert scaffold_packet["packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SCAFFOLD_PACKET_OUTCOME
    )
    assert scaffold_packet["strict_packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SCAFFOLD_PACKET_STRICT_OUTCOME
    )
    assert scaffold_packet["consumed_target"] == BASELINE_COMPONENT_EQUATION_SCAFFOLD_TARGET
    assert scaffold_packet["consumed_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SCAFFOLD_KIND
    )
    assert scaffold_packet["selected_next_target"] == (
        BASELINE_COMPONENT_EQUATION_SCAFFOLD_REVIEW_TARGET
    )
    assert scaffold_packet["selected_next_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SCAFFOLD_REVIEW_KIND
    )
    assert scaffold_packet["baseline_component_equation_scaffold_packet_prepared"] == (
        "yes"
    )
    assert scaffold_packet["baseline_component_equation_scaffold_only"] == "yes"
    assert scaffold_packet["tau_baseline_component_equation_slots_defined"] == "yes"
    assert scaffold_packet["component_equation_slots_defined_only"] == "yes"
    assert scaffold_packet["baseline_component_equation_scaffold_row_count"] == 8
    assert scaffold_packet["baseline_component_equation_scaffold_field_count"] == 7
    assert scaffold_packet["baseline_component_equation_scaffold_item_count"] == 20
    for slot_id in (
        "TBASE-EQ-SLOT-OPEN-SYSTEM-DECOHERENCE-v0",
        "TBASE-EQ-SLOT-MEASUREMENT-CONTRIBUTION-v0",
        "TBASE-EQ-SLOT-BACK-ACTION-CONTRIBUTION-v0",
        "TBASE-EQ-SLOT-FEEDBACK-HAMILTONIAN-CONTROL-v0",
        "TBASE-EQ-SLOT-DETECTOR-EFFICIENCY-CORRECTION-v0",
        "TBASE-EQ-SLOT-FEEDBACK-DELAY-CORRECTION-v0",
        "TBASE-EQ-SLOT-CONTROL-FIELD-EFFECT-v0",
        "TBASE-EQ-SLOT-THERMODYNAMIC-ENERGY-ACCOUNTING-v0",
    ):
        assert slot_id in scaffold_packet["baseline_component_equation_scaffold_slot_ids"]
    for role in (
        "open-system decoherence equation slot",
        "measurement contribution equation slot",
        "back-action contribution equation slot",
        "feedback Hamiltonian control equation slot",
        "detector efficiency correction slot",
        "feedback delay correction slot",
        "control-field effect slot",
        "thermodynamic / energy accounting slot",
    ):
        assert role in scaffold_packet["baseline_component_equation_scaffold_slot_roles"]
    assert scaffold_packet["open_system_decoherence_equation_slot_defined"] == "yes"
    assert scaffold_packet["measurement_contribution_equation_slot_defined"] == "yes"
    assert scaffold_packet["back_action_contribution_equation_slot_defined"] == "yes"
    assert scaffold_packet["feedback_hamiltonian_control_equation_slot_defined"] == (
        "yes"
    )
    assert scaffold_packet["detector_efficiency_correction_slot_defined"] == "yes"
    assert scaffold_packet["feedback_delay_correction_slot_defined"] == "yes"
    assert scaffold_packet["control_field_effect_slot_defined"] == "yes"
    assert scaffold_packet["thermodynamic_energy_accounting_slot_defined"] == "yes"
    assert scaffold_packet["component_equations_specified"] == "no"
    assert scaffold_packet["component_equations_selected"] == "no"
    assert scaffold_packet["component_equations_correctness_claimed"] == "no"
    assert scaffold_packet["component_equations_physical_adequacy_claimed"] == "no"
    assert scaffold_packet["component_equation_independence_claimed"] == "no"
    assert scaffold_packet["tau_baseline_value_computed"] == "no"
    assert scaffold_packet["baseline_model_completed"] == "no"
    assert scaffold_packet["measurement_protocol_defined"] == "no"
    assert scaffold_packet["statistical_validation_claimed"] == "no"
    assert scaffold_packet["residual_separation_claimed"] == "no"
    assert scaffold_packet["ccft_validation_accepted"] == "no"
    assert scaffold_packet["master_action_promoted"] == "no"
    _assert_registry_nonclaims(scaffold_packet)

    scaffold_review = workstream(
        BASELINE_COMPONENT_EQUATION_SCAFFOLD_REVIEW_TARGET, payload
    )
    assert scaffold_review["status"] == "paused"
    assert scaffold_review["active_lane"] == (
        BASELINE_COMPONENT_EQUATION_SCAFFOLD_REVIEW_TARGET
    )
    assert scaffold_review["authorization_evidence"] == _rel(
        lean_path(STAGES["baseline_component_equation_scaffold_review"])
    )
    assert scaffold_review["report"] == _rel(
        release_path(STAGES["baseline_component_equation_scaffold_review"])
    )
    assert scaffold_review["packet_result"] == (
        STAGES["baseline_component_equation_scaffold_review"].outcome_id
    )
    assert scaffold_review["strict_packet_result"] == (
        STAGES["baseline_component_equation_scaffold_review"].strict_outcome_id
    )
    assert scaffold_review["review_result"] == (
        STAGES["baseline_component_equation_scaffold_review"].outcome_id
    )
    assert scaffold_review["strict_review_result"] == (
        STAGES["baseline_component_equation_scaffold_review"].strict_outcome_id
    )
    assert scaffold_review["prepared_packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SCAFFOLD_PACKET_OUTCOME
    )
    assert scaffold_review["prepared_packet_strict_result"] == (
        BASELINE_COMPONENT_EQUATION_SCAFFOLD_PACKET_STRICT_OUTCOME
    )
    assert scaffold_review["consumed_target"] == (
        BASELINE_COMPONENT_EQUATION_SCAFFOLD_REVIEW_TARGET
    )
    assert scaffold_review["consumed_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SCAFFOLD_REVIEW_KIND
    )
    assert scaffold_review["selected_next_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_TARGET
    )
    assert scaffold_review["selected_next_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_KIND
    )
    assert (
        scaffold_review[
            "baseline_component_equation_scaffold_packet_result_review_consumed"
        ]
        == "yes"
    )
    assert (
        scaffold_review[
            "baseline_component_equation_scaffold_packet_accepted_as_equation_slots_only"
        ]
        == "yes"
    )
    assert scaffold_review["tau_baseline_equation_slots_accepted"] == "yes"
    assert scaffold_review["component_equation_slots_accepted_only"] == "yes"
    assert scaffold_review["equation_slot_adequacy_claimed"] == "no"
    assert scaffold_review["equation_slot_adequacy_accepted"] == "no"
    assert scaffold_review["component_equation_correctness_accepted"] == "no"
    assert scaffold_review["component_equation_independence_claimed"] == "no"
    assert scaffold_review["component_equation_independence_accepted"] == "no"
    assert (
        scaffold_review["baseline_component_equation_slot_completeness_claimed"]
        == "no"
    )
    assert (
        scaffold_review["baseline_component_equation_slot_completeness_accepted"]
        == "no"
    )
    assert scaffold_review["eight_equation_slots_complete_claimed"] == "no"
    assert (
        scaffold_review[
            "baseline_component_equation_source_classification_packet_selected"
        ]
        == "yes"
    )
    assert scaffold_review["next_source_classification_packet_required"] == "yes"
    _assert_registry_nonclaims(scaffold_review)

    source_packet = workstream(
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_TARGET, payload
    )
    assert source_packet["status"] == "paused"
    assert source_packet["active_lane"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_TARGET
    )
    assert source_packet["authorization_evidence"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_PACKET_EVIDENCE
    )
    assert source_packet["report"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_PACKET_REPORT
    )
    assert source_packet["packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_PACKET_OUTCOME
    )
    assert source_packet["strict_packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_PACKET_STRICT_OUTCOME
    )
    assert source_packet["consumed_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_TARGET
    )
    assert source_packet["consumed_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_KIND
    )
    assert source_packet["selected_next_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_TARGET
    )
    assert source_packet["selected_next_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_KIND
    )
    assert (
        source_packet[
            "baseline_component_equation_scaffold_result_review_consumed"
        ]
        == "yes"
    )
    assert (
        source_packet[
            "baseline_component_equation_source_classification_packet_prepared"
        ]
        == "yes"
    )
    assert (
        source_packet["baseline_component_equation_source_classification_only"]
        == "yes"
    )
    assert source_packet["equation_slot_source_status_classified_only"] == "yes"
    assert (
        source_packet[
            "equation_source_classification_before_equation_selection"
        ]
        == "yes"
    )
    assert source_packet[
        "baseline_component_equation_source_classification_row_count"
    ] == 8
    assert source_packet[
        "baseline_component_equation_source_classification_field_count"
    ] == 8
    assert source_packet[
        "baseline_component_equation_source_classification_allowed_class_count"
    ] == 6
    assert source_packet["standard_open_system_theory_import_required_slot_count"] == 3
    assert source_packet["literature_supplied_required_slot_count"] == 3
    assert source_packet["empirical_fit_needed_slot_count"] == 2
    assert source_packet["placeholder_carried_slot_count"] == 8
    assert source_packet["derived_from_existing_toe_ccft_math_slot_count"] == 0
    assert source_packet["blocked_primary_source_class_slot_count"] == 0
    assert source_packet["open_system_decoherence_primary_source_class"] == (
        "imported_from_standard_open_system_theory"
    )
    assert source_packet["measurement_contribution_primary_source_class"] == (
        "imported_from_standard_open_system_theory"
    )
    assert source_packet["back_action_contribution_primary_source_class"] == (
        "imported_from_standard_open_system_theory"
    )
    assert source_packet["feedback_hamiltonian_control_primary_source_class"] == (
        "literature_supplied"
    )
    assert source_packet["detector_efficiency_correction_primary_source_class"] == (
        "empirical_fit_needed"
    )
    assert source_packet["feedback_delay_correction_primary_source_class"] == (
        "empirical_fit_needed"
    )
    assert source_packet["control_field_effect_primary_source_class"] == (
        "literature_supplied"
    )
    assert source_packet["thermodynamic_energy_accounting_primary_source_class"] == (
        "literature_supplied"
    )
    assert source_packet["component_equations_derived"] == "no"
    assert source_packet["component_equations_imported"] == "no"
    assert source_packet["standard_open_system_equations_imported"] == "no"
    assert source_packet["literature_equations_adopted"] == "no"
    assert source_packet["empirical_fit_executed"] == "no"
    assert source_packet["equation_source_validated"] == "no"
    assert source_packet["component_equations_selected"] == "no"
    assert source_packet["tau_baseline_value_computed"] == "no"
    assert source_packet["baseline_model_completed"] == "no"
    assert source_packet["measurement_protocol_defined"] == "no"
    assert source_packet["statistical_validation_claimed"] == "no"
    assert source_packet["residual_separation_claimed"] == "no"
    assert source_packet["ccft_validation_accepted"] == "no"
    assert source_packet["master_action_promoted"] == "no"
    _assert_registry_nonclaims(source_packet)

    source_review = workstream(
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_TARGET, payload
    )
    assert source_review["status"] == "paused"
    assert source_review["active_lane"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_TARGET
    )
    assert source_review["authorization_evidence"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_EVIDENCE
    )
    assert source_review["report"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_REPORT
    )
    assert source_review["packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_OUTCOME
    )
    assert source_review["strict_packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_STRICT_OUTCOME
    )
    assert source_review["review_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_OUTCOME
    )
    assert source_review["strict_review_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_STRICT_OUTCOME
    )
    assert source_review["prepared_packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_PACKET_OUTCOME
    )
    assert source_review["prepared_packet_strict_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_PACKET_STRICT_OUTCOME
    )
    assert source_review["consumed_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_TARGET
    )
    assert source_review["consumed_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CLASSIFICATION_REVIEW_KIND
    )
    assert source_review["selected_next_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_TARGET
    )
    assert source_review["selected_next_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_KIND
    )
    assert (
        source_review[
            "baseline_component_equation_source_classification_packet_result_review_consumed"
        ]
        == "yes"
    )
    assert (
        source_review["equation_slot_source_status_classification_accepted_only"]
        == "yes"
    )
    assert source_review["source_classification_rows_accepted_as_labels_only"] == "yes"
    assert (
        source_review[
            "standard_open_system_import_required_slots_accepted_as_labels_only"
        ]
        == "yes"
    )
    assert (
        source_review["literature_supplied_slots_accepted_as_labels_only"]
        == "yes"
    )
    assert (
        source_review["empirical_fit_needed_slots_accepted_as_labels_only"]
        == "yes"
    )
    assert source_review["source_validation_criteria_packet_selected"] == "yes"
    assert source_review["accepted_source_classification_row_count"] == 8
    assert source_review["accepted_standard_open_system_import_required_slot_count"] == 3
    assert source_review["accepted_literature_supplied_required_slot_count"] == 3
    assert source_review["accepted_empirical_fit_needed_slot_count"] == 2
    assert source_review["accepted_placeholder_carried_slot_count"] == 8
    assert source_review["component_equations_derived"] == "no"
    assert source_review["component_equations_imported"] == "no"
    assert source_review["standard_open_system_equations_imported"] == "no"
    assert source_review["literature_equations_adopted"] == "no"
    assert source_review["empirical_fit_executed"] == "no"
    assert source_review["equation_source_validated"] == "no"
    assert source_review["source_classification_adequacy_claimed"] == "no"
    assert source_review["source_classification_completeness_claimed"] == "no"
    assert source_review["component_equations_selected"] == "no"
    assert source_review["tau_baseline_value_computed"] == "no"
    assert source_review["baseline_model_completed"] == "no"
    assert source_review["measurement_protocol_defined"] == "no"
    assert source_review["statistical_validation_claimed"] == "no"
    assert source_review["residual_separation_claimed"] == "no"
    assert source_review["ccft_validation_accepted"] == "no"
    assert source_review["master_action_promoted"] == "no"
    _assert_registry_nonclaims(source_review)

    criteria_packet = workstream(
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_TARGET, payload
    )
    assert criteria_packet["status"] == "paused"
    assert criteria_packet["active_lane"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_TARGET
    )
    assert criteria_packet["authorization_evidence"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_PACKET_EVIDENCE
    )
    assert criteria_packet["report"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_PACKET_REPORT
    )
    assert criteria_packet["packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_PACKET_OUTCOME
    )
    assert criteria_packet["strict_packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_PACKET_STRICT_OUTCOME
    )
    assert criteria_packet["consumed_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_TARGET
    )
    assert criteria_packet["consumed_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_KIND
    )
    assert criteria_packet["selected_next_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_TARGET
    )
    assert criteria_packet["selected_next_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_KIND
    )
    assert (
        criteria_packet[
            "baseline_component_equation_source_validation_criteria_packet_prepared"
        ]
        == "yes"
    )
    assert criteria_packet["source_validation_criteria_only"] == "yes"
    assert criteria_packet["source_acceptance_criteria_defined_only"] == "yes"
    assert criteria_packet["source_criteria_defined_before_source_validation"] == "yes"
    assert criteria_packet["source_criteria_defined_before_equation_import"] == "yes"
    assert criteria_packet["source_criteria_defined_before_literature_adoption"] == (
        "yes"
    )
    assert criteria_packet["source_criteria_defined_before_empirical_fit"] == "yes"
    assert (
        criteria_packet["standard_open_system_import_acceptance_criteria_defined"]
        == "yes"
    )
    assert (
        criteria_packet["literature_supplied_equation_acceptance_criteria_defined"]
        == "yes"
    )
    assert (
        criteria_packet["empirical_fit_needed_slot_acceptance_criteria_defined"]
        == "yes"
    )
    assert (
        criteria_packet[
            "baseline_component_equation_source_validation_criteria_row_count"
        ]
        == 3
    )
    assert (
        criteria_packet[
            "baseline_component_equation_source_validation_criteria_field_count"
        ]
        == 8
    )
    assert (
        criteria_packet[
            "standard_open_system_theory_import_acceptance_criteria_count"
        ]
        == 6
    )
    assert (
        criteria_packet["literature_supplied_equation_acceptance_criteria_count"]
        == 6
    )
    assert criteria_packet["empirical_fit_needed_slot_acceptance_criteria_count"] == 6
    assert criteria_packet["source_validation_criteria_total_criterion_count"] == 18
    assert criteria_packet["source_validation_criteria_source_class_count"] == 3
    assert criteria_packet["standard_open_system_import_required_slot_count_carried"] == 3
    assert criteria_packet["literature_supplied_required_slot_count_carried"] == 3
    assert criteria_packet["empirical_fit_needed_slot_count_carried"] == 2
    assert criteria_packet["source_validated"] == "no"
    assert criteria_packet["source_validation_executed"] == "no"
    assert criteria_packet["source_validation_performed"] == "no"
    assert criteria_packet["source_validation_accepted"] == "no"
    assert criteria_packet["standard_open_system_equations_imported"] == "no"
    assert criteria_packet["standard_open_system_equation_adopted"] == "no"
    assert criteria_packet["literature_equations_adopted"] == "no"
    assert criteria_packet["literature_equation_validated"] == "no"
    assert criteria_packet["empirical_fit_executed"] == "no"
    assert criteria_packet["empirical_fit_validated"] == "no"
    assert criteria_packet["fit_model_declared"] == "no"
    assert criteria_packet["data_source_selected"] == "no"
    assert criteria_packet["parameter_identifiability_checked"] == "no"
    assert criteria_packet["uncertainty_model_accepted"] == "no"
    assert criteria_packet["overfitting_guard_executed"] == "no"
    assert criteria_packet["failure_criteria_applied"] == "no"
    assert criteria_packet["component_equations_imported"] == "no"
    assert criteria_packet["component_equations_selected"] == "no"
    assert criteria_packet["equation_source_validated"] == "no"
    assert criteria_packet["tau_baseline_value_computed"] == "no"
    assert criteria_packet["baseline_model_completed"] == "no"
    assert criteria_packet["measurement_protocol_defined"] == "no"
    assert criteria_packet["statistical_validation_claimed"] == "no"
    assert criteria_packet["residual_separation_claimed"] == "no"
    assert criteria_packet["ccft_validation_accepted"] == "no"
    assert criteria_packet["master_action_promoted"] == "no"
    _assert_registry_nonclaims(criteria_packet)

    criteria_review = workstream(
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_TARGET,
        payload,
    )
    assert criteria_review["status"] == "paused"
    assert criteria_review["active_lane"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_TARGET
    )
    assert criteria_review["authorization_evidence"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_EVIDENCE
    )
    assert criteria_review["report"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_REPORT
    )
    assert criteria_review["packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_OUTCOME
    )
    assert criteria_review["strict_packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_STRICT_OUTCOME
    )
    assert criteria_review["review_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_OUTCOME
    )
    assert criteria_review["strict_review_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_STRICT_OUTCOME
    )
    assert criteria_review["prepared_packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_PACKET_OUTCOME
    )
    assert criteria_review["prepared_packet_strict_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_PACKET_STRICT_OUTCOME
    )
    assert criteria_review["consumed_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_TARGET
    )
    assert criteria_review["consumed_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_VALIDATION_CRITERIA_REVIEW_KIND
    )
    assert criteria_review["selected_next_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_TARGET
    )
    assert criteria_review["selected_next_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_KIND
    )
    assert (
        criteria_review[
            "baseline_component_equation_source_validation_criteria_packet_result_review_consumed"
        ]
        == "yes"
    )
    assert criteria_review["source_validation_criteria_accepted_only"] == "yes"
    assert criteria_review["source_acceptance_criteria_accepted_only"] == "yes"
    assert (
        criteria_review["source_validation_criteria_rows_accepted_as_criteria_only"]
        == "yes"
    )
    assert criteria_review["accepted_source_validation_criteria_row_count"] == 3
    assert criteria_review["accepted_source_validation_criteria_source_class_count"] == 3
    assert criteria_review["accepted_source_validation_criteria_total_criterion_count"] == 18
    assert (
        criteria_review[
            "accepted_standard_open_system_theory_import_acceptance_criteria_count"
        ]
        == 6
    )
    assert (
        criteria_review[
            "accepted_literature_supplied_equation_acceptance_criteria_count"
        ]
        == 6
    )
    assert criteria_review["accepted_empirical_fit_needed_slot_acceptance_criteria_count"] == 6
    assert criteria_review["accepted_standard_open_system_import_required_slot_count"] == 3
    assert criteria_review["accepted_literature_supplied_required_slot_count"] == 3
    assert criteria_review["accepted_empirical_fit_needed_slot_count"] == 2
    assert criteria_review["source_candidate_registry_packet_selected"] == "yes"
    assert criteria_review["source_candidate_registry_required_before_source_validation"] == "yes"
    assert criteria_review["source_candidate_registry_required_before_equation_import"] == "yes"
    assert (
        criteria_review[
            "source_candidate_registry_required_before_literature_adoption"
        ]
        == "yes"
    )
    assert criteria_review["source_candidate_registry_required_before_empirical_fit"] == "yes"
    assert criteria_review["source_validated"] == "no"
    assert criteria_review["source_validation_executed"] == "no"
    assert criteria_review["standard_open_system_equations_imported"] == "no"
    assert criteria_review["standard_open_system_equation_adopted"] == "no"
    assert criteria_review["literature_equations_adopted"] == "no"
    assert criteria_review["literature_equation_validated"] == "no"
    assert criteria_review["empirical_fit_executed"] == "no"
    assert criteria_review["fit_model_declared"] == "no"
    assert criteria_review["data_source_selected"] == "no"
    assert criteria_review["component_equations_selected"] == "no"
    assert criteria_review["equation_source_validated"] == "no"
    assert criteria_review["tau_baseline_value_computed"] == "no"
    assert criteria_review["baseline_model_completed"] == "no"
    assert criteria_review["measurement_protocol_defined"] == "no"
    assert criteria_review["statistical_validation_claimed"] == "no"
    assert criteria_review["residual_separation_claimed"] == "no"
    assert criteria_review["ccft_validation_accepted"] == "no"
    assert criteria_review["master_action_promoted"] == "no"
    _assert_registry_nonclaims(criteria_review)

    candidate_packet = workstream(
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_TARGET,
        payload,
    )
    assert candidate_packet["status"] == "paused"
    assert candidate_packet["active_lane"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_TARGET
    )
    assert candidate_packet["authorization_evidence"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_PACKET_EVIDENCE
    )
    assert candidate_packet["report"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_PACKET_REPORT
    )
    assert candidate_packet["packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_PACKET_OUTCOME
    )
    assert candidate_packet["strict_packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_PACKET_STRICT_OUTCOME
    )
    assert candidate_packet["consumed_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_TARGET
    )
    assert candidate_packet["consumed_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_KIND
    )
    assert candidate_packet["selected_next_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_TARGET
    )
    assert candidate_packet["selected_next_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_KIND
    )
    assert candidate_packet["source_candidate_registry_packet_prepared"] == "yes"
    assert candidate_packet["source_candidate_registry_only"] == "yes"
    assert candidate_packet["source_candidates_listed_only"] == "yes"
    assert candidate_packet["source_candidates_for_future_review_only"] == "yes"
    assert candidate_packet["source_candidates_registered_as_unvalidated_only"] == "yes"
    assert candidate_packet["candidate_sources_recorded_as_possible_sources_only"] == (
        "yes"
    )
    assert (
        candidate_packet[
            "baseline_component_equation_source_candidate_registry_field_count"
        ]
        == 9
    )
    assert (
        candidate_packet[
            "baseline_component_equation_source_candidate_registry_row_count"
        ]
        == 8
    )
    assert candidate_packet["source_candidate_registry_slot_id_count"] == 8
    assert candidate_packet["source_candidate_registry_candidate_source_count"] == 8
    assert candidate_packet["source_candidate_registry_source_class_count"] == 3
    assert candidate_packet["standard_open_system_theory_candidate_source_count"] == 3
    assert candidate_packet["literature_supplied_candidate_source_count"] == 3
    assert candidate_packet["empirical_fit_needed_candidate_source_count"] == 2
    assert candidate_packet["source_candidate_registry_missing_validation_item_count"] == 48
    assert (
        "candidate_standard_open_system_master_equation_family"
        in candidate_packet["source_candidate_registry_candidate_source_ids"]
    )
    assert (
        "candidate_measurement_feedback_thermodynamic_accounting_family"
        in candidate_packet["source_candidate_registry_candidate_source_ids"]
    )
    assert candidate_packet["candidate_source_accepted"] == "no"
    assert candidate_packet["candidate_source_validated"] == "no"
    assert candidate_packet["candidate_source_adopted"] == "no"
    assert candidate_packet["candidate_equation_adopted"] == "no"
    assert candidate_packet["source_validated"] == "no"
    assert candidate_packet["source_validation_executed"] == "no"
    assert candidate_packet["standard_open_system_equations_imported"] == "no"
    assert candidate_packet["standard_open_system_equation_adopted"] == "no"
    assert candidate_packet["literature_equations_adopted"] == "no"
    assert candidate_packet["empirical_fit_executed"] == "no"
    assert candidate_packet["fit_model_declared"] == "no"
    assert candidate_packet["data_source_selected"] == "no"
    assert candidate_packet["component_equations_selected"] == "no"
    assert candidate_packet["equation_source_validated"] == "no"
    assert candidate_packet["tau_baseline_value_computed"] == "no"
    assert candidate_packet["baseline_model_completed"] == "no"
    assert candidate_packet["measurement_protocol_defined"] == "no"
    assert candidate_packet["statistical_validation_claimed"] == "no"
    assert candidate_packet["residual_separation_claimed"] == "no"
    assert candidate_packet["ccft_validation_accepted"] == "no"
    assert candidate_packet["master_action_promoted"] == "no"
    _assert_registry_nonclaims(candidate_packet)

    candidate_review = workstream(
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_TARGET,
        payload,
    )
    assert candidate_review["status"] == "paused"
    assert candidate_review["active_lane"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_TARGET
    )
    assert (
        candidate_review["authorization_evidence"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_EVIDENCE
    )
    assert (
        candidate_review["report"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_REPORT
    )
    assert (
        candidate_review["packet_result"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_OUTCOME
    )
    assert (
        candidate_review["strict_packet_result"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_STRICT_OUTCOME
    )
    assert (
        candidate_review["review_result"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_OUTCOME
    )
    assert (
        candidate_review["strict_review_result"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_STRICT_OUTCOME
    )
    assert candidate_review["prepared_packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_PACKET_OUTCOME
    )
    assert candidate_review["prepared_packet_strict_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_PACKET_STRICT_OUTCOME
    )
    assert candidate_review["consumed_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_TARGET
    )
    assert candidate_review["consumed_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_CANDIDATE_REGISTRY_REVIEW_KIND
    )
    assert candidate_review["selected_next_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_TARGET
    )
    assert candidate_review["selected_next_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_KIND
    )
    assert (
        candidate_review[
            "baseline_component_equation_source_candidate_registry_packet_result_review_consumed"
        ]
        == "yes"
    )
    assert candidate_review["source_candidate_registry_accepted_only"] == "yes"
    assert candidate_review["source_candidates_accepted_as_candidate_rows_only"] == "yes"
    assert candidate_review["candidate_sources_accepted_as_possible_sources_only"] == (
        "yes"
    )
    assert (
        candidate_review[
            "candidate_source_applicability_warnings_retained_unresolved"
        ]
        == "yes"
    )
    assert candidate_review["candidate_source_missing_validation_items_retained"] == (
        "yes"
    )
    assert candidate_review["accepted_source_candidate_registry_field_count"] == 9
    assert candidate_review["accepted_source_candidate_registry_row_count"] == 8
    assert candidate_review["accepted_source_candidate_registry_slot_id_count"] == 8
    assert (
        candidate_review["accepted_source_candidate_registry_candidate_source_count"]
        == 8
    )
    assert candidate_review["accepted_source_candidate_registry_source_class_count"] == 3
    assert (
        candidate_review[
            "accepted_standard_open_system_theory_candidate_source_count"
        ]
        == 3
    )
    assert candidate_review["accepted_literature_supplied_candidate_source_count"] == 3
    assert candidate_review["accepted_empirical_fit_needed_candidate_source_count"] == 2
    assert (
        candidate_review[
            "accepted_source_candidate_registry_missing_validation_item_count"
        ]
        == 48
    )
    assert candidate_review["source_applicability_review_packet_selected"] == "yes"
    assert (
        candidate_review[
            "source_applicability_review_required_before_source_validation"
        ]
        == "yes"
    )
    assert (
        candidate_review[
            "source_applicability_review_required_before_equation_import"
        ]
        == "yes"
    )
    assert (
        candidate_review[
            "source_applicability_review_required_before_literature_adoption"
        ]
        == "yes"
    )
    assert (
        candidate_review["source_applicability_review_required_before_empirical_fit"]
        == "yes"
    )
    assert candidate_review["candidate_source_applicability_review_executed"] == "no"
    assert candidate_review["candidate_source_applicability_checked"] == "no"
    assert candidate_review["candidate_source_applicability_accepted"] == "no"
    assert candidate_review["source_candidate_applicability_determined"] == "no"
    assert candidate_review["source_validated"] == "no"
    assert candidate_review["source_validation_executed"] == "no"
    assert candidate_review["standard_open_system_equations_imported"] == "no"
    assert candidate_review["literature_equations_adopted"] == "no"
    assert candidate_review["empirical_fit_executed"] == "no"
    assert candidate_review["fit_model_declared"] == "no"
    assert candidate_review["data_source_selected"] == "no"
    assert candidate_review["component_equations_selected"] == "no"
    assert candidate_review["equation_source_validated"] == "no"
    assert candidate_review["tau_baseline_value_computed"] == "no"
    assert candidate_review["baseline_model_completed"] == "no"
    assert candidate_review["measurement_protocol_defined"] == "no"
    assert candidate_review["statistical_validation_claimed"] == "no"
    assert candidate_review["residual_separation_claimed"] == "no"
    assert candidate_review["ccft_validation_accepted"] == "no"
    assert candidate_review["master_action_promoted"] == "no"
    _assert_registry_nonclaims(candidate_review)

    applicability_packet = workstream(
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_TARGET,
        payload,
    )
    assert applicability_packet["status"] == "paused"
    assert applicability_packet["active_lane"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_TARGET
    )
    assert applicability_packet["authorized_next_strict_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_TARGET
    )
    assert applicability_packet["authorized_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_TARGET
    )
    assert applicability_packet["authorization_evidence"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_EVIDENCE
    )
    assert applicability_packet["report"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_REPORT
    )
    assert applicability_packet["packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_OUTCOME
    )
    assert applicability_packet["strict_packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_STRICT_OUTCOME
    )
    assert applicability_packet["consumed_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_PACKET_TARGET
    )
    assert applicability_packet["consumed_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_KIND
    )
    assert applicability_packet["selected_next_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_TARGET
    )
    assert applicability_packet["selected_next_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_REVIEW_REVIEW_KIND
    )
    assert (
        applicability_packet[
            "source_applicability_review_packet_prepared"
        ]
        == "yes"
    )
    assert applicability_packet["source_applicability_review_only"] == "yes"
    assert applicability_packet["candidate_source_applicability_map_prepared"] == "yes"
    assert (
        applicability_packet[
            "candidate_source_applicability_statuses_assigned_only"
        ]
        == "yes"
    )
    assert applicability_packet["candidate_source_applicability_checked"] == "yes"
    assert (
        applicability_packet["candidate_source_applicability_review_executed"]
        == "yes"
    )
    assert (
        applicability_packet[
            "candidate_source_applicability_review_as_prevalidation_filter_only"
        ]
        == "yes"
    )
    assert (
        applicability_packet[
            "baseline_component_equation_source_applicability_review_field_count"
        ]
        == 9
    )
    assert (
        applicability_packet[
            "baseline_component_equation_source_applicability_review_row_count"
        ]
        == 8
    )
    assert applicability_packet["source_applicability_review_slot_id_count"] == 8
    assert applicability_packet["source_applicability_review_status_count"] == 2
    assert applicability_packet["applicability_candidate_supported_count"] == 0
    assert applicability_packet["applicability_candidate_unclear_count"] == 3
    assert applicability_packet["applicability_candidate_blocked_count"] == 5
    assert applicability_packet["applicability_candidate_rejected_for_slot_count"] == 0
    assert (
        applicability_packet["standard_open_system_applicability_candidate_count"]
        == 3
    )
    assert applicability_packet["literature_supplied_applicability_candidate_count"] == 3
    assert applicability_packet["empirical_fit_needed_applicability_candidate_count"] == 2
    assert applicability_packet["unresolved_applicability_blocker_count"] == 8
    assert applicability_packet["required_next_applicability_check_count"] == 8
    assert applicability_packet["candidate_source_applicability_accepted"] == "no"
    assert applicability_packet["candidate_source_applicability_validated"] == "no"
    assert applicability_packet["candidate_source_accepted_as_applicable"] == "no"
    assert applicability_packet["candidate_source_rejected_as_inapplicable"] == "no"
    assert applicability_packet["source_applicability_acceptance_claimed"] == "no"
    assert applicability_packet["source_applicability_review_completed"] == "no"
    assert applicability_packet["source_validated"] == "no"
    assert applicability_packet["source_validation_executed"] == "no"
    assert applicability_packet["standard_open_system_equations_imported"] == "no"
    assert applicability_packet["literature_equations_adopted"] == "no"
    assert applicability_packet["empirical_fit_executed"] == "no"
    assert applicability_packet["fit_model_declared"] == "no"
    assert applicability_packet["data_source_selected"] == "no"
    assert applicability_packet["component_equations_selected"] == "no"
    assert applicability_packet["equation_source_validated"] == "no"
    assert applicability_packet["tau_baseline_value_computed"] == "no"
    assert applicability_packet["baseline_model_completed"] == "no"
    assert applicability_packet["measurement_protocol_defined"] == "no"
    assert applicability_packet["statistical_validation_claimed"] == "no"
    assert applicability_packet["residual_separation_claimed"] == "no"
    assert applicability_packet["ccft_validation_accepted"] == "no"
    assert applicability_packet["master_action_promoted"] == "no"
    _assert_registry_nonclaims(applicability_packet)

    gap_packet = workstream(
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_TARGET,
        payload,
    )
    assert gap_packet["status"] == "paused"
    assert gap_packet["authorization_evidence"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_PACKET_EVIDENCE
    )
    assert gap_packet["report"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_PACKET_REPORT
    )
    assert gap_packet["packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_PACKET_OUTCOME
    )
    assert gap_packet["strict_packet_result"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_PACKET_STRICT_OUTCOME
    )
    assert gap_packet["consumed_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_TARGET
    )
    assert (
        gap_packet["consumed_target_kind"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_KIND
    )
    assert gap_packet["selected_next_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_TARGET
    )
    assert gap_packet["selected_next_target_kind"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_KIND
    )
    assert gap_packet["source_applicability_gap_classification_packet_prepared"] == "yes"
    assert gap_packet["source_applicability_gap_classification_only"] == "yes"
    assert gap_packet["source_applicability_gaps_classified_only"] == "yes"
    assert (
        gap_packet[
            "unclear_and_blocked_source_applicability_gaps_classified_only"
        ]
        == "yes"
    )
    assert gap_packet[
        "baseline_component_equation_source_applicability_gap_classification_field_count"
    ] == 9
    assert gap_packet[
        "baseline_component_equation_source_applicability_gap_classification_row_count"
    ] == 8
    assert gap_packet["source_applicability_gap_classification_count"] == 8
    assert gap_packet["source_applicability_gap_missing_evidence_class_count"] == 8
    assert gap_packet["gap_classified_applicability_candidate_unclear_count"] == 3
    assert gap_packet["gap_classified_applicability_candidate_blocked_count"] == 5
    assert gap_packet["gap_classified_applicability_candidate_supported_count"] == 0
    assert (
        gap_packet["gap_classified_applicability_candidate_rejected_for_slot_count"]
        == 0
    )
    assert gap_packet["standard_theory_gap_classification_count"] == 3
    assert gap_packet["literature_gap_classification_count"] == 3
    assert gap_packet["empirical_fit_gap_classification_count"] == 2
    assert gap_packet["source_applicability_gap_remediation_performed"] == "no"
    assert gap_packet["source_candidate_replacement_performed"] == "no"
    assert gap_packet["source_candidates_replaced_count"] == 0
    assert gap_packet["source_applicability_gaps_remediated_count"] == 0
    assert gap_packet["source_validated"] == "no"
    assert gap_packet["standard_open_system_equations_imported"] == "no"
    assert gap_packet["literature_equations_adopted"] == "no"
    assert gap_packet["empirical_fit_executed"] == "no"
    assert gap_packet["tau_baseline_value_computed"] == "no"
    assert gap_packet["baseline_model_completed"] == "no"
    assert gap_packet["master_action_promoted"] == "no"
    _assert_registry_nonclaims(gap_packet)

    gap_review = workstream(
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_TARGET,
        payload,
    )
    assert gap_review["status"] == "paused"
    assert (
        gap_review["authorization_evidence"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_EVIDENCE
    )
    assert (
        gap_review["report"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_REPORT
    )
    assert (
        gap_review["packet_result"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_OUTCOME
    )
    assert (
        gap_review["strict_packet_result"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_STRICT_OUTCOME
    )
    assert gap_review["consumed_target"] == (
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_TARGET
    )
    assert (
        gap_review["consumed_target_kind"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_CLASSIFICATION_REVIEW_KIND
    )
    assert (
        gap_review["selected_next_target"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_TARGET
    )
    assert (
        gap_review["selected_next_target_kind"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_KIND
    )
    assert (
        gap_review[
            "baseline_component_equation_source_applicability_gap_classification_packet_result_review_consumed"
        ]
        == "yes"
    )
    assert gap_review["source_applicability_gap_classification_packet_accepted"] == "yes"
    assert gap_review["source_applicability_gap_classification_accepted_only"] == "yes"
    assert gap_review["unclear_and_blocked_gap_classifications_accepted_only"] == "yes"
    assert gap_review["accepted_gap_classified_applicability_candidate_unclear_count"] == 3
    assert gap_review["accepted_gap_classified_applicability_candidate_blocked_count"] == 5
    assert gap_review["accepted_gap_classified_applicability_candidate_supported_count"] == 0
    assert gap_review["source_applicability_gaps_remediated_count"] == 0
    assert gap_review["source_candidates_replaced_count"] == 0
    assert gap_review["gap_resolution_strategy_packet_selected"] == "yes"
    assert gap_review["gap_resolution_strategy_required_before_source_validation"] == "yes"
    assert gap_review["source_resolution_strategy_executed"] == "no"
    assert gap_review["source_applicability_gap_remediation_performed"] == "no"
    assert gap_review["source_candidate_replacement_performed"] == "no"
    assert gap_review["source_validated"] == "no"
    assert gap_review["source_validation_executed"] == "no"
    assert gap_review["standard_open_system_equations_imported"] == "no"
    assert gap_review["literature_equations_adopted"] == "no"
    assert gap_review["empirical_fit_executed"] == "no"
    assert gap_review["tau_baseline_value_computed"] == "no"
    assert gap_review["baseline_model_completed"] == "no"
    assert gap_review["master_action_promoted"] == "no"
    _assert_registry_nonclaims(gap_review)

    strategy_packet = workstream(
        BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_TARGET,
        payload,
    )
    assert strategy_packet["status"] == "paused"
    assert (
        strategy_packet["authorization_evidence"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_PACKET_EVIDENCE
    )
    assert (
        strategy_packet["report"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_PACKET_REPORT
    )
    assert (
        strategy_packet["packet_result"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_PACKET_OUTCOME
    )
    assert (
        strategy_packet["strict_packet_result"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_PACKET_STRICT_OUTCOME
    )
    assert (
        strategy_packet["consumed_target"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_TARGET
    )
    assert (
        strategy_packet["consumed_target_kind"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_KIND
    )
    assert (
        strategy_packet["selected_next_target"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_REVIEW_TARGET
    )
    assert (
        strategy_packet["selected_next_target_kind"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_REVIEW_KIND
    )
    assert strategy_packet["source_applicability_gap_resolution_strategy_packet_prepared"] == "yes"
    assert strategy_packet["source_applicability_gap_resolution_strategy_only"] == "yes"
    assert (
        strategy_packet["source_applicability_gap_resolution_paths_selected_only"]
        == "yes"
    )
    assert (
        strategy_packet[
            "baseline_component_equation_source_applicability_gap_resolution_strategy_field_count"
        ]
        == 9
    )
    assert (
        strategy_packet[
            "baseline_component_equation_source_applicability_gap_resolution_strategy_row_count"
        ]
        == 8
    )
    assert strategy_packet["source_applicability_gap_resolution_strategy_path_count"] == 8
    assert strategy_packet["strategy_path_clarification_needed_count"] == 3
    assert strategy_packet["strategy_path_standard_theory_import_work_needed_count"] == 3
    assert strategy_packet["strategy_path_literature_review_needed_count"] == 3
    assert strategy_packet["strategy_path_source_replacement_if_needed_count"] == 3
    assert strategy_packet["strategy_path_empirical_fit_design_needed_count"] == 2
    assert strategy_packet["source_resolution_path_selected"] == "yes"
    assert strategy_packet["source_remediation_strategy_selected"] == "yes"
    assert strategy_packet["source_replacement_strategy_selected"] == "yes"
    assert strategy_packet["literature_review_strategy_selected"] == "yes"
    assert strategy_packet["standard_theory_import_work_selected"] == "yes"
    assert strategy_packet["empirical_fit_design_selected"] == "yes"
    assert strategy_packet["source_resolution_strategy_executed"] == "no"
    assert strategy_packet["source_applicability_gap_remediation_performed"] == "no"
    assert strategy_packet["source_candidate_replacement_performed"] == "no"
    assert strategy_packet["source_candidate_replacement_selected"] == "no"
    assert strategy_packet["source_applicability_gaps_remediated_count"] == 0
    assert strategy_packet["source_candidates_replaced_count"] == 0
    assert strategy_packet["source_validated"] == "no"
    assert strategy_packet["source_validation_executed"] == "no"
    assert strategy_packet["standard_open_system_equations_imported"] == "no"
    assert strategy_packet["literature_equations_adopted"] == "no"
    assert strategy_packet["empirical_fit_executed"] == "no"
    assert strategy_packet["tau_baseline_value_computed"] == "no"
    assert strategy_packet["baseline_model_completed"] == "no"
    assert strategy_packet["master_action_promoted"] == "no"
    _assert_registry_nonclaims(strategy_packet)

    strategy_review = workstream(FINAL_PREVIOUS_TARGET, payload)
    assert strategy_review["status"] == "paused"
    assert strategy_review["authorization_evidence"] == FINAL_EVIDENCE
    assert strategy_review["report"] == FINAL_REPORT
    assert strategy_review["packet_result"] == FINAL_OUTCOME
    assert strategy_review["strict_packet_result"] == FINAL_STRICT_OUTCOME
    assert strategy_review["consumed_target"] == FINAL_PREVIOUS_TARGET
    assert (
        strategy_review["consumed_target_kind"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_REVIEW_KIND
    )
    assert strategy_review["selected_next_target"] == FINAL_LIVE_TARGET
    assert strategy_review["selected_next_target_kind"] == FINAL_KIND
    _assert_gap_resolution_strategy_review_acceptance(strategy_review)
    _assert_registry_nonclaims(strategy_review)

    active = workstream(FINAL_LIVE_TARGET, payload)
    assert active["status"] == "active"
    assert active["active_lane"] == FINAL_LIVE_TARGET
    assert active["authorized_next_strict_target"] == FINAL_LIVE_TARGET
    assert active["consumed_target"] == (
        FINAL_PREVIOUS_TARGET
    )
    assert (
        active["consumed_target_kind"]
        == BASELINE_COMPONENT_EQUATION_SOURCE_APPLICABILITY_GAP_RESOLUTION_STRATEGY_REVIEW_KIND
    )
    assert active["authorization_evidence"] == FINAL_EVIDENCE
    assert active["report"] == FINAL_REPORT
    assert active["packet_result"] == FINAL_OUTCOME
    assert active["strict_packet_result"] == FINAL_STRICT_OUTCOME
    assert active["selected_next_target"] == "PENDING"
    assert active["selected_next_target_kind"] == "PENDING"
    assert active["suggested_next_packet_target"] == FINAL_LIVE_TARGET
    assert active["suggested_next_packet_kind"] == FINAL_KIND
    _assert_gap_resolution_strategy_review_acceptance(active)
    assert (
        active[
            "baseline_component_equation_source_applicability_gap_classification_packet_result_review_consumed"
        ]
        == "yes"
    )
    assert active["source_applicability_gap_classification_packet_accepted"] == "yes"
    assert active["source_applicability_gap_classification_accepted_only"] == "yes"
    assert active["unclear_and_blocked_gap_classifications_accepted_only"] == "yes"
    assert active["accepted_gap_classified_applicability_candidate_unclear_count"] == 3
    assert active["accepted_gap_classified_applicability_candidate_blocked_count"] == 5
    assert active["accepted_gap_classified_applicability_candidate_supported_count"] == 0
    assert active["source_applicability_gaps_remediated_count"] == 0
    assert active["source_candidates_replaced_count"] == 0
    assert active["gap_resolution_strategy_packet_selected"] == "yes"
    assert active["gap_resolution_strategy_required_before_source_validation"] == "yes"
    assert active["source_applicability_gap_resolution_strategy_packet_prepared"] == "yes"
    assert active["source_applicability_gap_resolution_strategy_only"] == "yes"
    assert active["source_applicability_gap_resolution_paths_selected_only"] == "yes"
    assert (
        active[
            "baseline_component_equation_source_applicability_gap_resolution_strategy_field_count"
        ]
        == 9
    )
    assert (
        active[
            "baseline_component_equation_source_applicability_gap_resolution_strategy_row_count"
        ]
        == 8
    )
    assert active["source_applicability_gap_resolution_strategy_path_count"] == 8
    assert active["strategy_path_clarification_needed_count"] == 3
    assert active["strategy_path_standard_theory_import_work_needed_count"] == 3
    assert active["strategy_path_literature_review_needed_count"] == 3
    assert active["strategy_path_source_replacement_if_needed_count"] == 3
    assert active["strategy_path_empirical_fit_design_needed_count"] == 2
    assert active["strategy_rows_executed_count"] == 0
    assert active["source_resolution_path_selected"] == "yes"
    assert active["source_remediation_strategy_selected"] == "yes"
    assert active["source_replacement_strategy_selected"] == "yes"
    assert active["literature_review_strategy_selected"] == "yes"
    assert active["standard_theory_import_work_selected"] == "yes"
    assert active["empirical_fit_design_selected"] == "yes"
    assert active["source_resolution_strategy_executed"] == "no"
    assert active["source_candidate_replacement_selected"] == "no"
    assert active["source_applicability_gap_classification_packet_prepared"] == "yes"
    assert active["source_applicability_gap_classification_only"] == "yes"
    assert active["source_applicability_gaps_classified_only"] == "yes"
    assert (
        active["unclear_and_blocked_source_applicability_gaps_classified_only"]
        == "yes"
    )
    assert active[
        "baseline_component_equation_source_applicability_gap_classification_row_count"
    ] == 8
    assert active["gap_classified_applicability_candidate_unclear_count"] == 3
    assert active["gap_classified_applicability_candidate_blocked_count"] == 5
    assert active["source_applicability_gap_remediation_performed"] == "no"
    assert active["source_candidate_replacement_performed"] == "no"
    assert (
        active[
            "baseline_component_equation_source_candidate_registry_packet_result_review_consumed"
        ]
        == "yes"
    )
    assert active["source_candidate_registry_accepted_only"] == "yes"
    assert active["source_candidates_accepted_as_candidate_rows_only"] == "yes"
    assert active["source_applicability_review_packet_selected"] == "yes"
    assert active["source_applicability_review_packet_prepared"] == "yes"
    assert active["source_applicability_review_only"] == "yes"
    assert active["candidate_source_applicability_map_prepared"] == "yes"
    assert active["candidate_source_applicability_review_executed"] == "yes"
    assert active["candidate_source_applicability_checked"] == "yes"
    assert active["candidate_source_applicability_accepted"] == "no"
    assert active["source_candidate_applicability_determined"] == "no"
    assert active["applicability_candidate_unclear_count"] == 3
    assert active["applicability_candidate_blocked_count"] == 5
    assert active["applicability_candidate_supported_count"] == 0
    assert active["source_candidate_registry_packet_prepared"] == "yes"
    assert active["source_candidate_registry_only"] == "yes"
    assert active["source_candidates_listed_only"] == "yes"
    assert active["source_candidates_for_future_review_only"] == "yes"
    assert active["source_candidate_registry_source_class_count"] == 3
    assert active["standard_open_system_theory_candidate_source_count"] == 3
    assert active["literature_supplied_candidate_source_count"] == 3
    assert active["empirical_fit_needed_candidate_source_count"] == 2
    assert active["candidate_source_accepted"] == "no"
    assert active["candidate_source_validated"] == "no"
    assert active["candidate_source_adopted"] == "no"
    assert active["candidate_equation_adopted"] == "no"
    assert (
        active[
            "baseline_component_equation_source_validation_criteria_packet_result_review_consumed"
        ]
        == "yes"
    )
    assert active["source_validation_criteria_accepted_only"] == "yes"
    assert active["source_acceptance_criteria_accepted_only"] == "yes"
    assert active["source_validation_criteria_rows_accepted_as_criteria_only"] == "yes"
    assert active["source_candidate_registry_packet_selected"] == "yes"
    assert (
        active[
            "baseline_component_equation_source_validation_criteria_packet_prepared"
        ]
        == "yes"
    )
    assert active["source_validation_criteria_only"] == "yes"
    assert active["source_acceptance_criteria_defined_only"] == "yes"
    assert active["source_validated"] == "no"
    assert active["source_validation_executed"] == "no"
    assert active["component_equations_derived"] == "no"
    assert active["component_equations_imported"] == "no"
    assert active["literature_equations_adopted"] == "no"
    assert active["empirical_fit_executed"] == "no"
    assert active["equation_source_validated"] == "no"
    assert active[
        "measurement_feedback_baseline_pressure_packet_accepted_as_baseline_hardening_only"
    ] == "yes"
    assert active["external_source_treated_as_toe_evidence"] == "no"
    assert active["external_source_treated_as_ccft_evidence"] == "no"
    assert active["external_source_treated_as_empirical_validation"] == "no"
    assert active["external_source_treated_as_protocol_readiness"] == "no"
    assert active["external_source_treated_as_statistical_validation"] == "no"
    assert active["external_source_treated_as_master_action_support"] == "no"
    assert (
        active["future_tau_baseline_must_include_measurement_feedback_effects"]
        == "yes"
    )
    assert (
        active["residual_formula_changed_by_baseline_pressure_review"]
        == "no"
    )
    assert active["baseline_component_registry_packet_prepared"] == "yes"
    assert active["baseline_component_registry_traceability_only"] == "yes"
    assert active["tau_baseline_component_registry_prepared"] == "yes"
    assert active["tau_baseline_future_comparison_baseline_only"] == "yes"
    assert active["tau_baseline_value_computed"] == "no"
    assert active["tau_baseline_completed_model_claimed"] == "no"
    assert active["baseline_component_completeness_claimed"] == "no"
    assert active["baseline_component_registry_row_count"] == 8
    assert active["registered_tau_baseline_component_count"] == 8
    assert (
        "feedback Hamiltonian control"
        in active["registered_tau_baseline_components"]
    )
    assert (
        "thermodynamic and energy accounting"
        in active["registered_tau_baseline_components"]
    )
    assert (
        active["residual_formula_changed_by_baseline_component_registry"]
        == "no"
    )
    assert active["baseline_component_registry_result_review_consumed"] == "yes"
    assert active["baseline_component_interaction_risk_traceability_only"] == "yes"
    assert active["tau_baseline_component_interaction_risks_mapped"] == "yes"
    assert (
        active["interaction_risks_recorded_as_baseline_warnings_only"]
        == "yes"
    )
    assert active["baseline_component_interaction_risk_id_count"] == 8
    assert active["measurement_back_action_coupling_risk_recorded"] == "yes"
    assert active["detector_efficiency_feedback_control_coupling_risk_recorded"] == (
        "yes"
    )
    assert active["feedback_delay_hamiltonian_control_coupling_risk_recorded"] == (
        "yes"
    )
    assert active["control_field_decoherence_coupling_risk_recorded"] == "yes"
    assert active["measurement_feedback_energy_accounting_coupling_risk_recorded"] == (
        "yes"
    )
    assert active["detector_efficiency_measurement_record_coupling_risk_recorded"] == (
        "yes"
    )
    assert active["feedback_control_field_coupling_risk_recorded"] == "yes"
    assert active["delay_energy_accounting_coupling_risk_recorded"] == "yes"
    assert active["component_independence_claimed"] == "no"
    assert active["baseline_component_independence_claimed"] == "no"
    assert active["interaction_model_completed"] == "no"
    assert active["interaction_coupling_terms_computed"] == "no"
    assert active["baseline_model_completed"] == "no"
    assert active["baseline_component_completeness_claimed"] == "no"
    assert active["residual_formula_changed_by_interaction_risk_packet"] == "no"
    assert active["selected_primary_residual_formula"] == (
        "r_tau = (tau_candidate - tau_baseline) / tau_baseline"
    )
    assert active["normalized_lifetime_residual_selected_primary"] == "yes"
    assert active["residual_formula_selected"] == "yes"
    assert active["residual_formula_selection_only"] == "yes"
    assert active["formula_selected_for_future_comparison_use_only"] == "yes"
    assert active["ccft_empirical_discriminator_candidate_map_target_count"] == 11
    assert active[
        "ccft_empirical_discriminator_candidate_priority_selection_action_count"
    ] == 10
    assert active["selected_top_candidate_for_future_packet_only"] == (
        "controlled_mesoscopic_coherence_platform_candidate"
    )
    assert active["C_k_action_embedding_authorized"] == "no"
    assert active["C_k_variation_authorized"] == "no"
    assert active["empirical_discriminator_claims_authorized"] == "no"
    assert active["empirical_claim_authorized"] == "no"
    assert active["pillar_closure_authorized"] == "no"
    assert active["empirical_test_executed"] == "no"
    assert active["empirical_execution_authorized"] == "no"
    assert (
        active["selected_ccft_empirical_discriminator_candidate_packet_action_count"]
        == 11
    )
    assert active["selected_ccft_empirical_discriminator_candidate_id"] == (
        "controlled_mesoscopic_coherence_platform_candidate"
    )
    assert active["selected_ccft_empirical_discriminator_candidate_observable"] == (
        "coherence_lifetime_residual_candidate"
    )
    assert active["selected_ccft_empirical_discriminator_candidate_baseline"] == (
        "standard_open_system_decoherence_baseline_comparison"
    )
    assert active["selected_ccft_empirical_discriminator_candidate_falsifier"] == (
        "null_separation_from_baseline_with_registered_tolerances"
    )
    assert active["priority_selection_result_review_consumed"] == "yes"
    assert active["selected_candidate_instantiated_for_future_packet_only"] == "yes"
    assert active["selected_observable_bound_as_planning_row"] == "yes"
    assert active["selected_baseline_bound_as_planning_row"] == "yes"
    assert active["selected_falsifier_bound_as_planning_row"] == "yes"
    assert active["selected_candidate_packet_accepted_as_future_packet_only"] == "yes"
    assert active["registered_tolerances_traceability_placeholder_only"] == "yes"
    assert active["registered_tolerances_empirically_calibrated"] == "no"
    assert active["registered_tolerances_statistically_validated"] == "no"
    assert active["registered_tolerances_execution_authorized"] == "no"
    assert active["registered_tolerances_empirical_claim_authorized"] == "no"
    assert active["registered_tolerances_sufficient_for_execution"] == "no"
    assert (
        active["registered_tolerances_distinguish_ccft_from_baseline_claimed"]
        == "no"
    )
    assert active["registered_tolerances_bound_to_measurement_campaign"] == "no"
    assert active["tolerance_registry_result_review_consumed"] == "yes"
    assert active["tolerance_registry_review_result"] == (
        STAGES["tolerance_registry_review"].outcome_id
    )
    assert active["tolerance_registry_review_strict_result"] == (
        STAGES["tolerance_registry_review"].strict_outcome_id
    )
    assert active["baseline_comparison_semantics_packet_prepared"] == "yes"
    assert active["baseline_comparison_semantics_rows_registered"] == "yes"
    assert active["baseline_semantics_logic_only"] == "yes"
    assert active["baseline_complete_claimed"] == "no"
    assert active["baseline_experimentally_fitted"] == "no"
    assert active["residual_observed"] == "no"
    assert active["tolerance_determines_significance"] == "no"
    assert active["ccft_measurable_separation_predicted"] == "no"
    assert active["candidate_ready_for_execution"] == "no"
    assert active["baseline_separation_claimed"] == "no"
    assert active["empirical_protocol_authorized"] == "no"
    assert active["empirical_protocol_defined"] == "no"
    assert active["statistical_validation_claimed"] == "no"
    assert active["statistical_decision_rule_defined"] == "no"
    assert active["effect_size_threshold_defined"] == "no"
    assert active["execution_readiness_claimed"] == "no"
    assert active["baseline_comparison_semantics_packet_accepted_as_logic_only"] == "yes"
    assert active["baseline_semantics_rows_accepted_as_non_executed_only"] == "yes"
    assert active["residual_definition_status_accepted_as_placeholder_only"] == "yes"
    assert active["comparison_direction_accepted_as_placeholder_only"] == "yes"
    assert active["baseline_not_accepted_as_complete"] == "yes"
    assert active["baseline_adequacy_accepted"] == "no"
    assert active["baseline_empirical_fit_quality_accepted"] == "no"
    assert active["statistical_decision_rule_validity_accepted"] == "no"
    assert active["observed_separation_accepted"] == "no"
    assert active["ccft_predicted_separation_accepted"] == "no"
    assert active["experimental_protocol_readiness_accepted"] == "no"
    assert active["baseline_comparison_semantics_result_review_consumed"] == "yes"
    assert active["baseline_comparison_semantics_review_result"] == (
        STAGES["baseline_semantics_review"].outcome_id
    )
    assert active["baseline_comparison_semantics_review_strict_result"] == (
        STAGES["baseline_semantics_review"].strict_outcome_id
    )
    assert active[
        "selected_ccft_empirical_discriminator_observable_definition_semantics_field_count"
    ] == 9
    assert active[
        "selected_ccft_empirical_discriminator_observable_definition_semantics_row_count"
    ] == 1
    assert "coherence_lifetime_residual_candidate" in (
        active["selected_ccft_empirical_discriminator_observable_ids"]
    )
    assert active[
        "selected_ccft_empirical_discriminator_observable_candidate_platform_binding"
    ] == "controlled_mesoscopic_coherence_platform_candidate"
    assert active[
        "selected_ccft_empirical_discriminator_observable_baseline_binding"
    ] == "standard_open_system_decoherence_baseline_comparison"
    assert active[
        "selected_ccft_empirical_discriminator_observable_tolerance_binding"
    ] == "TOL-CCFT-MESO-COH-LIFETIME-RESIDUAL-v0"
    assert active[
        "selected_ccft_empirical_discriminator_observable_null_default"
    ] == "null_separation_from_baseline_with_registered_tolerances"
    assert active[
        "selected_ccft_empirical_discriminator_observable_execution_status"
    ] == "not_executed"
    assert active["observable_definition_semantics_packet_prepared"] == "yes"
    assert active["observable_definition_semantics_rows_registered"] == "yes"
    assert active["observable_semantics_meaning_only"] == "yes"
    assert active["observable_defined_as_future_comparison_object"] == "yes"
    assert active["comparison_direction_resolved"] == "no"
    assert active["observed_empirical_residual_claimed"] == "no"
    assert active["ccft_predicted_residual_claimed"] == "no"
    assert active["statistically_significant_deviation_claimed"] == "no"
    assert active["measurement_protocol_defined"] == "no"
    assert active["validated_discriminator_claimed"] == "no"
    assert active["coherence_lifetime_baseline_separation_claimed"] == "no"
    assert (
        active["observable_definition_semantics_packet_accepted_as_meaning_only"]
        == "yes"
    )
    assert (
        active["observable_definition_semantics_rows_accepted_as_non_executed_only"]
        == "yes"
    )
    assert (
        active[
            "coherence_lifetime_residual_candidate_accepted_as_future_comparison_object_only"
        ]
        == "yes"
    )
    assert active["registered_tolerance_binding_retained_as_traceability_only"] == "yes"
    assert active["residual_formula_selected"] == "yes"
    assert active["residual_formula_selection_required_before_protocol"] == "yes"
    assert active["observed_residual_accepted"] == "no"
    assert active["ccft_predicted_residual_accepted"] == "no"
    assert active["statistical_effect_size_accepted"] == "no"
    assert active["measured_coherence_anomaly_accepted"] == "no"
    assert active["baseline_separation_accepted"] == "no"
    assert active["measurement_protocol_readiness_accepted"] == "no"
    assert active["empirical_confirmation_accepted"] == "no"
    assert active["empirical_methods_section_claimed"] == "no"
    assert active["empirical_protocol_design_authorized"] == "no"
    assert active["empirical_protocol_executed"] == "no"
    assert active["selected_candidate_validation_claimed"] == "no"
    assert active["future_packet_preparation_only"] == "yes"
    assert active["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"] == "yes"
    assert active["later_ccft_artifacts_fully_populated"] == "yes"
    _assert_registry_nonclaims(active)


def test_post_phi_transport_ccft_public_mirrors_contain_outcome_tokens() -> None:
    for path in PUBLIC_SURFACES:
        text = read_text(path)
        assert FINAL_LIVE_TARGET in text
        assert FINAL_PREVIOUS_TARGET in text
        assert FINAL_OUTCOME in text
        assert FINAL_STRICT_OUTCOME in text
        assert LEAN_STATUS_WORDING in text
        for stage_key in ORDERED_STAGE_KEYS:
            spec = STAGES[stage_key]
            assert spec.outcome_id in text, f"{path} missing {spec.outcome_id}"
            assert spec.strict_outcome_id in text, (
                f"{path} missing {spec.strict_outcome_id}"
            )

    for doc in PAPER_DOCS:
        text = read_text(REPO_ROOT / doc)
        assert LOCAL_PHI_THEOREM_LINKAGE_TRIAD_LABEL in text
        assert "CCFT" in text
        assert "no proof execution" in text
        assert "no CCFT validation" in text
        assert "no master-action promotion" in text


def test_post_phi_transport_ccft_focused_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_post_phi_transport_ccft_chain_gate.py"
    )
