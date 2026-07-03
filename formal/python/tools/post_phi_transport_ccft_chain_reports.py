from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-07-02T00:00:00Z"
STAGE_CAPTURED_AT_UTC = {
    "observable_definition_semantics_packet": "2026-07-03T00:00:00Z",
    "observable_definition_semantics_review": "2026-07-03T00:00:00Z",
    "residual_formula_selection_packet": "2026-07-03T00:00:00Z",
    "residual_formula_selection_review": "2026-07-03T00:00:00Z",
    "measurement_feedback_baseline_pressure_packet": "2026-07-03T00:00:00Z",
}

LEAN_STATUS_WORDING = (
    "full ToeFormal aggregate = NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION; "
    "scoped Lean targets = PASSED_SERIAL_RERUN"
)
LEAN_STATUS_WORDING_LINES = [
    "full ToeFormal aggregate = NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION",
    "scoped Lean targets = PASSED_SERIAL_RERUN",
]
FULL_TOEFORMAL_AGGREGATE_STATUS = "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
SCOPED_LEAN_TARGETS_STATUS = "PASSED_SERIAL_RERUN"

LOCAL_PHI_THEOREM_LINKAGE_TRIAD_LABEL = (
    "local phi source/bridge/transport theorem-linkage triad"
)
LOCAL_PHI_TRIAD_EQUATIONS = [
    "C_source^phi = 0",
    "C_bridge^phi = 0",
    "C_transport^phi = 0",
]
CCFT_REQUIRED_FOLLOW_ON_ARTIFACTS = [
    "CCFT_TO_TOE_OBJECT_CROSSWALK_v0.md",
    "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0.md",
    "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0.md",
    "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0.md",
]
CCFT_INDEX_REVIEW_ACCEPTANCE_ITEMS = [
    "CCFT-specific C_k admissibility obligation index accepted",
    "CCFT remains candidate mesoscopic coherence bridge layer only",
    "C_source-style CCFT rows indexed",
    "C_bridge-style CCFT rows indexed",
    "C_transport-style CCFT rows indexed",
    "C_exchange-style CCFT rows indexed",
    "CCFT-ToE object crosswalk consumed as prior planning surface",
    "roadmap rebase consumed as planning-only authority",
    "local phi source/bridge/transport theorem-linkage triad preserved",
    "no proof execution",
    "no new theorem discharge",
    "no CCFT validation",
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
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_TARGET = (
    "prepare_ccft_full_variational_action_program_packet"
)
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_OUTCOME = (
    "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_PREPARED_LAGRANGIAN_"
    "HAMILTONIAN_SOURCE_AND_TRANSPORT_TARGETS_NO_ACTION_EMBEDDING_OR_"
    "MASTER_ACTION_PROMOTION"
)
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_STRICT_OUTCOME = (
    "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_PREPARED_AS_REQUIRED_PRE_"
    "DERIVATION_PLAN_NO_CK_VARIATION_OR_CCFT_VALIDATION"
)
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_REVIEW_TARGET = (
    "review_ccft_full_variational_action_program_packet_result"
)
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_DEFINITION_TARGETS = [
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
]
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_BOUNDARY = (
    "This packet defines a required pre-derivation planning program for CCFT "
    "Lagrangian, Hamiltonian, source, transport, and exchange target surfaces "
    "only. It does not embed C_k into an action, vary C_k, derive any C_k "
    "component, validate CCFT, authorize empirical discriminator claims, close "
    "any pillar or seam, or promote the master action."
)
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_REVIEW_OUTCOME = (
    "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_RESULT_REVIEW_ACCEPTS_"
    "LAGRANGIAN_HAMILTONIAN_SOURCE_AND_TRANSPORT_TARGETS_NO_ACTION_EMBEDDING_"
    "OR_MASTER_ACTION_PROMOTION"
)
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_REVIEW_STRICT_OUTCOME = (
    "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_RESULT_REVIEW_ACCEPTS_PRE_"
    "DERIVATION_PLAN_NO_CK_VARIATION_OR_CCFT_VALIDATION"
)
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_REVIEW_ACCEPTANCE_ITEMS = [
    "CCFT full variational/action program packet accepted",
    "CCFT full Lagrangian candidate targets indexed",
    "CCFT full Hamiltonian candidate targets indexed",
    "phi-sector variational route targets indexed",
    "chi-sector variational route targets indexed",
    "R/K rotor-curvature variational route targets indexed",
    "CCFT stress-energy/source candidate targets indexed",
    "CCFT C_source derivation targets indexed",
    "CCFT C_bridge derivation targets indexed",
    "CCFT C_transport component-derivation targets indexed",
    "CCFT C_exchange phi-chi exchange-balance targets indexed",
    "required blockers before action embedding preserved",
    "required blockers before C_k variation preserved",
    "required blockers before empirical discriminator claims preserved",
    "no proof execution",
    "no new theorem discharge",
    "no CCFT validation",
    "no action embedding",
    "no C_k variation",
    "no empirical validation",
    "no seam closure",
    "no master-action promotion",
]
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_TARGET = (
    "prepare_ccft_empirical_discriminator_candidate_map_packet"
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_REVIEW_TARGET = (
    "review_ccft_empirical_discriminator_candidate_map_packet_result"
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_OUTCOME = (
    "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_PREPARED_MEASURABLE_"
    "SYSTEM_AND_FALSIFIER_CANDIDATES_NO_EMPIRICAL_VALIDATION_OR_SEAM_CLOSURE"
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_STRICT_OUTCOME = (
    "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_PREPARED_AS_PLANNING_"
    "MAP_NO_CCFT_VALIDATION_OR_MASTER_ACTION_PROMOTION"
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_TARGET = (
    "prepare_ccft_empirical_discriminator_candidate_priority_selection_packet"
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_REVIEW_TARGET = (
    "review_ccft_empirical_discriminator_candidate_priority_selection_packet_result"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_candidate_packet"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_candidate_packet_result"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_tolerance_registry_packet"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_tolerance_registry_packet_result"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_PREPARED_"
    "REGISTERS_NON_EXECUTED_TOLERANCE_TRACEABILITY_ROWS_NO_EMPIRICAL_"
    "CALIBRATION_OR_CCFT_VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_PREPARED_"
    "AS_TRACEABILITY_AND_COMPARISON_LOGIC_REGISTRY_NO_EXECUTION_OR_MASTER_"
    "ACTION_PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_REVIEW_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_RESULT_"
    "REVIEW_ACCEPTS_NON_EXECUTED_TOLERANCE_TRACEABILITY_ROWS_ONLY_NO_"
    "EMPIRICAL_CALIBRATION_OR_CCFT_VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_REVIEW_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_RESULT_"
    "REVIEW_ACCEPTS_TRACEABILITY_ONLY_NO_STATISTICAL_VALIDATION_NO_EXECUTION_"
    "SUFFICIENCY_NO_MASTER_ACTION_PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_comparison_"
    "semantics_packet"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_baseline_comparison_"
    "semantics_packet_result"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_KIND = (
    "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_TOLERANCE_REVIEW_SUGGESTED_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_"
    "PACKET_PREPARED_NON_EXECUTED_BASELINE_COMPARISON_LOGIC_NO_EMPIRICAL_"
    "VALIDATION_OR_CCFT_VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_TOLERANCE_REVIEW_SUGGESTED_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_"
    "PACKET_PREPARED_AS_PLANNING_SEMANTICS_ONLY_NO_PROTOCOL_EXECUTION_OR_"
    "MASTER_ACTION_PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_result_review"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_"
    "PACKET_PREPARED_DEFINES_NON_EXECUTED_BASELINE_COMPARISON_SEMANTICS_"
    "NO_BASELINE_SEPARATION_CLAIM_OR_CCFT_VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_"
    "PACKET_PREPARED_COMPARISON_LOGIC_ONLY_NO_EMPIRICAL_PROTOCOL_NO_"
    "STATISTICAL_VALIDATION_NO_MASTER_ACTION_PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_"
    "PACKET_RESULT_REVIEW_ACCEPTS_NON_EXECUTED_BASELINE_COMPARISON_SEMANTICS_"
    "ONLY_NO_BASELINE_SEPARATION_CLAIM_OR_CCFT_VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_"
    "PACKET_RESULT_REVIEW_ACCEPTS_COMPARISON_LOGIC_ONLY_NO_EMPIRICAL_PROTOCOL_"
    "NO_STATISTICAL_VALIDATION_NO_MASTER_ACTION_PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_observable_definition_"
    "semantics_packet"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_observable_definition_"
    "semantics_packet_result"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_KIND = (
    "selected_ccft_empirical_discriminator_observable_definition_semantics_packet"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_observable_definition_semantics_packet_result_review"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_PACKET_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_"
    "PACKET_PREPARED_DEFINES_COHERENCE_LIFETIME_RESIDUAL_CANDIDATE_AS_"
    "NON_EXECUTED_OBSERVABLE_SEMANTICS_NO_EMPIRICAL_RESIDUAL_OR_CCFT_"
    "VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_PACKET_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_"
    "PACKET_PREPARED_OBSERVABLE_MEANING_ONLY_NO_MEASUREMENT_PROTOCOL_NO_"
    "STATISTICAL_VALIDATION_NO_MASTER_ACTION_PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_"
    "PACKET_RESULT_REVIEW_ACCEPTS_COHERENCE_LIFETIME_RESIDUAL_CANDIDATE_AS_"
    "NON_EXECUTED_OBSERVABLE_SEMANTICS_ONLY_NO_EMPIRICAL_RESIDUAL_OR_CCFT_"
    "VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_"
    "PACKET_RESULT_REVIEW_ACCEPTS_OBSERVABLE_MEANING_ONLY_NO_MEASUREMENT_"
    "PROTOCOL_NO_STATISTICAL_VALIDATION_NO_MASTER_ACTION_PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_SUGGESTED_OUTCOME = (
    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_PACKET_OUTCOME
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_SUGGESTED_STRICT_OUTCOME = (
    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_PACKET_STRICT_OUTCOME
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_residual_formula_selection_packet"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_KIND = (
    "selected_ccft_empirical_discriminator_residual_formula_selection_packet"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_SUGGESTED_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_PACKET_"
    "PREPARED_SELECTS_NORMALIZED_COHERENCE_LIFETIME_RESIDUAL_FORMULA_FOR_"
    "FUTURE_COMPARISON_ONLY_NO_EMPIRICAL_RESIDUAL_OR_CCFT_VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_SUGGESTED_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_PACKET_"
    "PREPARED_FORMULA_SELECTION_ONLY_NO_MEASUREMENT_PROTOCOL_NO_STATISTICAL_"
    "VALIDATION_NO_MASTER_ACTION_PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_PACKET_OUTCOME = (
    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_SUGGESTED_OUTCOME
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_PACKET_STRICT_OUTCOME = (
    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_SUGGESTED_STRICT_OUTCOME
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_residual_formula_selection_"
    "packet_result"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_residual_formula_selection_packet_result_review"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_PACKET_"
    "RESULT_REVIEW_ACCEPTS_NORMALIZED_COHERENCE_LIFETIME_RESIDUAL_FORMULA_"
    "FOR_FUTURE_COMPARISON_ONLY_NO_EMPIRICAL_RESIDUAL_OR_CCFT_VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_PACKET_"
    "RESULT_REVIEW_ACCEPTS_FORMULA_SELECTION_ONLY_NO_MEASUREMENT_PROTOCOL_NO_"
    "STATISTICAL_VALIDATION_NO_MASTER_ACTION_PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_measurement_feedback_"
    "baseline_pressure_packet"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_KIND = (
    "selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_SUGGESTED_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_"
    "PRESSURE_PACKET_PREPARED_RECORDS_QUANTUM_MEASUREMENT_FEEDBACK_AS_"
    "LITERATURE_BASELINE_PRESSURE_ONLY_NO_CCFT_VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_SUGGESTED_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_"
    "PRESSURE_PACKET_PREPARED_REFERENCE_BASELINE_NOTE_ONLY_NO_PROTOCOL_"
    "EXECUTION_NO_MASTER_ACTION_PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_OUTCOME = (
    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_SUGGESTED_OUTCOME
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_STRICT_OUTCOME = (
    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_SUGGESTED_STRICT_OUTCOME
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_measurement_feedback_"
    "baseline_pressure_packet_result"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_KIND = (
    "selected_ccft_empirical_discriminator_measurement_feedback_baseline_"
    "pressure_packet_result_review"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_"
    "PRESSURE_PACKET_RESULT_REVIEW_ACCEPTS_ARXIV_2503_13615_AS_LITERATURE_"
    "BASELINE_PRESSURE_ONLY_NO_TOE_OR_CCFT_EVIDENCE"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_"
    "PRESSURE_PACKET_RESULT_REVIEW_ACCEPTS_BASELINE_HARDENING_ONLY_NO_"
    "EMPIRICAL_VALIDATION_NO_PROTOCOL_READINESS_NO_MASTER_ACTION_PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_component_registry_packet"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_KIND = (
    "selected_ccft_empirical_discriminator_baseline_component_registry_packet"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_SUGGESTED_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_"
    "PACKET_PREPARED_LISTS_FUTURE_TAU_BASELINE_COMPONENTS_FOR_COMPARISON_"
    "ONLY_NO_EMPIRICAL_VALIDATION_OR_CCFT_VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_SUGGESTED_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_"
    "PACKET_PREPARED_COMPONENT_REGISTRY_ONLY_NO_PROTOCOL_READINESS_NO_"
    "MASTER_ACTION_PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_FIELDS = [
    "tolerance_id",
    "observable_binding",
    "baseline_binding",
    "comparison_semantics",
    "null_condition",
    "source_status",
    "execution_status",
    "claim_boundary",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_ROWS = [
    {
        "tolerance_id": "TOL-CCFT-MESO-COH-LIFETIME-RESIDUAL-v0",
        "observable_binding": "coherence_lifetime_residual_candidate",
        "baseline_binding": "standard_open_system_decoherence_baseline_comparison",
        "comparison_semantics": (
            "placeholder comparison-logic row; future protocol must choose "
            "absolute residual, normalized residual, confidence interval "
            "separation, or effect-size threshold before any execution"
        ),
        "null_condition": (
            "null_separation_from_baseline_with_registered_tolerances"
        ),
        "source_status": "placeholder_future_empirical_calibration_needed",
        "execution_status": "not_executed",
        "claim_boundary": (
            "no empirical validation, no CCFT validation, no protocol execution"
        ),
    }
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_COMPARISON_SEMANTICS = [
    "absolute_residual_placeholder",
    "normalized_residual_placeholder",
    "confidence_interval_separation_placeholder",
    "effect_size_threshold_placeholder",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_BOUNDARY = (
    "This packet registers tolerance traceability and comparison-logic rows "
    "for the selected CCFT empirical discriminator candidate only. It does "
    "not calibrate tolerances from data, validate CCFT, validate any empirical "
    "claim, authorize protocol design or execution, show separation from "
    "baseline physics, bind to a measurement campaign, close any pillar or "
    "seam, promote C_k, embed or vary C_k in an action, or promote the master "
    "action."
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_REVIEW_ACCEPTANCE_ITEMS = [
    "selected CCFT empirical discriminator tolerance registry packet accepted",
    "selected-candidate packet result review consumed",
    "controlled mesoscopic coherence platform candidate preserved",
    "coherence lifetime residual observable binding preserved",
    "standard open-system decoherence baseline binding preserved",
    "null separation falsifier condition preserved",
    "tolerance traceability fields accepted",
    "non-executed tolerance traceability row accepted",
    "comparison semantics accepted as placeholders only",
    "registered_tolerances treated as traceability infrastructure only",
    "registered_tolerances not treated as empirically calibrated",
    "registered_tolerances not treated as statistically validated",
    "registered_tolerances not treated as sufficient for execution",
    "registered_tolerances not treated as baseline-separation evidence",
    "registered_tolerances not bound to a measurement campaign",
    "tolerance row not accepted as a test protocol",
    "tolerance row not accepted as an effect-size threshold",
    "tolerance row not accepted as a statistical decision rule",
    "tolerance row not accepted as experimental design",
    "future empirical calibration remains required",
    "baseline-comparison semantics packet selected as next planning target",
    "no proof execution",
    "no new theorem discharge",
    "no CCFT validation",
    "no empirical validation",
    "no pillar closure",
    "no seam closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no scalar/QFT closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no C_k variation",
    "no master-action promotion",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_FIELDS = [
    "baseline_semantics_id",
    "candidate_binding",
    "observable_binding",
    "baseline_binding",
    "residual_definition_status",
    "comparison_direction",
    "null_default",
    "tolerance_binding",
    "execution_status",
    "claim_boundary",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_ROWS = [
    {
        "baseline_semantics_id": "BSEM-CCFT-MESO-COH-LIFETIME-v0",
        "candidate_binding": "controlled_mesoscopic_coherence_platform_candidate",
        "observable_binding": "coherence_lifetime_residual_candidate",
        "baseline_binding": "standard_open_system_decoherence_baseline_comparison",
        "residual_definition_status": "placeholder_future_refinement_needed",
        "comparison_direction": (
            "placeholder comparison direction; future packet must choose "
            "longer lifetime, shorter lifetime, absolute deviation magnitude, "
            "normalized deviation, or signed residual before any execution"
        ),
        "null_default": (
            "null_separation_from_baseline_with_registered_tolerances"
        ),
        "tolerance_binding": "TOL-CCFT-MESO-COH-LIFETIME-RESIDUAL-v0",
        "execution_status": "not_executed",
        "claim_boundary": (
            "no empirical validation, no CCFT validation, no baseline-separation claim"
        ),
    }
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_BOUNDARY = (
    "This packet defines only non-executed baseline-comparison semantics for "
    "a future coherence-lifetime residual comparison against the standard "
    "open-system decoherence baseline. It does not claim the baseline is "
    "complete, experimentally fitted, or sufficient; does not observe a "
    "residual; does not treat registered tolerances as significance criteria; "
    "does not claim CCFT predicts measurable separation; does not authorize "
    "an empirical protocol; does not validate CCFT; does not close any pillar "
    "or seam; and does not promote the master action."
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_ACCEPTANCE_ITEMS = [
    "baseline-comparison semantics packet accepted",
    "controlled mesoscopic coherence platform candidate preserved",
    "coherence lifetime residual observable binding preserved",
    "standard open-system decoherence baseline binding preserved",
    "null default preserved",
    "tolerance traceability binding consumed as traceability-only prior",
    "baseline-comparison semantics accepted as non-executed comparison logic only",
    "residual definition status accepted as placeholder only",
    "comparison direction accepted as placeholder only",
    "baseline not accepted as complete",
    "baseline adequacy not accepted",
    "baseline empirical fit quality not accepted",
    "statistical decision-rule validity not accepted",
    "observed separation not accepted",
    "CCFT-predicted separation not accepted",
    "experimental protocol readiness not accepted",
    "observable-definition semantics packet selected as next planning target",
    "no proof execution",
    "no new theorem discharge",
    "no empirical validation",
    "no CCFT validation",
    "no baseline-separation claim",
    "no empirical protocol",
    "no statistical validation",
    "no pillar closure",
    "no seam closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no scalar/QFT closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no C_k variation",
    "no master-action promotion",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_FIELDS = [
    "observable_id",
    "candidate_platform_binding",
    "baseline_binding",
    "residual_semantics",
    "comparison_direction_status",
    "tolerance_binding",
    "null_default",
    "execution_status",
    "claim_boundary",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_ROWS = [
    {
        "observable_id": "coherence_lifetime_residual_candidate",
        "candidate_platform_binding": (
            "controlled_mesoscopic_coherence_platform_candidate"
        ),
        "baseline_binding": "standard_open_system_decoherence_baseline_comparison",
        "residual_semantics": (
            "future comparison object only; candidate residual meaning is "
            "reserved for a later coherence-lifetime quantity compared with "
            "the registered baseline, not an observed empirical residual, "
            "not a CCFT-predicted residual, and not a statistically "
            "validated deviation"
        ),
        "comparison_direction_status": (
            "undefined and refinement-pending; longer lifetime, shorter "
            "lifetime, absolute deviation magnitude, normalized deviation, "
            "and signed residual remain unselected"
        ),
        "tolerance_binding": "TOL-CCFT-MESO-COH-LIFETIME-RESIDUAL-v0",
        "null_default": (
            "null_separation_from_baseline_with_registered_tolerances"
        ),
        "execution_status": "not_executed",
        "claim_boundary": (
            "no empirical residual, no CCFT validation, no measurement "
            "protocol, no statistical validation, no baseline-separation claim"
        ),
    }
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_BOUNDARY = (
    "This packet defines only the meaning of "
    "coherence_lifetime_residual_candidate as a future comparison object for "
    "the selected controlled mesoscopic coherence platform against the "
    "standard open-system decoherence baseline. It does not assert an "
    "observed empirical residual, a CCFT-predicted residual, a statistically "
    "significant deviation, an executable measurement protocol, a validated "
    "discriminator, or separation from the baseline; it does not validate "
    "CCFT, close any pillar or seam, embed or vary C_k in an action, or "
    "promote the master action."
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_ACCEPTANCE_ITEMS = [
    "observable-definition semantics packet accepted",
    "coherence_lifetime_residual_candidate accepted as a future comparison object only",
    "controlled mesoscopic coherence platform candidate preserved",
    "standard open-system decoherence baseline binding preserved",
    "registered tolerance binding preserved as traceability only",
    "null default preserved as null separation with registered tolerances",
    "observable semantics accepted as meaning-only",
    "observable-definition row accepted as non-executed only",
    "comparison direction remains refinement-pending",
    "residual formula remains unselected",
    "observed empirical residual not accepted",
    "CCFT-predicted residual not accepted",
    "statistical effect size not accepted",
    "measured coherence anomaly not accepted",
    "baseline separation not accepted",
    "measurement protocol readiness not accepted",
    "empirical confirmation not accepted",
    "residual-formula selection packet selected as next planning target",
    "no proof execution",
    "no new theorem discharge",
    "no empirical validation",
    "no CCFT validation",
    "no baseline-separation claim",
    "no empirical protocol",
    "no statistical validation",
    "no pillar closure",
    "no seam closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no scalar/QFT closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no C_k variation",
    "no master-action promotion",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_FIELDS = [
    "formula_id",
    "formula_type",
    "formula",
    "plain_meaning",
    "selection_status",
    "main_risk",
    "claim_boundary",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_ROWS = [
    {
        "formula_id": "absolute_lifetime_difference",
        "formula_type": "lifetime_difference",
        "formula": "Delta_tau = tau_candidate - tau_baseline",
        "plain_meaning": "simple lifetime difference",
        "selection_status": "deferred_candidate",
        "main_risk": "depends heavily on units and scale",
        "claim_boundary": (
            "future comparison formula candidate only; no empirical residual "
            "or CCFT validation"
        ),
    },
    {
        "formula_id": "lifetime_ratio",
        "formula_type": "lifetime_ratio",
        "formula": "R_tau = tau_candidate / tau_baseline",
        "plain_meaning": "lifetime ratio",
        "selection_status": "deferred_candidate",
        "main_risk": "can hide absolute size",
        "claim_boundary": (
            "future comparison formula candidate only; no empirical residual "
            "or CCFT validation"
        ),
    },
    {
        "formula_id": "normalized_lifetime_residual",
        "formula_type": "normalized_lifetime_residual",
        "formula": "r_tau = (tau_candidate - tau_baseline) / tau_baseline",
        "plain_meaning": (
            "candidate coherence lifetime relative to baseline as a fraction "
            "of the baseline"
        ),
        "selection_status": "selected_primary_future_comparison_formula",
        "main_risk": (
            "baseline denominator convention must remain explicit before any "
            "protocol or statistical use"
        ),
        "claim_boundary": (
            "selected formula shape only; no observed residual, no predicted "
            "CCFT residual, no statistical effect size, and no baseline "
            "separation claim"
        ),
    },
    {
        "formula_id": "decay_rate_difference",
        "formula_type": "decay_rate_difference",
        "formula": "Delta_gamma = gamma_candidate - gamma_baseline",
        "plain_meaning": "decay-rate difference",
        "selection_status": "retained_later_comparison_candidate",
        "main_risk": (
            "may be more natural for decoherence models but changes the "
            "interpretive object from lifetime to rate"
        ),
        "claim_boundary": (
            "retained for later comparison only; no empirical residual or "
            "CCFT validation"
        ),
    },
    {
        "formula_id": "log_lifetime_ratio",
        "formula_type": "symmetric_ratio",
        "formula": "log_R_tau = log(tau_candidate / tau_baseline)",
        "plain_meaning": "symmetric ratio form",
        "selection_status": "deferred_candidate",
        "main_risk": "more abstract and less plain",
        "claim_boundary": (
            "future comparison formula candidate only; no empirical residual "
            "or CCFT validation"
        ),
    },
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_BOUNDARY = (
    "This packet selects only the normalized coherence-lifetime residual "
    "formula shape r_tau = (tau_candidate - tau_baseline) / tau_baseline for "
    "future comparison use. It does not claim that the residual exists, has "
    "been observed, is predicted by CCFT, separates from the baseline, has a "
    "statistical effect size, is ready for measurement-protocol design, "
    "validates CCFT, closes any pillar or seam, embeds or varies C_k in an "
    "action, or promotes the master action."
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_ITEMS = [
    "residual formula selection packet prepared",
    "observable-definition semantics result review consumed",
    "coherence_lifetime_residual_candidate preserved",
    "controlled mesoscopic coherence platform candidate preserved",
    "standard open-system decoherence baseline binding preserved",
    "registered tolerance binding preserved as traceability only",
    "absolute lifetime difference compared and deferred",
    "lifetime ratio compared and deferred",
    "normalized lifetime residual selected as primary future comparison formula",
    "decay-rate difference retained as later comparison candidate",
    "log lifetime ratio compared and deferred",
    "residual formula selected as formula shape only",
    "formula selected for future comparison use only",
    "no observed empirical residual",
    "no CCFT-predicted residual",
    "no measured coherence anomaly",
    "no statistical effect size",
    "no baseline separation",
    "no measurement protocol readiness",
    "no empirical confirmation",
    "no proof execution",
    "no new theorem discharge",
    "no empirical validation",
    "no CCFT validation",
    "no empirical protocol",
    "no statistical validation",
    "no pillar closure",
    "no seam closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no scalar/QFT closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no C_k variation",
    "no master-action promotion",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_ACCEPTANCE_ITEMS = [
    "residual formula selection packet accepted",
    "normalized coherence-lifetime residual formula accepted as future comparison formula only",
    "r_tau formula retained as scale-free lifetime comparison shape",
    "tau_baseline positive nonzero precondition recorded",
    "tau_candidate not accepted as observed value",
    "tau_candidate not accepted as CCFT-derived prediction",
    "r_tau accepted as dimensionless because lifetime units cancel",
    "r_tau equals zero means no lifetime separation from baseline if later measured or derived",
    "r_tau greater than zero would mean longer candidate lifetime than baseline if later measured or derived",
    "r_tau less than zero would mean shorter candidate lifetime than baseline if later measured or derived",
    "sign semantics not accepted as current empirical evidence",
    "external measurement-feedback Hamiltonian-control source recorded as future baseline pressure only",
    "measurement-feedback baseline-pressure packet selected as next planning target",
    "no proof execution",
    "no new theorem discharge",
    "no observed empirical residual",
    "no CCFT-predicted residual",
    "no measured coherence anomaly",
    "no statistical effect size",
    "no baseline separation",
    "no measurement protocol readiness",
    "no empirical confirmation",
    "no empirical validation",
    "no CCFT validation",
    "no empirical protocol",
    "no statistical validation",
    "no pillar closure",
    "no seam closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no scalar/QFT closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no C_k variation",
    "no master-action promotion",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_BOUNDARY = (
    "This result review accepts only the normalized coherence-lifetime "
    "residual formula r_tau = (tau_candidate - tau_baseline) / tau_baseline "
    "as a future comparison formula. It records that tau_baseline must be "
    "positive and nonzero, that tau_candidate is neither observed nor "
    "CCFT-derived here, that r_tau is dimensionless, and that sign semantics "
    "are interpretive only if later measured or derived. It also records "
    "measurement-feedback Hamiltonian-control literature as future baseline "
    "pressure only. It does not claim an observed residual, a CCFT prediction, "
    "baseline separation, measurement-protocol readiness, statistical "
    "validation, empirical confirmation, CCFT validation, C_k promotion, "
    "action embedding, or master-action promotion."
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_SOURCE = {
    "source_id": "arxiv_2503_13615_reshaping_quantum_arrow_of_time",
    "title": "Reshaping the Quantum Arrow of Time",
    "arxiv_id": "2503.13615",
    "source_url": "https://arxiv.org/abs/2503.13615",
    "authors": [
        "Luis Pedro Garcia-Pintos",
        "Yi-Kai Liu",
        "Alexey V. Gorshkov",
    ],
    "submitted": "2025-03-17",
    "last_revised": "2025-12-22",
    "source_status": "external_literature_baseline_pressure_only",
}
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_COMPONENTS = [
    "standard open-system decoherence",
    "continuous or repeated quantum measurement",
    "measurement back-action",
    "feedback Hamiltonian control",
    "detector efficiency limits",
    "feedback delay",
    "monitoring-induced energy flow",
    "quantum thermodynamic accounting",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_FIELDS = [
    "pressure_id",
    "standard_physics_effect",
    "future_baseline_implication",
    "claim_boundary",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_ROWS = [
    {
        "pressure_id": "measurement_feedback_monitored_quantum_trajectories",
        "standard_physics_effect": (
            "monitored quantum trajectories can carry a measurement-induced "
            "arrow-of-time structure"
        ),
        "future_baseline_implication": (
            "future tau_baseline cannot treat measurement as passive bookkeeping"
        ),
        "claim_boundary": "baseline pressure only; no CCFT evidence",
    },
    {
        "pressure_id": "explicit_hamiltonian_control",
        "standard_physics_effect": (
            "explicit Hamiltonian control can reproduce or counteract monitored "
            "trajectory behavior"
        ),
        "future_baseline_implication": (
            "future tau_baseline may need Hamiltonian-control terms before any "
            "residual interpretation"
        ),
        "claim_boundary": "baseline pressure only; no master-action support",
    },
    {
        "pressure_id": "feedback_reversed_arrow_trajectories",
        "standard_physics_effect": (
            "feedback can generate trajectories consistent with a reversed "
            "measurement arrow of time"
        ),
        "future_baseline_implication": (
            "apparent time-arrow anomalies are not sufficient CCFT discriminators"
        ),
        "claim_boundary": "baseline pressure only; no ToE truth claim",
    },
    {
        "pressure_id": "open_system_backward_dynamics_simulation",
        "standard_physics_effect": (
            "standard control tools can simulate backward-in-time open-system "
            "dynamics"
        ),
        "future_baseline_implication": (
            "future residual claims must beat open-system control baselines"
        ),
        "claim_boundary": "baseline pressure only; no baseline separation",
    },
    {
        "pressure_id": "continuous_measurement_engine",
        "standard_physics_effect": (
            "continuous measurement can power a feedback-driven measurement engine"
        ),
        "future_baseline_implication": (
            "future baselines may need monitoring-induced energy-flow accounting"
        ),
        "claim_boundary": "baseline pressure only; no empirical validation",
    },
    {
        "pressure_id": "monitoring_induced_energy_flow",
        "standard_physics_effect": (
            "monitoring can pump energy into the controlled quantum system"
        ),
        "future_baseline_implication": (
            "future baselines should include quantum thermodynamic energy "
            "accounting before any residual is interpreted"
        ),
        "claim_boundary": "baseline pressure only; no CCFT prediction",
    },
    {
        "pressure_id": "finite_efficiency_measurement_regime",
        "standard_physics_effect": (
            "finite-efficiency measurement regimes remain part of the external "
            "standard-physics pressure source"
        ),
        "future_baseline_implication": (
            "future baselines should not assume ideal detector efficiency"
        ),
        "claim_boundary": "baseline pressure only; no statistical validation",
    },
    {
        "pressure_id": "feedback_delay_regime",
        "standard_physics_effect": (
            "feedback delay can be modeled inside experimentally realizable "
            "measurement-feedback conditions"
        ),
        "future_baseline_implication": (
            "future baselines should account for finite control-loop delay"
        ),
        "claim_boundary": "baseline pressure only; no protocol execution",
    },
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_BOUNDARY = (
    "This packet records arXiv:2503.13615, Reshaping the Quantum Arrow of "
    "Time, as literature baseline pressure only. It records that standard "
    "quantum measurement, feedback, Hamiltonian control, detector efficiency "
    "limits, feedback delay, monitoring-induced energy flow, and quantum "
    "thermodynamic accounting can strengthen a future tau_baseline before "
    "any normalized coherence-lifetime residual can be meaningful. It does "
    "not treat the source as ToE evidence, CCFT evidence, empirical "
    "validation, baseline separation, measurement-protocol readiness, "
    "statistical validation, C_k promotion, action embedding, or "
    "master-action support."
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_ITEMS = [
    "measurement-feedback baseline-pressure packet prepared",
    "residual-formula selection result review consumed",
    "normalized coherence-lifetime residual formula retained",
    "residual formula unchanged by literature baseline pressure",
    "arXiv:2503.13615 recorded as external literature source",
    "source recorded as baseline pressure only",
    "monitored quantum trajectories recorded as standard-physics pressure",
    "explicit Hamiltonian control recorded as standard-physics pressure",
    "feedback-produced reversed-arrow trajectories recorded as standard-physics pressure",
    "backward open-system dynamics simulation recorded as standard-physics pressure",
    "continuous measurement engine recorded as standard-physics pressure",
    "finite-efficiency measurement regime recorded as standard-physics pressure",
    "feedback delay regime recorded as standard-physics pressure",
    "monitoring-induced energy flow recorded as standard-physics pressure",
    "future tau_baseline strengthened beyond ordinary decoherence",
    "future residual claims must compare against measurement-feedback baselines",
    "no observed empirical residual",
    "no CCFT-predicted residual",
    "no measured coherence anomaly",
    "no statistical effect size",
    "no baseline separation",
    "no measurement protocol readiness",
    "no empirical confirmation",
    "no proof execution",
    "no new theorem discharge",
    "no empirical validation",
    "no CCFT validation",
    "no empirical protocol",
    "no statistical validation",
    "no pillar closure",
    "no seam closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no scalar/QFT closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no C_k variation",
    "no master-action promotion",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_ACCEPTANCE_ITEMS = [
    "measurement-feedback baseline-pressure packet accepted",
    "arXiv:2503.13615 accepted as literature baseline pressure only",
    "Reshaping the Quantum Arrow of Time source accepted as baseline-hardening note only",
    "standard measurement-feedback quantum control accepted as future baseline burden",
    "source not accepted as ToE evidence",
    "source not accepted as CCFT evidence",
    "source not accepted as empirical validation",
    "source not accepted as observed residual evidence",
    "source not accepted as baseline separation",
    "source not accepted as protocol readiness",
    "source not accepted as statistical validation",
    "source not accepted as master-action support",
    "future tau_baseline burden strengthened",
    "future residual formula left unchanged",
    "future baseline-component registry selected as next target",
    "no proof execution",
    "no new theorem discharge",
    "no observed empirical residual",
    "no CCFT-predicted residual",
    "no measured coherence anomaly",
    "no statistical effect size",
    "no baseline separation",
    "no measurement protocol readiness",
    "no empirical confirmation",
    "no empirical validation",
    "no CCFT validation",
    "no empirical protocol",
    "no statistical validation",
    "no pillar closure",
    "no seam closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no scalar/QFT closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no C_k variation",
    "no master-action promotion",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_BOUNDARY = (
    "This result review accepts the measurement-feedback baseline-pressure "
    "packet only as a baseline-hardening literature note. It accepts "
    "arXiv:2503.13615, Reshaping the Quantum Arrow of Time, only as evidence "
    "that standard quantum measurement-feedback physics can strengthen a "
    "future tau_baseline. It does not treat the source as ToE evidence, CCFT "
    "evidence, empirical validation, observed residual evidence, baseline "
    "separation, protocol readiness, statistical validation, C_k promotion, "
    "action embedding, or master-action support."
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_OUTCOME = (
    "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_PREPARED_"
    "RANKS_MEASURABLE_SYSTEM_AND_FALSIFIER_ROWS_NO_EMPIRICAL_VALIDATION_OR_"
    "CCFT_VALIDATION"
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_STRICT_OUTCOME = (
    "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_PREPARED_"
    "SELECTS_TOP_DISCRIMINATOR_CANDIDATE_FOR_PACKET_ONLY_NO_EXECUTION_OR_"
    "MASTER_ACTION_PROMOTION"
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_ACTIONS = [
    "consume the accepted empirical discriminator candidate map",
    "rank candidate measurable systems",
    "rank candidate observables",
    "rank candidate falsifier rows",
    "rank candidate baseline-model comparisons",
    "select one top candidate for future packet preparation only",
    "record selection criteria",
    "record rejected or deferred candidates",
    "preserve that no empirical test is executed",
    "preserve that no CCFT validation is claimed",
]
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_CRITERIA = [
    "measurability",
    "falsifiability",
    "baseline-model comparability",
    "clarity of CCFT observable mapping",
    "near-term feasibility",
    "risk of overclaim",
    "relevance to CCFT as candidate mesoscopic bridge layer",
]
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_MEASURABLE_SYSTEM_RANKING = [
    "rank_1_controlled_mesoscopic_coherence_platform_candidate",
    "rank_2_condensed_matter_collective_coherence_platform_candidate",
    "rank_3_astronomical_coherence_proxy_candidate",
]
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_OBSERVABLE_RANKING = [
    "rank_1_coherence_lifetime_residual_candidate",
    "rank_2_phase_correlation_transport_residual_candidate",
    "rank_3_noise_spectrum_coherence_residual_candidate",
]
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_FALSIFIER_RANKING = [
    "rank_1_null_separation_from_baseline_with_registered_tolerances",
    "rank_2_sign_incompatible_residual_against_candidate_mapping",
    "rank_3_protocol_dependence_without_reproducible_system_control",
]
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_BASELINE_RANKING = [
    "rank_1_standard_open_system_decoherence_baseline_comparison",
    "rank_2_numerical_surrogate_model_comparison",
    "rank_3_environmental_noise_systematics_comparison",
]
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTED_TOP_CANDIDATE = (
    "controlled_mesoscopic_coherence_platform_candidate"
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_DEFERRED_CANDIDATES = [
    "condensed_matter_collective_coherence_platform_candidate",
    "astronomical_coherence_proxy_candidate",
]
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_BOUNDARY = (
    "This packet ranks empirical-discriminator candidate rows and selects one "
    "top candidate for future packet preparation only. It does not execute an "
    "empirical test, validate CCFT, validate any empirical claim, close any "
    "pillar or seam, promote C_k, embed or vary C_k in an action, or promote "
    "the master action."
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_REVIEW_OUTCOME = (
    "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_RESULT_"
    "REVIEW_ACCEPTS_TOP_DISCRIMINATOR_PRIORITY_FOR_FUTURE_PACKET_ONLY_NO_"
    "EMPIRICAL_VALIDATION_OR_CCFT_VALIDATION"
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_REVIEW_STRICT_OUTCOME = (
    "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_RESULT_"
    "REVIEW_ACCEPTS_PRIORITY_SELECTION_AS_PLANNING_ONLY_NO_EXECUTION_OR_"
    "MASTER_ACTION_PROMOTION"
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_REVIEW_ACCEPTANCE_ITEMS = [
    "CCFT empirical discriminator candidate priority selection accepted",
    "accepted empirical discriminator candidate map consumed",
    "candidate measurable systems ranked",
    "candidate observables ranked",
    "candidate falsifier rows ranked",
    "candidate baseline-model comparisons ranked",
    "selected top candidate retained for future packet preparation only",
    "selection criteria preserved",
    "rejected or deferred candidates preserved",
    "selected top discriminator remains packet-level priority candidate only",
    "no empirical test executed",
    "no proof execution",
    "no new theorem discharge",
    "no CCFT validation",
    "no empirical validation",
    "no pillar closure",
    "no seam closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no scalar/QFT closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no C_k variation",
    "no master-action promotion",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_PREPARED_"
    "CONTROLLED_MESOSCOPIC_COHERENCE_PLATFORM_CANDIDATE_NO_EMPIRICAL_"
    "VALIDATION_OR_CCFT_VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_PREPARED_AS_"
    "BOUNDED_CANDIDATE_SPECIFICATION_NO_EXECUTION_OR_MASTER_ACTION_PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_ACTIONS = [
    "consume the accepted priority-selection result review",
    "instantiate controlled_mesoscopic_coherence_platform_candidate",
    "bind coherence_lifetime_residual_candidate as selected observable row",
    "bind standard_open_system_decoherence_baseline_comparison as selected baseline row",
    "bind null_separation_from_baseline_with_registered_tolerances as selected falsifier row",
    "record candidate control-variable placeholders",
    "record numerical-vs-physical comparison placeholders",
    "record blockers before empirical protocol design",
    "record blockers before empirical execution",
    "preserve that no empirical validation is claimed",
    "preserve that no CCFT validation is claimed",
]
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_BOUNDARY = (
    "This packet instantiates the selected CCFT empirical discriminator "
    "candidate as a bounded future-packet candidate only. It does not execute "
    "an empirical protocol, authorize empirical execution, validate CCFT, "
    "validate any empirical claim, close any pillar or seam, promote C_k, "
    "embed or vary C_k in an action, or promote the master action."
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_ID = (
    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTED_TOP_CANDIDATE
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_OBSERVABLE = (
    "coherence_lifetime_residual_candidate"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_BASELINE = (
    "standard_open_system_decoherence_baseline_comparison"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_FALSIFIER = (
    "null_separation_from_baseline_with_registered_tolerances"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_REVIEW_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_RESULT_REVIEW_"
    "ACCEPTS_CONTROLLED_MESOSCOPIC_COHERENCE_PLATFORM_CANDIDATE_AS_FUTURE_"
    "PACKET_ONLY_NO_EMPIRICAL_VALIDATION_OR_CCFT_VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_REVIEW_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_RESULT_REVIEW_"
    "ACCEPTS_BOUNDED_CANDIDATE_SPECIFICATION_NO_EXECUTION_OR_MASTER_ACTION_"
    "PROMOTION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_REVIEW_ACCEPTANCE_ITEMS = [
    "selected CCFT empirical discriminator candidate packet accepted",
    "accepted priority-selection result review consumed",
    "controlled mesoscopic coherence platform candidate accepted as future packet only",
    "coherence lifetime residual candidate accepted as selected observable row",
    "standard open-system decoherence baseline comparison accepted as selected baseline row",
    "null separation from baseline with registered tolerances accepted as selected falsifier row",
    "registered_tolerances treated as non-executed traceability placeholder only",
    "registered_tolerances not treated as empirically calibrated",
    "candidate control-variable placeholders preserved",
    "numerical-vs-physical comparison placeholders preserved",
    "blockers before empirical protocol design preserved",
    "blockers before empirical execution preserved",
    "no empirical protocol design authorized",
    "no empirical execution authorization",
    "no empirical test executed",
    "no proof execution",
    "no new theorem discharge",
    "no CCFT validation",
    "no empirical validation",
    "no pillar closure",
    "no seam closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no scalar/QFT closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no C_k variation",
    "no master-action promotion",
]
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_REVIEW_OUTCOME = (
    "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_RESULT_REVIEW_ACCEPTS_"
    "MEASURABLE_SYSTEM_AND_FALSIFIER_CANDIDATE_MAP_NO_EMPIRICAL_VALIDATION_"
    "OR_SEAM_CLOSURE"
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_REVIEW_STRICT_OUTCOME = (
    "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_RESULT_REVIEW_ACCEPTS_"
    "PLANNING_MAP_NO_CCFT_VALIDATION_OR_MASTER_ACTION_PROMOTION"
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_TARGETS = [
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
]
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_BOUNDARY = (
    "This packet indexes empirical-discriminator planning candidates only. "
    "It does not execute proof work, discharge theorems, validate CCFT, "
    "validate any empirical claim, close any pillar or seam, promote C_k, "
    "embed or vary C_k in an action, or promote the master action."
)
CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_REVIEW_ACCEPTANCE_ITEMS = [
    "CCFT empirical discriminator candidate map accepted",
    "candidate measurable systems indexed",
    "candidate observables indexed",
    "candidate control variables indexed",
    "candidate baseline models indexed",
    "candidate failure modes indexed",
    "candidate falsifiers indexed",
    "candidate numerical-vs-physical comparison routes indexed",
    "candidate empirical-discriminator questions indexed",
    "required blockers before empirical claim preserved",
    "required blockers before CCFT validation preserved",
    "required blockers before pillar or seam relevance preserved",
    "no proof execution",
    "no new theorem discharge",
    "no CCFT validation",
    "no empirical validation",
    "no pillar closure",
    "no seam closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no scalar/QFT closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no C_k variation",
    "no master-action promotion",
]

NONCLAIMS = [
    "no proof execution",
    "no new theorem discharge",
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
    "no CCFT validation",
    "no master-action promotion",
]
ROADMAP_REBASE_BOUNDARY = (
    "This roadmap rebase indexes CCFT as a candidate mesoscopic coherence "
    "bridge layer only. It does not validate CCFT, promote CCFT as "
    "fundamental physics, derive CCFT from the master action, embed C_k in "
    "the action, vary C_k, close any pillar, close any seam, authorize "
    "empirical validation, or promote the master action."
)
TRIAD_BOUNDARY = (
    "This packet records only the local phi source/bridge/transport "
    "theorem-linkage triad. It is not a phi C_k rule-family closeout and "
    "does not overwrite or reinterpret the historical 2026-06-19 phi "
    "rule-family artifacts."
)


@dataclass(frozen=True)
class StageSpec:
    key: str
    schema_id: str
    packet_id: str
    status: str
    outcome_id: str
    strict_outcome_id: str
    consumed_target: str
    consumed_target_kind: str
    selected_next_target: str
    selected_next_target_kind: str
    lean_module: str
    json_filename: str
    result_kind: str
    packet_classification: str
    stage_role: str


STAGES: dict[str, StageSpec] = {
    "selector": StageSpec(
        key="selector",
        schema_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_20260702_v0"
        ),
        packet_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_v0"
        ),
        status=(
            "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_"
            "TRANSPORT_CLOSEOUT"
        ),
        outcome_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_SELECTS_PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_"
            "FAMILY_SYNTHESIS_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
        ),
        strict_outcome_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_SELECTS_LOCAL_PHI_THEOREM_LINKAGE_TRIAD_SYNTHESIS_NO_GAP_"
            "DISCHARGE_OR_CK_RULE_PROMOTION"
        ),
        consumed_target=(
            "select_next_ck_family_theorem_linkage_obligation_after_phi_transport_"
            "closeout"
        ),
        consumed_target_kind=(
            "ck_family_theorem_linkage_obligation_selector_after_phi_transport_"
            "closeout"
        ),
        selected_next_target=(
            "review_ck_family_theorem_linkage_obligation_selection_after_phi_"
            "transport_closeout_result"
        ),
        selected_next_target_kind=(
            "ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
            "closeout_result_review"
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "CKFamilyTheoremLinkageObligationSelectionAfterPhiTransportCloseout"
        ),
        json_filename=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_20260702_v0.json"
        ),
        result_kind="selection",
        packet_classification=(
            "post_phi_transport_selector_selects_local_phi_theorem_linkage_triad_"
            "synthesis_only"
        ),
        stage_role="selector",
    ),
    "selector_review": StageSpec(
        key="selector_review",
        schema_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_RESULT_REVIEW_20260702_v0"
        ),
        packet_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_RESULT_REVIEW_v0"
        ),
        status=(
            "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_"
            "TRANSPORT_CLOSEOUT_RESULT_REVIEW"
        ),
        outcome_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_RESULT_REVIEW_ACCEPTS_PHI_CK_SOURCE_BRIDGE_TRANSPORT_"
            "THEOREM_LINKAGE_FAMILY_SYNTHESIS_SELECTION_NO_PROOF_EXECUTION_OR_"
            "MASTER_ACTION_PROMOTION"
        ),
        strict_outcome_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_RESULT_REVIEW_ACCEPTS_LOCAL_PHI_THEOREM_LINKAGE_TRIAD_"
            "SYNTHESIS_SELECTION_NO_GAP_DISCHARGE_OR_CK_RULE_PROMOTION"
        ),
        consumed_target=(
            "review_ck_family_theorem_linkage_obligation_selection_after_phi_"
            "transport_closeout_result"
        ),
        consumed_target_kind=(
            "ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
            "closeout_result_review"
        ),
        selected_next_target=(
            "prepare_phi_ck_source_bridge_transport_theorem_linkage_family_"
            "synthesis_packet"
        ),
        selected_next_target_kind=(
            "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_packet"
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "CKFamilyTheoremLinkageObligationSelectionAfterPhiTransportCloseoutResultReview"
        ),
        json_filename=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_RESULT_REVIEW_20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "post_phi_transport_selector_review_accepts_local_phi_triad_synthesis_"
            "selection_only"
        ),
        stage_role="selector_result_review",
    ),
    "triad_packet": StageSpec(
        key="triad_packet",
        schema_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "PACKET_20260702_v0"
        ),
        packet_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "PACKET_v0"
        ),
        status=(
            "ACTIVE_PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_"
            "SYNTHESIS_PACKET"
        ),
        outcome_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "PACKET_PREPARED_LOCAL_TRIAD_INDEXED_NO_PHI_SECTOR_OR_SEAM_CLOSURE"
        ),
        strict_outcome_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "PACKET_PREPARED_C_SOURCE_C_BRIDGE_C_TRANSPORT_PHI_LOCAL_LINKAGE_"
            "ONLY_NO_CK_RULE_PROMOTION"
        ),
        consumed_target=(
            "prepare_phi_ck_source_bridge_transport_theorem_linkage_family_"
            "synthesis_packet"
        ),
        consumed_target_kind=(
            "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_packet"
        ),
        selected_next_target=(
            "review_phi_ck_source_bridge_transport_theorem_linkage_family_"
            "synthesis_result"
        ),
        selected_next_target_kind=(
            "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
            "result_review"
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "PhiCKSourceBridgeTransportTheoremLinkageFamilySynthesisPacket"
        ),
        json_filename=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "PACKET_20260702_v0.json"
        ),
        result_kind="packet",
        packet_classification=(
            "local_phi_source_bridge_transport_theorem_linkage_triad_index_only"
        ),
        stage_role="triad_synthesis_packet",
    ),
    "triad_review": StageSpec(
        key="triad_review",
        schema_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "RESULT_REVIEW_20260702_v0"
        ),
        packet_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "RESULT_REVIEW_v0"
        ),
        status=(
            "ACTIVE_PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_"
            "SYNTHESIS_RESULT_REVIEW"
        ),
        outcome_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "RESULT_REVIEW_ACCEPTS_LOCAL_TRIAD_INDEX_NO_PHI_SECTOR_OR_SEAM_CLOSURE"
        ),
        strict_outcome_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "RESULT_REVIEW_ACCEPTS_C_SOURCE_C_BRIDGE_C_TRANSPORT_PHI_LOCAL_"
            "LINKAGE_FAMILY_NO_CK_RULE_PROMOTION"
        ),
        consumed_target=(
            "review_phi_ck_source_bridge_transport_theorem_linkage_family_"
            "synthesis_result"
        ),
        consumed_target_kind=(
            "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
            "result_review"
        ),
        selected_next_target="prepare_coherence_admissibility_bridge_roadmap_rebase_packet",
        selected_next_target_kind="coherence_admissibility_bridge_roadmap_rebase_packet",
        lean_module=(
            "ToeFormal.Derivation."
            "PhiCKSourceBridgeTransportTheoremLinkageFamilySynthesisResultReview"
        ),
        json_filename=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "RESULT_REVIEW_20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "local_phi_triad_synthesis_review_accepts_index_without_promotion"
        ),
        stage_role="triad_synthesis_result_review",
    ),
    "roadmap_packet": StageSpec(
        key="roadmap_packet",
        schema_id="COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_20260702_v0",
        packet_id="COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_v0",
        status="ACTIVE_COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_PACKET",
        outcome_id=(
            "COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_PREPARED_CCFT_AS_"
            "CANDIDATE_MESOSCOPIC_LINKAGE_LAYER_NO_PILLAR_OR_SEAM_CLOSURE"
        ),
        strict_outcome_id=(
            "COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_PREPARED_CCFT_MASTER_"
            "ACTION_CK_ARCHITECTURE_INDEXED_NO_CCFT_VALIDATION_OR_MASTER_ACTION_"
            "PROMOTION"
        ),
        consumed_target="prepare_coherence_admissibility_bridge_roadmap_rebase_packet",
        consumed_target_kind="coherence_admissibility_bridge_roadmap_rebase_packet",
        selected_next_target="review_coherence_admissibility_bridge_roadmap_rebase_result",
        selected_next_target_kind=(
            "coherence_admissibility_bridge_roadmap_rebase_result_review"
        ),
        lean_module="ToeFormal.Derivation.CoherenceAdmissibilityBridgeRoadmapRebase",
        json_filename="COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_20260702_v0.json",
        result_kind="packet",
        packet_classification=(
            "ccft_candidate_mesoscopic_bridge_layer_roadmap_rebase_planning_only"
        ),
        stage_role="roadmap_rebase_packet",
    ),
    "roadmap_review": StageSpec(
        key="roadmap_review",
        schema_id=(
            "COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_RESULT_REVIEW_"
            "20260702_v0"
        ),
        packet_id="COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_RESULT_REVIEW_v0",
        status="ACTIVE_COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_RESULT_REVIEW",
        outcome_id=(
            "COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_RESULT_REVIEW_ACCEPTS_"
            "CCFT_AS_CANDIDATE_MESOSCOPIC_LINKAGE_LAYER_NO_PILLAR_OR_SEAM_CLOSURE"
        ),
        strict_outcome_id=(
            "COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_RESULT_REVIEW_ACCEPTS_"
            "CCFT_MASTER_ACTION_CK_ARCHITECTURE_INDEX_NO_CCFT_VALIDATION_OR_"
            "MASTER_ACTION_PROMOTION"
        ),
        consumed_target="review_coherence_admissibility_bridge_roadmap_rebase_result",
        consumed_target_kind=(
            "coherence_admissibility_bridge_roadmap_rebase_result_review"
        ),
        selected_next_target="prepare_ccft_to_toe_object_crosswalk_packet",
        selected_next_target_kind="ccft_to_toe_object_crosswalk_packet",
        lean_module=(
            "ToeFormal.Derivation.CoherenceAdmissibilityBridgeRoadmapRebaseResultReview"
        ),
        json_filename=(
            "COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_RESULT_REVIEW_"
            "20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "roadmap_rebase_review_accepts_ccft_candidate_layer_planning_index_only"
        ),
        stage_role="roadmap_rebase_result_review",
    ),
    "crosswalk_packet": StageSpec(
        key="crosswalk_packet",
        schema_id="CCFT_TO_TOE_OBJECT_CROSSWALK_PACKET_20260702_v0",
        packet_id="CCFT_TO_TOE_OBJECT_CROSSWALK_PACKET_v0",
        status="ACTIVE_CCFT_TO_TOE_OBJECT_CROSSWALK_PACKET",
        outcome_id=(
            "CCFT_TO_TOE_OBJECT_CROSSWALK_PACKET_PREPARED_MESOSCOPIC_BRIDGE_"
            "LAYER_MAPPING_NO_PILLAR_OR_SEAM_CLOSURE"
        ),
        strict_outcome_id=(
            "CCFT_TO_TOE_OBJECT_CROSSWALK_PACKET_PREPARED_OBJECT_SURFACE_"
            "MAPPING_ONLY_NO_CCFT_VALIDATION_OR_MASTER_ACTION_PROMOTION"
        ),
        consumed_target="prepare_ccft_to_toe_object_crosswalk_packet",
        consumed_target_kind="ccft_to_toe_object_crosswalk_packet",
        selected_next_target="prepare_ccft_ck_admissibility_obligation_index_packet",
        selected_next_target_kind="ccft_ck_admissibility_obligation_index_packet",
        lean_module="ToeFormal.Derivation.CCFTToTOEObjectCrosswalkPacket",
        json_filename="CCFT_TO_TOE_OBJECT_CROSSWALK_PACKET_20260702_v0.json",
        result_kind="packet",
        packet_classification=(
            "ccft_to_toe_object_crosswalk_maps_candidate_surfaces_without_closure"
        ),
        stage_role="ccft_to_toe_object_crosswalk_packet",
    ),
    "ck_index_packet": StageSpec(
        key="ck_index_packet",
        schema_id="CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_20260702_v0",
        packet_id="CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_v0",
        status="ACTIVE_CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET",
        outcome_id=(
            "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_PREPARED_SOURCE_BRIDGE_"
            "TRANSPORT_EXCHANGE_ROWS_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
        ),
        strict_outcome_id=(
            "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_PREPARED_CCFT_SPECIFIC_"
            "CK_OBLIGATIONS_ONLY_NO_CCFT_VALIDATION_OR_CK_RULE_PROMOTION"
        ),
        consumed_target="prepare_ccft_ck_admissibility_obligation_index_packet",
        consumed_target_kind="ccft_ck_admissibility_obligation_index_packet",
        selected_next_target="review_ccft_ck_admissibility_obligation_index_packet_result",
        selected_next_target_kind=(
            "ccft_ck_admissibility_obligation_index_packet_result_review"
        ),
        lean_module="ToeFormal.Derivation.CCFTCKAdmissibilityObligationIndexPacket",
        json_filename="CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_20260702_v0.json",
        result_kind="packet",
        packet_classification=(
            "ccft_specific_ck_obligation_index_source_bridge_transport_exchange_only"
        ),
        stage_role="ccft_ck_admissibility_obligation_index_packet",
    ),
    "ck_index_review": StageSpec(
        key="ck_index_review",
        schema_id=(
            "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_RESULT_REVIEW_"
            "20260702_v0"
        ),
        packet_id="CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_RESULT_REVIEW_v0",
        status="ACTIVE_CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_RESULT_REVIEW",
        outcome_id=(
            "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_RESULT_REVIEW_ACCEPTS_"
            "CCFT_SOURCE_BRIDGE_TRANSPORT_EXCHANGE_OBLIGATION_INDEX_NO_PROOF_"
            "EXECUTION_OR_MASTER_ACTION_PROMOTION"
        ),
        strict_outcome_id=(
            "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_RESULT_REVIEW_ACCEPTS_"
            "CCFT_ADMISSIBILITY_ROWS_AS_PLANNING_INDEX_NO_CCFT_VALIDATION_OR_"
            "SEAM_CLOSURE"
        ),
        consumed_target="review_ccft_ck_admissibility_obligation_index_packet_result",
        consumed_target_kind=(
            "ccft_ck_admissibility_obligation_index_packet_result_review"
        ),
        selected_next_target=CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_TARGET,
        selected_next_target_kind="ccft_full_variational_action_program_packet",
        lean_module=(
            "ToeFormal.Derivation."
            "CCFTCKAdmissibilityObligationIndexPacketResultReview"
        ),
        json_filename=(
            "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_RESULT_REVIEW_"
            "20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "ccft_ck_admissibility_obligation_index_review_accepts_planning_"
            "rows_only"
        ),
        stage_role="ccft_ck_admissibility_obligation_index_packet_result_review",
    ),
    "variational_packet": StageSpec(
        key="variational_packet",
        schema_id="CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_20260702_v0",
        packet_id="CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_v0",
        status="ACTIVE_CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET",
        outcome_id=CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_OUTCOME,
        strict_outcome_id=CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_STRICT_OUTCOME,
        consumed_target=CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_TARGET,
        consumed_target_kind="ccft_full_variational_action_program_packet",
        selected_next_target=CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_REVIEW_TARGET,
        selected_next_target_kind=(
            "ccft_full_variational_action_program_packet_result_review"
        ),
        lean_module="ToeFormal.Derivation.CCFTFullVariationalActionProgramPacket",
        json_filename="CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_20260702_v0.json",
        result_kind="packet",
        packet_classification=(
            "ccft_full_variational_action_program_pre_derivation_plan_only"
        ),
        stage_role="ccft_full_variational_action_program_packet",
    ),
    "variational_review": StageSpec(
        key="variational_review",
        schema_id=(
            "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_RESULT_REVIEW_"
            "20260702_v0"
        ),
        packet_id="CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_RESULT_REVIEW_v0",
        status="ACTIVE_CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_RESULT_REVIEW",
        outcome_id=CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_REVIEW_OUTCOME,
        strict_outcome_id=CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_REVIEW_STRICT_OUTCOME,
        consumed_target=CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_REVIEW_TARGET,
        consumed_target_kind=(
            "ccft_full_variational_action_program_packet_result_review"
        ),
        selected_next_target=CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_TARGET,
        selected_next_target_kind="ccft_empirical_discriminator_candidate_map_packet",
        lean_module=(
            "ToeFormal.Derivation."
            "CCFTFullVariationalActionProgramPacketResultReview"
        ),
        json_filename=(
            "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_RESULT_REVIEW_"
            "20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "ccft_full_variational_action_program_review_accepts_pre_derivation_"
            "plan_only"
        ),
        stage_role="ccft_full_variational_action_program_packet_result_review",
    ),
    "empirical_packet": StageSpec(
        key="empirical_packet",
        schema_id=(
            "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_20260702_v0"
        ),
        packet_id="CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_v0",
        status="ACTIVE_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET",
        outcome_id=CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_OUTCOME,
        strict_outcome_id=(
            CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_STRICT_OUTCOME
        ),
        consumed_target=CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_TARGET,
        consumed_target_kind="ccft_empirical_discriminator_candidate_map_packet",
        selected_next_target=CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_REVIEW_TARGET,
        selected_next_target_kind=(
            "ccft_empirical_discriminator_candidate_map_packet_result_review"
        ),
        lean_module=(
            "ToeFormal.Derivation.CCFTEmpiricalDiscriminatorCandidateMapPacket"
        ),
        json_filename=(
            "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_"
            "20260702_v0.json"
        ),
        result_kind="packet",
        packet_classification=(
            "ccft_empirical_discriminator_candidate_map_planning_only"
        ),
        stage_role="ccft_empirical_discriminator_candidate_map_packet",
    ),
    "empirical_review": StageSpec(
        key="empirical_review",
        schema_id=(
            "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_RESULT_REVIEW_"
            "20260702_v0"
        ),
        packet_id=(
            "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_RESULT_REVIEW_v0"
        ),
        status=(
            "ACTIVE_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_RESULT_REVIEW"
        ),
        outcome_id=CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_REVIEW_OUTCOME,
        strict_outcome_id=(
            CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_REVIEW_STRICT_OUTCOME
        ),
        consumed_target=CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_REVIEW_TARGET,
        consumed_target_kind=(
            "ccft_empirical_discriminator_candidate_map_packet_result_review"
        ),
        selected_next_target=(
            CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_TARGET
        ),
        selected_next_target_kind=(
            "ccft_empirical_discriminator_candidate_priority_selection_packet"
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "CCFTEmpiricalDiscriminatorCandidateMapPacketResultReview"
        ),
        json_filename=(
            "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_RESULT_REVIEW_"
            "20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "ccft_empirical_discriminator_candidate_map_review_accepts_"
            "planning_map_only"
        ),
        stage_role="ccft_empirical_discriminator_candidate_map_packet_result_review",
    ),
    "priority_packet": StageSpec(
        key="priority_packet",
        schema_id=(
            "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_"
            "20260702_v0"
        ),
        packet_id=(
            "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_v0"
        ),
        status=(
            "ACTIVE_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET"
        ),
        outcome_id=(
            CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_OUTCOME
        ),
        strict_outcome_id=(
            CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_STRICT_OUTCOME
        ),
        consumed_target=(
            CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_TARGET
        ),
        consumed_target_kind=(
            "ccft_empirical_discriminator_candidate_priority_selection_packet"
        ),
        selected_next_target=(
            CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_REVIEW_TARGET
        ),
        selected_next_target_kind=(
            "ccft_empirical_discriminator_candidate_priority_selection_packet_result_review"
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "CCFTEmpiricalDiscriminatorCandidatePrioritySelectionPacket"
        ),
        json_filename=(
            "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_"
            "20260702_v0.json"
        ),
        result_kind="packet",
        packet_classification=(
            "ccft_empirical_discriminator_candidate_priority_selection_packet_only"
        ),
        stage_role="ccft_empirical_discriminator_candidate_priority_selection_packet",
    ),
    "priority_review": StageSpec(
        key="priority_review",
        schema_id=(
            "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_"
            "RESULT_REVIEW_20260702_v0"
        ),
        packet_id=(
            "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_"
            "RESULT_REVIEW_v0"
        ),
        status=(
            "ACTIVE_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_"
            "PACKET_RESULT_REVIEW"
        ),
        outcome_id=(
            CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_REVIEW_OUTCOME
        ),
        strict_outcome_id=(
            CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_REVIEW_STRICT_OUTCOME
        ),
        consumed_target=(
            CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_REVIEW_TARGET
        ),
        consumed_target_kind=(
            "ccft_empirical_discriminator_candidate_priority_selection_packet_result_review"
        ),
        selected_next_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_TARGET
        ),
        selected_next_target_kind=(
            "selected_ccft_empirical_discriminator_candidate_packet"
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "CCFTEmpiricalDiscriminatorCandidatePrioritySelectionPacketResultReview"
        ),
        json_filename=(
            "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_"
            "RESULT_REVIEW_20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "ccft_empirical_discriminator_candidate_priority_selection_review_"
            "accepts_planning_priority_only"
        ),
        stage_role=(
            "ccft_empirical_discriminator_candidate_priority_selection_packet_"
            "result_review"
        ),
    ),
    "selected_candidate_packet": StageSpec(
        key="selected_candidate_packet",
        schema_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_"
            "20260702_v0"
        ),
        packet_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_v0"
        ),
        status="ACTIVE_SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET",
        outcome_id=SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_OUTCOME,
        strict_outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_STRICT_OUTCOME
        ),
        consumed_target=SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_TARGET,
        consumed_target_kind="selected_ccft_empirical_discriminator_candidate_packet",
        selected_next_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_REVIEW_TARGET
        ),
        selected_next_target_kind=(
            "selected_ccft_empirical_discriminator_candidate_packet_result_review"
        ),
        lean_module=(
            "ToeFormal.Derivation.SelectedCCFTEmpiricalDiscriminatorCandidatePacket"
        ),
        json_filename=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_"
            "20260702_v0.json"
        ),
        result_kind="packet",
        packet_classification=(
            "selected_ccft_empirical_discriminator_candidate_bounded_packet_only"
        ),
        stage_role="selected_ccft_empirical_discriminator_candidate_packet",
    ),
    "selected_candidate_review": StageSpec(
        key="selected_candidate_review",
        schema_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_RESULT_"
            "REVIEW_20260702_v0"
        ),
        packet_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_RESULT_"
            "REVIEW_v0"
        ),
        status=(
            "ACTIVE_SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_"
            "RESULT_REVIEW"
        ),
        outcome_id=SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_REVIEW_OUTCOME,
        strict_outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_REVIEW_STRICT_OUTCOME
        ),
        consumed_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_REVIEW_TARGET
        ),
        consumed_target_kind=(
            "selected_ccft_empirical_discriminator_candidate_packet_result_review"
        ),
        selected_next_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_TARGET
        ),
        selected_next_target_kind=(
            "selected_ccft_empirical_discriminator_tolerance_registry_packet"
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "SelectedCCFTEmpiricalDiscriminatorCandidatePacketResultReview"
        ),
        json_filename=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_RESULT_"
            "REVIEW_20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "selected_ccft_empirical_discriminator_candidate_review_accepts_"
            "bounded_packet_instantiation_only"
        ),
        stage_role=(
            "selected_ccft_empirical_discriminator_candidate_packet_result_review"
        ),
    ),
    "tolerance_registry_packet": StageSpec(
        key="tolerance_registry_packet",
        schema_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_"
            "20260702_v0"
        ),
        packet_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_v0"
        ),
        status=(
            "ACTIVE_SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_"
            "PACKET"
        ),
        outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_OUTCOME
        ),
        strict_outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_STRICT_OUTCOME
        ),
        consumed_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_TARGET
        ),
        consumed_target_kind=(
            "selected_ccft_empirical_discriminator_tolerance_registry_packet"
        ),
        selected_next_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_REVIEW_TARGET
        ),
        selected_next_target_kind=(
            "selected_ccft_empirical_discriminator_tolerance_registry_packet_result_review"
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "SelectedCCFTEmpiricalDiscriminatorToleranceRegistryPacket"
        ),
        json_filename=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_"
            "20260702_v0.json"
        ),
        result_kind="packet",
        packet_classification=(
            "selected_ccft_empirical_discriminator_tolerance_registry_traceability_only"
        ),
        stage_role=(
            "selected_ccft_empirical_discriminator_tolerance_registry_packet"
        ),
    ),
    "tolerance_registry_review": StageSpec(
        key="tolerance_registry_review",
        schema_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_"
            "RESULT_REVIEW_20260702_v0"
        ),
        packet_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_"
            "RESULT_REVIEW_v0"
        ),
        status=(
            "ACTIVE_SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_"
            "PACKET_RESULT_REVIEW"
        ),
        outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_REVIEW_OUTCOME
        ),
        strict_outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_REVIEW_STRICT_OUTCOME
        ),
        consumed_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_REVIEW_TARGET
        ),
        consumed_target_kind=(
            "selected_ccft_empirical_discriminator_tolerance_registry_packet_result_review"
        ),
        selected_next_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_TARGET
        ),
        selected_next_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_KIND
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "SelectedCCFTEmpiricalDiscriminatorToleranceRegistryPacketResultReview"
        ),
        json_filename=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_"
            "RESULT_REVIEW_20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "selected_ccft_empirical_discriminator_tolerance_registry_review_"
            "accepts_traceability_only"
        ),
        stage_role=(
            "selected_ccft_empirical_discriminator_tolerance_registry_packet_result_review"
        ),
    ),
    "baseline_semantics_packet": StageSpec(
        key="baseline_semantics_packet",
        schema_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_"
            "SEMANTICS_PACKET_20260702_v0"
        ),
        packet_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_"
            "SEMANTICS_PACKET_v0"
        ),
        status=(
            "ACTIVE_SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_"
            "SEMANTICS_PACKET"
        ),
        outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_OUTCOME
        ),
        strict_outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_STRICT_OUTCOME
        ),
        consumed_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_TARGET
        ),
        consumed_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_KIND
        ),
        selected_next_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_TARGET
        ),
        selected_next_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_KIND
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "SelectedCCFTEmpiricalDiscriminatorBaselineComparisonSemanticsPacket"
        ),
        json_filename=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_"
            "SEMANTICS_PACKET_20260702_v0.json"
        ),
        result_kind="packet",
        packet_classification=(
            "selected_ccft_empirical_discriminator_baseline_comparison_"
            "semantics_logic_only"
        ),
        stage_role=(
            "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet"
        ),
    ),
    "baseline_semantics_review": StageSpec(
        key="baseline_semantics_review",
        schema_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_"
            "SEMANTICS_PACKET_RESULT_REVIEW_20260702_v0"
        ),
        packet_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_"
            "SEMANTICS_PACKET_RESULT_REVIEW_v0"
        ),
        status=(
            "ACTIVE_SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_"
            "SEMANTICS_PACKET_RESULT_REVIEW"
        ),
        outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_OUTCOME
        ),
        strict_outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_STRICT_OUTCOME
        ),
        consumed_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_TARGET
        ),
        consumed_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_KIND
        ),
        selected_next_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_TARGET
        ),
        selected_next_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_KIND
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "SelectedCCFTEmpiricalDiscriminatorBaselineComparisonSemanticsPacketResultReview"
        ),
        json_filename=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_"
            "SEMANTICS_PACKET_RESULT_REVIEW_20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "selected_ccft_empirical_discriminator_baseline_comparison_"
            "semantics_review_accepts_logic_only"
        ),
        stage_role=(
            "selected_ccft_empirical_discriminator_baseline_comparison_"
            "semantics_packet_result_review"
        ),
    ),
    "observable_definition_semantics_packet": StageSpec(
        key="observable_definition_semantics_packet",
        schema_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_"
            "SEMANTICS_PACKET_20260703_v0"
        ),
        packet_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_"
            "SEMANTICS_PACKET_v0"
        ),
        status=(
            "ACTIVE_SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_"
            "DEFINITION_SEMANTICS_PACKET"
        ),
        outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_PACKET_OUTCOME
        ),
        strict_outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_PACKET_STRICT_OUTCOME
        ),
        consumed_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_TARGET
        ),
        consumed_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_KIND
        ),
        selected_next_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_TARGET
        ),
        selected_next_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_KIND
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "SelectedCCFTEmpiricalDiscriminatorObservableDefinitionSemanticsPacket"
        ),
        json_filename=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_"
            "SEMANTICS_PACKET_20260703_v0.json"
        ),
        result_kind="packet",
        packet_classification=(
            "selected_ccft_empirical_discriminator_observable_definition_"
            "semantics_meaning_only"
        ),
        stage_role=(
            "selected_ccft_empirical_discriminator_observable_definition_"
            "semantics_packet"
        ),
    ),
    "observable_definition_semantics_review": StageSpec(
        key="observable_definition_semantics_review",
        schema_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_"
            "SEMANTICS_PACKET_RESULT_REVIEW_20260703_v0"
        ),
        packet_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_"
            "SEMANTICS_PACKET_RESULT_REVIEW_v0"
        ),
        status=(
            "ACTIVE_SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_"
            "DEFINITION_SEMANTICS_PACKET_RESULT_REVIEW"
        ),
        outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_OUTCOME
        ),
        strict_outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_STRICT_OUTCOME
        ),
        consumed_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_TARGET
        ),
        consumed_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_KIND
        ),
        selected_next_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_TARGET
        ),
        selected_next_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_KIND
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "SelectedCCFTEmpiricalDiscriminatorObservableDefinitionSemanticsPacketResultReview"
        ),
        json_filename=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_"
            "SEMANTICS_PACKET_RESULT_REVIEW_20260703_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "selected_ccft_empirical_discriminator_observable_definition_"
            "semantics_review_accepts_meaning_only"
        ),
        stage_role=(
            "selected_ccft_empirical_discriminator_observable_definition_"
            "semantics_packet_result_review"
        ),
    ),
    "residual_formula_selection_packet": StageSpec(
        key="residual_formula_selection_packet",
        schema_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_"
            "PACKET_20260703_v0"
        ),
        packet_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_"
            "PACKET_v0"
        ),
        status=(
            "ACTIVE_SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_"
            "SELECTION_PACKET"
        ),
        outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_PACKET_OUTCOME
        ),
        strict_outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_PACKET_STRICT_OUTCOME
        ),
        consumed_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_TARGET
        ),
        consumed_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_KIND
        ),
        selected_next_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_TARGET
        ),
        selected_next_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_KIND
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "SelectedCCFTEmpiricalDiscriminatorResidualFormulaSelectionPacket"
        ),
        json_filename=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_"
            "PACKET_20260703_v0.json"
        ),
        result_kind="packet",
        packet_classification=(
            "selected_ccft_empirical_discriminator_residual_formula_selection_"
            "normalized_lifetime_residual_future_comparison_only"
        ),
        stage_role=(
            "selected_ccft_empirical_discriminator_residual_formula_selection_"
            "packet"
        ),
    ),
    "residual_formula_selection_review": StageSpec(
        key="residual_formula_selection_review",
        schema_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_"
            "PACKET_RESULT_REVIEW_20260703_v0"
        ),
        packet_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_"
            "PACKET_RESULT_REVIEW_v0"
        ),
        status=(
            "ACTIVE_SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_"
            "SELECTION_PACKET_RESULT_REVIEW"
        ),
        outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_OUTCOME
        ),
        strict_outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_STRICT_OUTCOME
        ),
        consumed_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_TARGET
        ),
        consumed_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_KIND
        ),
        selected_next_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_TARGET
        ),
        selected_next_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_KIND
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "SelectedCCFTEmpiricalDiscriminatorResidualFormulaSelectionPacketResultReview"
        ),
        json_filename=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_"
            "PACKET_RESULT_REVIEW_20260703_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "selected_ccft_empirical_discriminator_residual_formula_selection_"
            "review_accepts_normalized_lifetime_residual_future_comparison_only"
        ),
        stage_role=(
            "selected_ccft_empirical_discriminator_residual_formula_selection_"
            "packet_result_review"
        ),
    ),
    "measurement_feedback_baseline_pressure_packet": StageSpec(
        key="measurement_feedback_baseline_pressure_packet",
        schema_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_"
            "BASELINE_PRESSURE_PACKET_20260703_v0"
        ),
        packet_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_"
            "BASELINE_PRESSURE_PACKET_v0"
        ),
        status=(
            "ACTIVE_SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_"
            "BASELINE_PRESSURE_PACKET"
        ),
        outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_OUTCOME
        ),
        strict_outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_STRICT_OUTCOME
        ),
        consumed_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_TARGET
        ),
        consumed_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_KIND
        ),
        selected_next_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_TARGET
        ),
        selected_next_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_KIND
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "SelectedCCFTEmpiricalDiscriminatorMeasurementFeedbackBaselinePressurePacket"
        ),
        json_filename=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_"
            "BASELINE_PRESSURE_PACKET_20260703_v0.json"
        ),
        result_kind="packet",
        packet_classification=(
            "selected_ccft_empirical_discriminator_measurement_feedback_"
            "baseline_pressure_literature_note_only"
        ),
        stage_role=(
            "selected_ccft_empirical_discriminator_measurement_feedback_"
            "baseline_pressure_packet"
        ),
    ),
    "measurement_feedback_baseline_pressure_review": StageSpec(
        key="measurement_feedback_baseline_pressure_review",
        schema_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_"
            "BASELINE_PRESSURE_PACKET_RESULT_REVIEW_20260703_v0"
        ),
        packet_id=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_"
            "BASELINE_PRESSURE_PACKET_RESULT_REVIEW_v0"
        ),
        status=(
            "ACTIVE_SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_"
            "BASELINE_PRESSURE_PACKET_RESULT_REVIEW"
        ),
        outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_OUTCOME
        ),
        strict_outcome_id=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_STRICT_OUTCOME
        ),
        consumed_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_TARGET
        ),
        consumed_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_KIND
        ),
        selected_next_target=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_TARGET
        ),
        selected_next_target_kind=(
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_KIND
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "SelectedCCFTEmpiricalDiscriminatorMeasurementFeedbackBaselinePressurePacketResultReview"
        ),
        json_filename=(
            "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_"
            "BASELINE_PRESSURE_PACKET_RESULT_REVIEW_20260703_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "selected_ccft_empirical_discriminator_measurement_feedback_"
            "baseline_pressure_review_accepts_baseline_hardening_only"
        ),
        stage_role=(
            "selected_ccft_empirical_discriminator_measurement_feedback_"
            "baseline_pressure_packet_result_review"
        ),
    ),
}

ORDERED_STAGE_KEYS = [
    "selector",
    "selector_review",
    "triad_packet",
    "triad_review",
    "roadmap_packet",
    "roadmap_review",
    "crosswalk_packet",
    "ck_index_packet",
    "ck_index_review",
    "variational_packet",
    "variational_review",
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
]

NEXT_REQUIRED_OBJECT_BY_STAGE = {
    "variational_review": "CCFT empirical discriminator candidate map packet",
    "empirical_review": (
        "CCFT empirical discriminator candidate priority selection packet"
    ),
    "priority_packet": (
        "CCFT empirical discriminator candidate priority selection packet result review"
    ),
    "priority_review": "selected CCFT empirical discriminator candidate packet",
    "selected_candidate_packet": (
        "selected CCFT empirical discriminator candidate packet result review"
    ),
    "selected_candidate_review": (
        "selected CCFT empirical discriminator tolerance registry packet"
    ),
    "tolerance_registry_packet": (
        "selected CCFT empirical discriminator tolerance registry packet result review"
    ),
    "tolerance_registry_review": (
        "selected CCFT empirical discriminator baseline-comparison semantics packet"
    ),
    "baseline_semantics_packet": (
        "selected CCFT empirical discriminator baseline-comparison semantics packet result review"
    ),
    "baseline_semantics_review": (
        "selected CCFT empirical discriminator observable-definition semantics packet"
    ),
    "observable_definition_semantics_packet": (
        "selected CCFT empirical discriminator observable-definition semantics packet result review"
    ),
    "observable_definition_semantics_review": (
        "selected CCFT empirical discriminator residual-formula selection packet"
    ),
    "residual_formula_selection_packet": (
        "selected CCFT empirical discriminator residual-formula selection packet result review"
    ),
    "residual_formula_selection_review": (
        "selected CCFT empirical discriminator measurement-feedback baseline-pressure packet"
    ),
    "measurement_feedback_baseline_pressure_packet": (
        "selected CCFT empirical discriminator measurement-feedback baseline-pressure packet result review"
    ),
    "measurement_feedback_baseline_pressure_review": (
        "selected CCFT empirical discriminator baseline-component registry packet"
    ),
    "empirical_packet": (
        "CCFT empirical discriminator candidate map packet result review"
    ),
    "variational_packet": (
        "CCFT full variational/action program packet result review"
    ),
    "ck_index_review": "CCFT full variational/action program packet",
}


def release_path(spec: StageSpec) -> Path:
    return REPO_ROOT / "formal" / "docs" / "release" / spec.json_filename


def lean_path(spec: StageSpec) -> Path:
    stem = spec.lean_module.rsplit(".", 1)[-1] + ".lean"
    return REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / stem


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _result_fields(spec: StageSpec) -> dict[str, Any]:
    fields: dict[str, Any] = {
        "outcome_id": spec.outcome_id,
        "packet_result": spec.outcome_id,
        "strict_packet_result": spec.strict_outcome_id,
        "result_token": spec.outcome_id,
        "strict_result_token": spec.strict_outcome_id,
    }
    if spec.result_kind == "selection":
        fields.update(
            {
                "selection_result": spec.outcome_id,
                "selector_outcome": spec.outcome_id,
                "strict_selection_result": spec.strict_outcome_id,
                "strict_selector_outcome": spec.strict_outcome_id,
            }
        )
    if spec.result_kind == "review":
        fields.update(
            {
                "review_result": spec.outcome_id,
                "strict_review_result": spec.strict_outcome_id,
            }
        )
    return fields


def _boolean_nonclaim_flags() -> dict[str, bool]:
    return {
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_discharged": False,
        "new_theorem_discharge": False,
        "theorem_linkage_obligation_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "phi_sector_closure_claimed": False,
        "full_scalar_qft_closure_claimed": False,
        "full_scalar_QFT_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "sr_cosmo_closure_claimed": False,
        "qm_stat_closure_claimed": False,
        "pillar_closure_claim": False,
        "seam_closure_claim": False,
        "general_C_k_closure": False,
        "general_C_k_theorem_linkage_closure": False,
        "C_k_rule_promoted": False,
        "rule_promoted": False,
        "C_k_action_embedding_claimed": False,
        "C_k_action_variation_executed": False,
        "action_embedding_claimed": False,
        "action_variation_executed": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "CCFT_validated": False,
        "CCFT_fundamental_physics_claimed": False,
        "CCFT_derivation_from_master_action_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "historical_20260619_rule_family_artifacts_overwritten": False,
        "new_triad_called_rule_family_closeout": False,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
    }


def build_stage_payload(
    stage_key: str,
    *,
    captured_at_utc: str | None = None,
) -> dict[str, Any]:
    spec = STAGES[stage_key]
    captured_at_utc = (
        captured_at_utc
        if captured_at_utc is not None
        else STAGE_CAPTURED_AT_UTC.get(stage_key, DEFAULT_CAPTURED_AT_UTC)
    )
    ccft_crosswalk_prepared = stage_key in {
        "crosswalk_packet",
        "ck_index_packet",
        "ck_index_review",
        "variational_packet",
        "variational_review",
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
    }
    ccft_ck_index_prepared = stage_key in {
        "ck_index_packet",
        "ck_index_review",
        "variational_packet",
        "variational_review",
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
    }
    ccft_full_variational_program_prepared = stage_key in {
        "variational_packet",
        "variational_review",
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
    }
    ccft_empirical_discriminator_map_prepared = stage_key in {
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
    }
    payload: dict[str, Any] = {
        "artifact_id": spec.schema_id,
        "schema_id": spec.schema_id,
        "packet_id": spec.packet_id,
        "status": spec.status,
        "stage_key": spec.key,
        "stage_role": spec.stage_role,
        "prepared": True,
        "accepted": True,
        "reviewed": spec.result_kind == "review",
        "selected": spec.result_kind == "selection",
        "captured_at_utc": captured_at_utc,
        "packet_classification": spec.packet_classification,
        "consumed_target": spec.consumed_target,
        "consumed_target_kind": spec.consumed_target_kind,
        "selected_next_target": spec.selected_next_target,
        "selected_next_target_kind": spec.selected_next_target_kind,
        "local_phi_triad_label": LOCAL_PHI_THEOREM_LINKAGE_TRIAD_LABEL,
        "local_phi_theorem_linkage_triad": LOCAL_PHI_TRIAD_EQUATIONS,
        "local_phi_theorem_linkage_triad_count": len(LOCAL_PHI_TRIAD_EQUATIONS),
        "C_source_phi_zero": "C_source^phi = 0",
        "C_bridge_phi_zero": "C_bridge^phi = 0",
        "C_transport_phi_zero": "C_transport^phi = 0",
        "triad_boundary": TRIAD_BOUNDARY,
        "roadmap_rebase_boundary": ROADMAP_REBASE_BOUNDARY,
        "nonclaims": NONCLAIMS,
        "nonclaim_count": len(NONCLAIMS),
        "lean_status_wording": LEAN_STATUS_WORDING,
        "lean_status_wording_lines": LEAN_STATUS_WORDING_LINES,
        "full_toeformal_aggregate_status": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "scoped_lean_targets_status": SCOPED_LEAN_TARGETS_STATUS,
        "ccft_role": "candidate mesoscopic coherence bridge layer",
        "master_action_role": "non-promoted candidate organizing surface",
        "C_k_role": "admissibility-only bridge-checking family",
        "phi_triad_role": "local theorem-linkage family only",
        "ccft_required_follow_on_artifacts": CCFT_REQUIRED_FOLLOW_ON_ARTIFACTS,
        "next_required_object": NEXT_REQUIRED_OBJECT_BY_STAGE.get(
            stage_key,
            "CCFT-to-ToE object crosswalk",
        ),
        "roadmap_rebase_lists_follow_on_artifacts_only": (
            stage_key in {"roadmap_packet", "roadmap_review"}
        ),
        "later_ccft_artifacts_fully_populated": (
            ccft_crosswalk_prepared
            and ccft_ck_index_prepared
            and ccft_full_variational_program_prepared
            and ccft_empirical_discriminator_map_prepared
        ),
        "CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared": ccft_crosswalk_prepared,
        "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared": (
            ccft_ck_index_prepared
        ),
        "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared": (
            ccft_full_variational_program_prepared
        ),
        "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared": (
            ccft_empirical_discriminator_map_prepared
        ),
        "files": {
            "json_report": _ptr(release_path(spec)),
            "lean_packet_file": _ptr(lean_path(spec)),
        },
        "lane_level_lean_targets": [
            spec.lean_module,
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
    }
    if stage_key == "ck_index_review":
        payload.update(
            {
                "ccft_index_review_acceptance_items": (
                    CCFT_INDEX_REVIEW_ACCEPTANCE_ITEMS
                ),
                "ccft_index_review_acceptance_item_count": len(
                    CCFT_INDEX_REVIEW_ACCEPTANCE_ITEMS
                ),
                "suggested_next_packet_outcome": (
                    CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_OUTCOME
                ),
                "strict_suggested_next_packet_outcome": (
                    CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_STRICT_OUTCOME
                ),
                "next_disciplined_move_reason": (
                    "The CCFT-ToE crosswalk and CCFT C_k obligation index "
                    "have now been prepared. The next disciplined move is "
                    "not proof execution yet; it is to define the "
                    "variational/action program needed before any derived "
                    "C_k component, action embedding, or transport-zero "
                    "proof can be attempted."
                ),
            }
        )
    if stage_key in {
        "variational_packet",
        "variational_review",
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
    }:
        payload.update(
            {
                "ccft_full_variational_action_program_targets": (
                    CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_DEFINITION_TARGETS
                ),
                "ccft_full_variational_action_program_target_count": len(
                    CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_DEFINITION_TARGETS
                ),
                "ccft_full_variational_action_program_boundary": (
                    CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_BOUNDARY
                ),
                "ccft_lagrangian_candidate_targets_defined": True,
                "ccft_hamiltonian_candidate_targets_defined": True,
                "phi_sector_variational_route_targets_defined": True,
                "chi_sector_variational_route_targets_defined": True,
                "rotor_curvature_variational_route_targets_defined": True,
                "ccft_stress_energy_source_candidate_targets_defined": True,
                "ccft_C_source_derivation_targets_defined": True,
                "ccft_C_bridge_derivation_targets_defined": True,
                "ccft_C_transport_component_derivation_targets_defined": True,
                "ccft_C_exchange_phi_chi_exchange_balance_targets_defined": True,
                "required_blockers_before_action_embedding_defined": True,
                "required_blockers_before_C_k_variation_defined": True,
                "required_blockers_before_empirical_discriminator_claims_defined": True,
                "C_k_action_embedding_authorized": False,
                "C_k_variation_authorized": False,
                "empirical_discriminator_claims_authorized": False,
            }
        )
    if stage_key in {
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
    }:
        payload.update(
            {
                "ccft_empirical_discriminator_candidate_map_targets": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_TARGETS
                ),
                "ccft_empirical_discriminator_candidate_map_target_count": (
                    len(CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_TARGETS)
                ),
                "ccft_empirical_discriminator_candidate_map_boundary": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_BOUNDARY
                ),
                "candidate_measurable_systems_indexed": True,
                "candidate_observables_indexed": True,
                "candidate_control_variables_indexed": True,
                "candidate_baseline_models_indexed": True,
                "candidate_failure_modes_indexed": True,
                "candidate_falsifiers_indexed": True,
                "candidate_numerical_vs_physical_comparison_routes_indexed": True,
                "candidate_empirical_discriminator_questions_indexed": True,
                "required_blockers_before_empirical_claim_indexed": True,
                "required_blockers_before_CCFT_validation_indexed": True,
                "required_blockers_before_pillar_or_seam_relevance_indexed": True,
                "empirical_claim_authorized": False,
                "pillar_closure_authorized": False,
            }
        )
    if stage_key in {
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
    }:
        payload.update(
            {
                "ccft_empirical_discriminator_candidate_priority_selection_actions": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_ACTIONS
                ),
                "ccft_empirical_discriminator_candidate_priority_selection_action_count": (
                    len(
                        CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_ACTIONS
                    )
                ),
                "ccft_empirical_discriminator_candidate_priority_selection_criteria": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_CRITERIA
                ),
                "ccft_empirical_discriminator_candidate_priority_selection_criteria_count": (
                    len(
                        CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_CRITERIA
                    )
                ),
                "candidate_measurable_system_ranking": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_MEASURABLE_SYSTEM_RANKING
                ),
                "candidate_observable_ranking": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_OBSERVABLE_RANKING
                ),
                "candidate_falsifier_row_ranking": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_FALSIFIER_RANKING
                ),
                "candidate_baseline_model_comparison_ranking": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_BASELINE_RANKING
                ),
                "selected_top_candidate_for_future_packet_only": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTED_TOP_CANDIDATE
                ),
                "deferred_or_rejected_candidates": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_DEFERRED_CANDIDATES
                ),
                "ccft_empirical_discriminator_candidate_priority_selection_boundary": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_BOUNDARY
                ),
                "accepted_empirical_discriminator_candidate_map_consumed": True,
                "candidate_measurable_systems_ranked": True,
                "candidate_observables_ranked": True,
                "candidate_falsifier_rows_ranked": True,
                "candidate_baseline_model_comparisons_ranked": True,
                "top_candidate_selected_for_future_packet_only": True,
                "selection_criteria_recorded": True,
                "rejected_or_deferred_candidates_recorded": True,
                "empirical_test_executed": False,
                "future_packet_preparation_only": True,
            }
        )
    if stage_key == "empirical_review":
        payload.update(
            {
                "ccft_empirical_discriminator_candidate_map_review_acceptance_items": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_REVIEW_ACCEPTANCE_ITEMS
                ),
                "ccft_empirical_discriminator_candidate_map_review_acceptance_item_count": (
                    len(
                        CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_REVIEW_ACCEPTANCE_ITEMS
                    )
                ),
                "prepared_packet_result": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_OUTCOME
                ),
                "prepared_packet_strict_result": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_PACKET_STRICT_OUTCOME
                ),
                "next_disciplined_move_reason": (
                    "The empirical discriminator map is only a planning map. "
                    "The next disciplined step is to select or rank candidate "
                    "discriminator rows, not execute an empirical claim or "
                    "validation attempt."
                ),
            }
        )
    if stage_key == "priority_review":
        payload.update(
            {
                "ccft_empirical_discriminator_candidate_priority_selection_review_acceptance_items": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_REVIEW_ACCEPTANCE_ITEMS
                ),
                "ccft_empirical_discriminator_candidate_priority_selection_review_acceptance_item_count": (
                    len(
                        CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_REVIEW_ACCEPTANCE_ITEMS
                    )
                ),
                "prepared_packet_result": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_OUTCOME
                ),
                "prepared_packet_strict_result": (
                    CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_STRICT_OUTCOME
                ),
                "selected_top_discriminator_priority_accepted_for_future_packet_only": True,
                "selected_candidate_packet_preparation_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_TARGET
                ),
                "empirical_execution_authorized": False,
                "next_disciplined_move_reason": (
                    "The priority selection is only a planning review. The next "
                    "disciplined step is a narrowly bounded packet for the "
                    "selected top discriminator candidate itself, not execution "
                    "of an empirical test or validation attempt."
                ),
            }
        )
    if stage_key in {
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
    }:
        payload.update(
            {
                "selected_ccft_empirical_discriminator_candidate_packet_actions": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_ACTIONS
                ),
                "selected_ccft_empirical_discriminator_candidate_packet_action_count": (
                    len(SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_ACTIONS)
                ),
                "selected_ccft_empirical_discriminator_candidate_packet_boundary": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_BOUNDARY
                ),
                "selected_ccft_empirical_discriminator_candidate_id": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_ID
                ),
                "selected_ccft_empirical_discriminator_candidate_observable": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_OBSERVABLE
                ),
                "selected_ccft_empirical_discriminator_candidate_baseline": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_BASELINE
                ),
                "selected_ccft_empirical_discriminator_candidate_falsifier": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_FALSIFIER
                ),
                "priority_selection_result_review_consumed": True,
                "selected_candidate_instantiated_for_future_packet_only": True,
                "selected_observable_bound_as_planning_row": True,
                "selected_baseline_bound_as_planning_row": True,
                "selected_falsifier_bound_as_planning_row": True,
                "candidate_control_variable_placeholders_recorded": True,
                "candidate_numerical_vs_physical_placeholders_recorded": True,
                "blockers_before_empirical_protocol_design_recorded": True,
                "blockers_before_empirical_execution_recorded": True,
                "empirical_execution_authorized": False,
                "empirical_protocol_executed": False,
                "selected_candidate_validation_claimed": False,
            }
        )
    if stage_key == "selected_candidate_review":
        payload.update(
            {
                "selected_ccft_empirical_discriminator_candidate_review_acceptance_items": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_REVIEW_ACCEPTANCE_ITEMS
                ),
                "selected_ccft_empirical_discriminator_candidate_review_acceptance_item_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_REVIEW_ACCEPTANCE_ITEMS
                    )
                ),
                "prepared_packet_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_OUTCOME
                ),
                "prepared_packet_strict_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_STRICT_OUTCOME
                ),
                "selected_candidate_packet_accepted_as_future_packet_only": True,
                "registered_tolerances_traceability_placeholder_only": True,
                "registered_tolerances_empirically_calibrated": False,
                "registered_tolerances_execution_authorized": False,
                "registered_tolerances_empirical_claim_authorized": False,
                "empirical_protocol_design_authorized": False,
                "suggested_next_packet_outcome": (
                    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_"
                    "PACKET_PREPARED_PLACEHOLDER_TOLERANCE_TRACEABILITY_PLAN_"
                    "NO_EMPIRICAL_CALIBRATION_OR_VALIDATION"
                ),
                "strict_suggested_next_packet_outcome": (
                    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_"
                    "PACKET_PREPARED_AS_PRE_PROTOCOL_TRACEABILITY_MAP_NO_"
                    "EXECUTION_OR_MASTER_ACTION_PROMOTION"
                ),
                "next_disciplined_move_reason": (
                    "The selected-candidate packet result review accepts only "
                    "bounded candidate instantiation. Because the falsifier row "
                    "uses registered_tolerances, the next disciplined step is a "
                    "tolerance traceability registry packet before any empirical "
                    "protocol design, execution, calibration, or validation claim."
                ),
            }
        )
    if stage_key in {
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
    }:
        payload.update(
            {
                "selected_candidate_result_review_consumed": True,
                "selected_candidate_review_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_REVIEW_OUTCOME
                ),
                "selected_candidate_review_strict_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_REVIEW_STRICT_OUTCOME
                ),
                "selected_candidate_packet_accepted_as_future_packet_only": True,
                "selected_ccft_empirical_discriminator_tolerance_registry_fields": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_FIELDS
                ),
                "selected_ccft_empirical_discriminator_tolerance_registry_field_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_FIELDS
                    )
                ),
                "selected_ccft_empirical_discriminator_tolerance_registry_rows": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_ROWS
                ),
                "selected_ccft_empirical_discriminator_tolerance_registry_row_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_ROWS
                    )
                ),
                "selected_ccft_empirical_discriminator_tolerance_ids": [
                    row["tolerance_id"]
                    for row in SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_ROWS
                ],
                "selected_ccft_empirical_discriminator_tolerance_observable_binding": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_OBSERVABLE
                ),
                "selected_ccft_empirical_discriminator_tolerance_baseline_binding": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_BASELINE
                ),
                "selected_ccft_empirical_discriminator_tolerance_null_condition": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_FALSIFIER
                ),
                "selected_ccft_empirical_discriminator_tolerance_source_status": (
                    "placeholder_future_empirical_calibration_needed"
                ),
                "selected_ccft_empirical_discriminator_tolerance_execution_status": (
                    "not_executed"
                ),
                "selected_ccft_empirical_discriminator_tolerance_comparison_semantics": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_COMPARISON_SEMANTICS
                ),
                "selected_ccft_empirical_discriminator_tolerance_comparison_semantics_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_COMPARISON_SEMANTICS
                    )
                ),
                "selected_ccft_empirical_discriminator_tolerance_registry_boundary": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_BOUNDARY
                ),
                "registered_tolerances_traceability_placeholder_only": True,
                "registered_tolerances_empirically_calibrated": False,
                "registered_tolerances_statistically_validated": False,
                "registered_tolerances_execution_authorized": False,
                "registered_tolerances_empirical_claim_authorized": False,
                "registered_tolerances_sufficient_for_execution": False,
                "registered_tolerances_distinguish_ccft_from_baseline_claimed": False,
                "registered_tolerances_bound_to_measurement_campaign": False,
                "empirical_methods_section_claimed": False,
                "empirical_protocol_design_authorized": False,
                "empirical_execution_authorized": False,
                "empirical_test_executed": False,
                "future_empirical_calibration_needed": True,
                "next_disciplined_move_reason": (
                    "The tolerance registry packet records traceability and "
                    "comparison logic only. The next disciplined step is a "
                    "result review of that registry, not protocol design, "
                    "empirical execution, calibration, CCFT validation, or "
                    "baseline-separation claim."
                    if stage_key == "tolerance_registry_packet"
                    else (
                        "The tolerance registry result review accepts only "
                        "non-executed traceability rows. The next disciplined "
                        "step is baseline-comparison semantics planning, not "
                        "protocol design, empirical execution, calibration, "
                        "CCFT validation, or baseline-separation claim."
                    )
                ),
            }
        )
    if stage_key == "tolerance_registry_review":
        payload.update(
            {
                "selected_ccft_empirical_discriminator_tolerance_registry_review_acceptance_items": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_REVIEW_ACCEPTANCE_ITEMS
                ),
                "selected_ccft_empirical_discriminator_tolerance_registry_review_acceptance_item_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_REVIEW_ACCEPTANCE_ITEMS
                    )
                ),
                "prepared_packet_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_OUTCOME
                ),
                "prepared_packet_strict_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_STRICT_OUTCOME
                ),
                "tolerance_registry_packet_accepted_as_traceability_only": True,
                "tolerance_registry_rows_accepted_as_non_executed_only": True,
                "comparison_semantics_accepted_as_placeholders_only": True,
                "null_condition_retained_as_default": True,
                "future_empirical_calibration_required_before_claim": True,
                "tolerance_row_accepted_as_test_protocol": False,
                "tolerance_row_accepted_as_effect_size_threshold": False,
                "tolerance_row_accepted_as_statistical_decision_rule": False,
                "tolerance_row_accepted_as_experimental_design": False,
                "selected_next_planning_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_TARGET
                ),
                "suggested_next_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_TARGET
                ),
                "suggested_next_packet_kind": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_KIND
                ),
                "suggested_next_packet_outcome": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_TOLERANCE_REVIEW_SUGGESTED_OUTCOME
                ),
                "strict_suggested_next_packet_outcome": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_TOLERANCE_REVIEW_SUGGESTED_STRICT_OUTCOME
                ),
            }
        )
    if stage_key in {
        "baseline_semantics_packet",
        "baseline_semantics_review",
        "observable_definition_semantics_packet",
        "observable_definition_semantics_review",
        "residual_formula_selection_packet",
        "residual_formula_selection_review",
        "measurement_feedback_baseline_pressure_packet",
        "measurement_feedback_baseline_pressure_review",
    }:
        payload.update(
            {
                "tolerance_registry_result_review_consumed": True,
                "tolerance_registry_review_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_REVIEW_OUTCOME
                ),
                "tolerance_registry_review_strict_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_REVIEW_STRICT_OUTCOME
                ),
                "selected_ccft_empirical_discriminator_baseline_comparison_semantics_fields": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_FIELDS
                ),
                "selected_ccft_empirical_discriminator_baseline_comparison_semantics_field_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_FIELDS
                    )
                ),
                "selected_ccft_empirical_discriminator_baseline_comparison_semantics_rows": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_ROWS
                ),
                "selected_ccft_empirical_discriminator_baseline_comparison_semantics_row_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_ROWS
                    )
                ),
                "selected_ccft_empirical_discriminator_baseline_semantics_ids": [
                    row["baseline_semantics_id"]
                    for row in SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_ROWS
                ],
                "selected_ccft_empirical_discriminator_baseline_candidate_binding": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_ID
                ),
                "selected_ccft_empirical_discriminator_baseline_observable_binding": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_OBSERVABLE
                ),
                "selected_ccft_empirical_discriminator_baseline_binding": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_BASELINE
                ),
                "selected_ccft_empirical_discriminator_baseline_null_default": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_FALSIFIER
                ),
                "selected_ccft_empirical_discriminator_baseline_tolerance_binding": (
                    "TOL-CCFT-MESO-COH-LIFETIME-RESIDUAL-v0"
                ),
                "selected_ccft_empirical_discriminator_residual_definition_status": (
                    "placeholder_future_refinement_needed"
                ),
                "selected_ccft_empirical_discriminator_comparison_direction_status": (
                    "placeholder_direction_not_selected"
                ),
                "selected_ccft_empirical_discriminator_baseline_semantics_boundary": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_BOUNDARY
                ),
                "baseline_comparison_semantics_packet_prepared": True,
                "baseline_comparison_semantics_rows_registered": True,
                "baseline_semantics_logic_only": True,
                "baseline_complete_claimed": False,
                "baseline_experimentally_fitted": False,
                "residual_observed": False,
                "tolerance_determines_significance": False,
                "ccft_measurable_separation_predicted": False,
                "candidate_ready_for_execution": False,
                "baseline_separation_claimed": False,
                "empirical_protocol_authorized": False,
                "empirical_protocol_defined": False,
                "statistical_validation_claimed": False,
                "statistical_decision_rule_defined": False,
                "effect_size_threshold_defined": False,
                "execution_readiness_claimed": False,
                "next_disciplined_move_reason": (
                    "The baseline-comparison semantics result review accepts "
                    "only non-executed comparison logic. The next disciplined "
                    "step is observable-definition semantics for the "
                    "coherence_lifetime_residual_candidate, not empirical "
                    "protocol design, statistical validation, execution, "
                    "baseline separation, or CCFT validation."
                    if stage_key == "baseline_semantics_review"
                    else (
                        "The observable-definition semantics packet defines "
                        "only the meaning of coherence_lifetime_residual_"
                        "candidate as a future comparison object. The next "
                        "disciplined step is result review, not empirical "
                        "protocol design, statistical validation, execution, "
                        "baseline separation, or CCFT validation."
                        if stage_key == "observable_definition_semantics_packet"
                        else (
                            "The baseline-comparison semantics packet defines "
                            "only how a future packet would compare a "
                            "candidate coherence-lifetime residual against a "
                            "standard open-system decoherence baseline. The "
                            "next disciplined step is result review, not "
                            "empirical protocol design, statistical validation, "
                            "execution, baseline separation, or CCFT validation."
                        )
                    )
                ),
            }
        )
    if stage_key == "baseline_semantics_review":
        payload.update(
            {
                "selected_ccft_empirical_discriminator_baseline_comparison_semantics_review_acceptance_items": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_ACCEPTANCE_ITEMS
                ),
                "selected_ccft_empirical_discriminator_baseline_comparison_semantics_review_acceptance_item_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_ACCEPTANCE_ITEMS
                    )
                ),
                "prepared_packet_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_OUTCOME
                ),
                "prepared_packet_strict_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_STRICT_OUTCOME
                ),
                "baseline_comparison_semantics_packet_accepted_as_logic_only": True,
                "baseline_semantics_rows_accepted_as_non_executed_only": True,
                "residual_definition_status_accepted_as_placeholder_only": True,
                "comparison_direction_accepted_as_placeholder_only": True,
                "baseline_not_accepted_as_complete": True,
                "baseline_adequacy_accepted": False,
                "baseline_empirical_fit_quality_accepted": False,
                "statistical_decision_rule_validity_accepted": False,
                "observed_separation_accepted": False,
                "ccft_predicted_separation_accepted": False,
                "experimental_protocol_readiness_accepted": False,
                "selected_next_planning_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_TARGET
                ),
                "suggested_next_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_TARGET
                ),
                "suggested_next_packet_kind": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_KIND
                ),
                "suggested_next_packet_outcome": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_SUGGESTED_OUTCOME
                ),
                "strict_suggested_next_packet_outcome": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_SUGGESTED_STRICT_OUTCOME
                ),
            }
        )
    if stage_key in {
        "observable_definition_semantics_packet",
        "observable_definition_semantics_review",
        "residual_formula_selection_packet",
        "residual_formula_selection_review",
        "measurement_feedback_baseline_pressure_packet",
        "measurement_feedback_baseline_pressure_review",
    }:
        observable_next_target = (
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_TARGET
            if stage_key == "observable_definition_semantics_review"
            else (
                SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_TARGET
                if stage_key == "residual_formula_selection_packet"
                else SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_TARGET
            )
        )
        observable_next_kind = (
            SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_KIND
            if stage_key == "observable_definition_semantics_review"
            else (
                SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_KIND
                if stage_key == "residual_formula_selection_packet"
                else SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_KIND
            )
        )
        payload.update(
            {
                "baseline_comparison_semantics_result_review_consumed": True,
                "baseline_comparison_semantics_review_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_OUTCOME
                ),
                "baseline_comparison_semantics_review_strict_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_REVIEW_STRICT_OUTCOME
                ),
                "baseline_comparison_semantics_packet_accepted_as_logic_only": True,
                "baseline_semantics_rows_accepted_as_non_executed_only": True,
                "residual_definition_status_accepted_as_placeholder_only": True,
                "comparison_direction_accepted_as_placeholder_only": True,
                "baseline_not_accepted_as_complete": True,
                "baseline_adequacy_accepted": False,
                "baseline_empirical_fit_quality_accepted": False,
                "statistical_decision_rule_validity_accepted": False,
                "observed_separation_accepted": False,
                "ccft_predicted_separation_accepted": False,
                "experimental_protocol_readiness_accepted": False,
                "selected_ccft_empirical_discriminator_observable_definition_semantics_fields": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_FIELDS
                ),
                "selected_ccft_empirical_discriminator_observable_definition_semantics_field_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_FIELDS
                    )
                ),
                "selected_ccft_empirical_discriminator_observable_definition_semantics_rows": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_ROWS
                ),
                "selected_ccft_empirical_discriminator_observable_definition_semantics_row_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_ROWS
                    )
                ),
                "selected_ccft_empirical_discriminator_observable_ids": [
                    row["observable_id"]
                    for row in SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_ROWS
                ],
                "selected_ccft_empirical_discriminator_observable_id": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_OBSERVABLE
                ),
                "selected_ccft_empirical_discriminator_observable_candidate_platform_binding": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_ID
                ),
                "selected_ccft_empirical_discriminator_observable_baseline_binding": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_BASELINE
                ),
                "selected_ccft_empirical_discriminator_observable_tolerance_binding": (
                    "TOL-CCFT-MESO-COH-LIFETIME-RESIDUAL-v0"
                ),
                "selected_ccft_empirical_discriminator_observable_null_default": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_FALSIFIER
                ),
                "selected_ccft_empirical_discriminator_observable_execution_status": (
                    "not_executed"
                ),
                "selected_ccft_empirical_discriminator_observable_definition_boundary": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_BOUNDARY
                ),
                "observable_definition_semantics_packet_prepared": True,
                "observable_definition_semantics_rows_registered": True,
                "observable_semantics_meaning_only": True,
                "observable_defined_as_future_comparison_object": True,
                "comparison_direction_resolved": False,
                "observed_empirical_residual_claimed": False,
                "ccft_predicted_residual_claimed": False,
                "statistically_significant_deviation_claimed": False,
                "measurement_protocol_defined": False,
                "validated_discriminator_claimed": False,
                "coherence_lifetime_baseline_separation_claimed": False,
                "selected_next_planning_packet_target": (
                    observable_next_target
                ),
                "suggested_next_packet_target": (
                    observable_next_target
                ),
                "suggested_next_packet_kind": (
                    observable_next_kind
                ),
            }
        )
    if stage_key in {
        "residual_formula_selection_packet",
        "residual_formula_selection_review",
        "measurement_feedback_baseline_pressure_packet",
        "measurement_feedback_baseline_pressure_review",
    }:
        payload.update(
            {
                "observable_definition_semantics_result_review_consumed": True,
                "observable_definition_semantics_review_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_OUTCOME
                ),
                "observable_definition_semantics_review_strict_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_STRICT_OUTCOME
                ),
                "observable_definition_semantics_packet_accepted_as_meaning_only": True,
                "observable_definition_semantics_rows_accepted_as_non_executed_only": True,
                "coherence_lifetime_residual_candidate_accepted_as_future_comparison_object_only": True,
                "registered_tolerance_binding_retained_as_traceability_only": True,
                "selected_ccft_empirical_discriminator_residual_formula_selection_fields": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_FIELDS
                ),
                "selected_ccft_empirical_discriminator_residual_formula_selection_field_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_FIELDS
                    )
                ),
                "selected_ccft_empirical_discriminator_residual_formula_selection_rows": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_ROWS
                ),
                "selected_ccft_empirical_discriminator_residual_formula_selection_row_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_ROWS
                    )
                ),
                "selected_ccft_empirical_discriminator_residual_formula_ids": [
                    row["formula_id"]
                    for row in SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_ROWS
                ],
                "selected_primary_residual_formula_id": (
                    "normalized_lifetime_residual"
                ),
                "selected_primary_residual_formula_type": (
                    "normalized_lifetime_residual"
                ),
                "selected_primary_residual_formula": (
                    "r_tau = (tau_candidate - tau_baseline) / tau_baseline"
                ),
                "selected_primary_residual_formula_plain_meaning": (
                    "How much longer or shorter the candidate coherence "
                    "lifetime is compared with the baseline, as a fraction "
                    "of the baseline."
                ),
                "absolute_lifetime_difference_selected_primary": False,
                "lifetime_ratio_selected_primary": False,
                "normalized_lifetime_residual_selected_primary": True,
                "decay_rate_difference_selected_primary": False,
                "decay_rate_difference_retained_for_later_comparison": True,
                "log_lifetime_ratio_selected_primary": False,
                "residual_formula_selection_packet_prepared": True,
                "residual_formula_candidate_forms_compared": True,
                "residual_formula_selected": True,
                "residual_formula_selection_required_before_protocol": True,
                "residual_formula_selection_only": True,
                "formula_selected_for_future_comparison_use_only": True,
                "residual_formula_execution_status": "not_executed",
                "measurement_protocol_readiness_accepted": False,
                "measurement_protocol_defined": False,
                "statistical_validation_claimed": False,
                "statistical_decision_rule_defined": False,
                "effect_size_threshold_defined": False,
                "observed_residual_accepted": False,
                "observed_empirical_residual_claimed": False,
                "ccft_predicted_residual_accepted": False,
                "ccft_predicted_residual_claimed": False,
                "statistical_effect_size_accepted": False,
                "measured_coherence_anomaly_accepted": False,
                "baseline_separation_accepted": False,
                "baseline_separation_claimed": False,
                "empirical_confirmation_accepted": False,
                "selected_ccft_empirical_discriminator_residual_formula_selection_items": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_ITEMS
                ),
                "selected_ccft_empirical_discriminator_residual_formula_selection_item_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_ITEMS
                    )
                ),
                "selected_ccft_empirical_discriminator_residual_formula_selection_boundary": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_BOUNDARY
                ),
                "selected_next_planning_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_TARGET
                ),
                "suggested_next_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_TARGET
                ),
                "suggested_next_packet_kind": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_KIND
                ),
                "next_disciplined_move_reason": (
                    "The residual-formula packet selects only the normalized "
                    "coherence-lifetime residual formula for future comparison "
                    "use. The next disciplined step is result review, not "
                    "measurement protocol design, statistical validation, "
                    "observed residual interpretation, baseline separation, "
                    "or CCFT validation."
                ),
            }
        )
    if stage_key == "residual_formula_selection_review":
        payload.update(
            {
                "selected_ccft_empirical_discriminator_residual_formula_selection_review_acceptance_items": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_ACCEPTANCE_ITEMS
                ),
                "selected_ccft_empirical_discriminator_residual_formula_selection_review_acceptance_item_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_ACCEPTANCE_ITEMS
                    )
                ),
                "prepared_packet_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_PACKET_OUTCOME
                ),
                "prepared_packet_strict_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_PACKET_STRICT_OUTCOME
                ),
                "residual_formula_selection_packet_accepted": True,
                "normalized_lifetime_residual_formula_accepted": True,
                "formula_accepted_for_future_comparison_use_only": True,
                "tau_baseline_positive_nonzero_precondition_recorded": True,
                "tau_candidate_observed_value_accepted": False,
                "tau_candidate_ccft_derived_prediction_accepted": False,
                "r_tau_dimensionless": True,
                "r_tau_zero_means_no_lifetime_separation_if_later_measured_or_derived": True,
                "r_tau_positive_means_longer_candidate_lifetime_if_later_measured_or_derived": True,
                "r_tau_negative_means_shorter_candidate_lifetime_if_later_measured_or_derived": True,
                "r_tau_sign_semantics_count_as_current_evidence": False,
                "measurement_feedback_baseline_pressure_source": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_SOURCE
                ),
                "measurement_feedback_baseline_pressure_components": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_COMPONENTS
                ),
                "measurement_feedback_baseline_pressure_component_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_COMPONENTS
                    )
                ),
                "external_source_treated_as_baseline_pressure_only": True,
                "external_source_treated_as_ccft_validation": False,
                "external_source_treated_as_toe_truth_claim": False,
                "selected_ccft_empirical_discriminator_residual_formula_selection_review_boundary": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_BOUNDARY
                ),
                "selected_next_planning_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_TARGET
                ),
                "suggested_next_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_TARGET
                ),
                "suggested_next_packet_kind": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_KIND
                ),
                "suggested_next_packet_outcome": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_SUGGESTED_OUTCOME
                ),
                "strict_suggested_next_packet_outcome": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_SUGGESTED_STRICT_OUTCOME
                ),
                "next_disciplined_move_reason": (
                    "The residual-formula selection result review accepts "
                    "only the normalized coherence-lifetime residual formula "
                    "as future comparison logic. The next disciplined step is "
                    "a measurement-feedback baseline-pressure packet, because "
                    "known quantum measurement, feedback, Hamiltonian control, "
                    "and thermodynamic accounting can strengthen the standard "
                    "baseline before any protocol, statistics, empirical "
                    "residual, baseline separation, or CCFT validation claim."
                ),
            }
        )
    if stage_key == "measurement_feedback_baseline_pressure_packet":
        payload.update(
            {
                "residual_formula_selection_result_review_consumed": True,
                "residual_formula_selection_review_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_OUTCOME
                ),
                "residual_formula_selection_review_strict_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_REVIEW_STRICT_OUTCOME
                ),
                "residual_formula_selection_packet_accepted": True,
                "normalized_lifetime_residual_formula_accepted": True,
                "formula_accepted_for_future_comparison_use_only": True,
                "selected_primary_residual_formula_unchanged": True,
                "measurement_feedback_baseline_pressure_packet_prepared": True,
                "measurement_feedback_baseline_pressure_only": True,
                "measurement_feedback_baseline_pressure_fields": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_FIELDS
                ),
                "measurement_feedback_baseline_pressure_field_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_FIELDS
                    )
                ),
                "measurement_feedback_baseline_pressure_rows": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_ROWS
                ),
                "measurement_feedback_baseline_pressure_row_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_ROWS
                    )
                ),
                "measurement_feedback_baseline_pressure_source": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_SOURCE
                ),
                "measurement_feedback_baseline_pressure_components": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_COMPONENTS
                ),
                "measurement_feedback_baseline_pressure_component_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_COMPONENTS
                    )
                ),
                "measurement_feedback_baseline_pressure_items": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_ITEMS
                ),
                "measurement_feedback_baseline_pressure_item_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_ITEMS
                    )
                ),
                "measurement_feedback_baseline_pressure_boundary": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_BOUNDARY
                ),
                "external_literature_source_recorded": True,
                "external_literature_source_id": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_SOURCE[
                        "source_id"
                    ]
                ),
                "external_literature_arxiv_id": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_SOURCE[
                        "arxiv_id"
                    ]
                ),
                "external_literature_source_url": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_SOURCE[
                        "source_url"
                    ]
                ),
                "external_source_treated_as_baseline_pressure_only": True,
                "external_source_treated_as_toe_evidence": False,
                "external_source_treated_as_toe_truth_claim": False,
                "external_source_treated_as_ccft_evidence": False,
                "external_source_treated_as_ccft_validation": False,
                "external_source_treated_as_empirical_validation": False,
                "external_source_treated_as_master_action_support": False,
                "baseline_strengthened_by_measurement_feedback": True,
                "tau_baseline_strengthened_beyond_ordinary_decoherence": True,
                "future_tau_baseline_must_include_measurement_feedback_effects": True,
                "future_residual_claims_must_beat_measurement_feedback_baseline": True,
                "future_tau_baseline_components": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_COMPONENTS
                ),
                "future_tau_baseline_component_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_COMPONENTS
                    )
                ),
                "residual_formula_changed_by_baseline_pressure_packet": False,
                "observed_residual_accepted": False,
                "ccft_predicted_residual_accepted": False,
                "statistical_effect_size_accepted": False,
                "baseline_separation_accepted": False,
                "measurement_protocol_readiness_accepted": False,
                "empirical_confirmation_accepted": False,
                "selected_next_planning_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_TARGET
                ),
                "suggested_next_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_TARGET
                ),
                "suggested_next_packet_kind": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_KIND
                ),
                "suggested_next_packet_outcome": "PENDING_RESULT_REVIEW",
                "strict_suggested_next_packet_outcome": "PENDING_RESULT_REVIEW",
                "next_disciplined_move_reason": (
                    "The measurement-feedback baseline-pressure packet records "
                    "arXiv:2503.13615 as literature baseline pressure only. "
                    "The next disciplined step is result review of this "
                    "reference-baseline note, not measurement protocol design, "
                    "statistical validation, observed residual interpretation, "
                    "baseline separation, CCFT validation, or master-action "
                    "promotion."
                ),
            }
        )
    if stage_key == "measurement_feedback_baseline_pressure_review":
        payload.update(
            {
                "measurement_feedback_baseline_pressure_packet_result_review_consumed": True,
                "prepared_packet_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_OUTCOME
                ),
                "prepared_packet_strict_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_PACKET_STRICT_OUTCOME
                ),
                "measurement_feedback_baseline_pressure_packet_accepted": True,
                "measurement_feedback_baseline_pressure_packet_accepted_as_baseline_hardening_only": True,
                "arxiv_2503_13615_accepted_as_literature_baseline_pressure_only": True,
                "source_accepted_as_baseline_hardening_note_only": True,
                "standard_measurement_feedback_quantum_control_accepted_as_future_baseline_burden": True,
                "future_tau_baseline_burden_strengthened": True,
                "future_tau_baseline_must_include_measurement_feedback_effects": True,
                "future_residual_claims_must_beat_measurement_feedback_baseline": True,
                "future_baseline_component_registry_selected": True,
                "selected_primary_residual_formula_unchanged": True,
                "residual_formula_changed_by_baseline_pressure_review": False,
                "measurement_feedback_baseline_pressure_review_acceptance_items": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_ACCEPTANCE_ITEMS
                ),
                "measurement_feedback_baseline_pressure_review_acceptance_item_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_ACCEPTANCE_ITEMS
                    )
                ),
                "measurement_feedback_baseline_pressure_review_boundary": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_REVIEW_BOUNDARY
                ),
                "measurement_feedback_baseline_pressure_source": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_SOURCE
                ),
                "measurement_feedback_baseline_pressure_components": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_COMPONENTS
                ),
                "measurement_feedback_baseline_pressure_component_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_COMPONENTS
                    )
                ),
                "future_tau_baseline_components": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_COMPONENTS
                ),
                "future_tau_baseline_component_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_MEASUREMENT_FEEDBACK_BASELINE_PRESSURE_COMPONENTS
                    )
                ),
                "external_source_treated_as_baseline_pressure_only": True,
                "external_source_treated_as_toe_evidence": False,
                "external_source_treated_as_toe_truth_claim": False,
                "external_source_treated_as_ccft_evidence": False,
                "external_source_treated_as_ccft_validation": False,
                "external_source_treated_as_empirical_validation": False,
                "external_source_treated_as_observed_residual_evidence": False,
                "external_source_treated_as_baseline_separation": False,
                "external_source_treated_as_protocol_readiness": False,
                "external_source_treated_as_statistical_validation": False,
                "external_source_treated_as_master_action_support": False,
                "observed_residual_accepted": False,
                "ccft_predicted_residual_accepted": False,
                "statistical_effect_size_accepted": False,
                "baseline_separation_accepted": False,
                "measurement_protocol_readiness_accepted": False,
                "empirical_confirmation_accepted": False,
                "selected_next_planning_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_TARGET
                ),
                "suggested_next_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_TARGET
                ),
                "suggested_next_packet_kind": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_KIND
                ),
                "suggested_next_packet_outcome": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_SUGGESTED_OUTCOME
                ),
                "strict_suggested_next_packet_outcome": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPONENT_REGISTRY_SUGGESTED_STRICT_OUTCOME
                ),
                "next_disciplined_move_reason": (
                    "The measurement-feedback baseline-pressure result review "
                    "accepts only baseline hardening from arXiv:2503.13615. "
                    "The next disciplined step is a baseline-component registry "
                    "packet listing what future tau_baseline must include before "
                    "any CCFT residual comparison can be meaningful, not "
                    "measurement protocol design, statistical validation, "
                    "empirical validation, CCFT validation, or master-action "
                    "promotion."
                ),
            }
        )
    if stage_key == "observable_definition_semantics_review":
        payload.update(
            {
                "selected_ccft_empirical_discriminator_observable_definition_semantics_review_acceptance_items": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_ACCEPTANCE_ITEMS
                ),
                "selected_ccft_empirical_discriminator_observable_definition_semantics_review_acceptance_item_count": (
                    len(
                        SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_REVIEW_ACCEPTANCE_ITEMS
                    )
                ),
                "prepared_packet_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_PACKET_OUTCOME
                ),
                "prepared_packet_strict_result": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_OBSERVABLE_DEFINITION_SEMANTICS_PACKET_STRICT_OUTCOME
                ),
                "observable_definition_semantics_packet_accepted_as_meaning_only": True,
                "observable_definition_semantics_rows_accepted_as_non_executed_only": True,
                "coherence_lifetime_residual_candidate_accepted_as_future_comparison_object_only": True,
                "registered_tolerance_binding_retained_as_traceability_only": True,
                "residual_formula_selected": False,
                "residual_formula_selection_required_before_protocol": True,
                "observed_residual_accepted": False,
                "ccft_predicted_residual_accepted": False,
                "statistical_effect_size_accepted": False,
                "measured_coherence_anomaly_accepted": False,
                "baseline_separation_accepted": False,
                "measurement_protocol_readiness_accepted": False,
                "empirical_confirmation_accepted": False,
                "selected_next_planning_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_TARGET
                ),
                "suggested_next_packet_target": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_TARGET
                ),
                "suggested_next_packet_kind": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_KIND
                ),
                "suggested_next_packet_outcome": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_SUGGESTED_OUTCOME
                ),
                "strict_suggested_next_packet_outcome": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_RESIDUAL_FORMULA_SELECTION_SUGGESTED_STRICT_OUTCOME
                ),
                "next_disciplined_move_reason": (
                    "The observable-definition semantics result review accepts "
                    "only the meaning of coherence_lifetime_residual_candidate "
                    "as a future comparison object. The next disciplined step "
                    "is residual-formula selection, not measurement protocol "
                    "design, statistical validation, observed residual "
                    "interpretation, baseline separation, or CCFT validation."
                ),
            }
        )
    if stage_key == "variational_review":
        payload.update(
            {
                "ccft_full_variational_action_program_review_acceptance_items": (
                    CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_REVIEW_ACCEPTANCE_ITEMS
                ),
                "ccft_full_variational_action_program_review_acceptance_item_count": (
                    len(CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_REVIEW_ACCEPTANCE_ITEMS)
                ),
                "prepared_packet_result": (
                    CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_OUTCOME
                ),
                "prepared_packet_strict_result": (
                    CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_STRICT_OUTCOME
                ),
            }
        )
    payload.update(_result_fields(spec))
    payload.update(_boolean_nonclaim_flags())
    return payload


def write_stage_payload(payload: dict[str, Any], out: Path) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def stage_main(stage_key: str, argv: list[str] | None = None) -> int:
    spec = STAGES[stage_key]
    parser = argparse.ArgumentParser(description=f"Write {spec.packet_id}.")
    parser.add_argument("--out", type=Path, default=release_path(spec))
    parser.add_argument("--captured-at-utc", default=None)
    args = parser.parse_args(argv)
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_stage_payload(stage_key, captured_at_utc=args.captured_at_utc)
    path = write_stage_payload(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "outcome_id": payload["outcome_id"],
                "selected_next_target": payload["selected_next_target"],
                "phi_sector_closure_claimed": payload[
                    "phi_sector_closure_claimed"
                ],
                "CCFT_validated": payload["CCFT_validated"],
                "master_action_promoted": payload["master_action_promoted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0
