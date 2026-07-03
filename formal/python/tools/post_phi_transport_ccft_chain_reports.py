from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-07-02T00:00:00Z"

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
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_KIND = (
    "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_"
    "PACKET_PREPARED_NON_EXECUTED_BASELINE_COMPARISON_LOGIC_NO_EMPIRICAL_"
    "VALIDATION_OR_CCFT_VALIDATION"
)
SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_STRICT_OUTCOME = (
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_"
    "PACKET_PREPARED_AS_PLANNING_SEMANTICS_ONLY_NO_PROTOCOL_EXECUTION_OR_"
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
]


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
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    spec = STAGES[stage_key]
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
        "next_required_object": (
            "CCFT empirical discriminator candidate map packet"
            if stage_key == "variational_review"
            else (
                "CCFT empirical discriminator candidate priority selection packet"
                if stage_key == "empirical_review"
                else (
                    "selected CCFT empirical discriminator baseline-comparison semantics packet"
                    if stage_key == "tolerance_registry_review"
                    else (
                        "selected CCFT empirical discriminator tolerance registry packet result review"
                        if stage_key == "tolerance_registry_packet"
                        else (
                            "selected CCFT empirical discriminator tolerance registry packet"
                            if stage_key == "selected_candidate_review"
                            else (
                                "selected CCFT empirical discriminator candidate packet result review"
                                if stage_key == "selected_candidate_packet"
                                else (
                                    "selected CCFT empirical discriminator candidate packet"
                                    if stage_key == "priority_review"
                                    else (
                                        "CCFT empirical discriminator candidate priority selection packet result review"
                                        if stage_key == "priority_packet"
                                        else (
                                            "CCFT empirical discriminator candidate map packet result review"
                                            if stage_key == "empirical_packet"
                                            else (
                                                "CCFT full variational/action program packet result review"
                                                if stage_key == "variational_packet"
                                                else (
                                                    "CCFT full variational/action program packet"
                                                    if stage_key == "ck_index_review"
                                                    else "CCFT-to-ToE object crosswalk"
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
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
    if stage_key in {"tolerance_registry_packet", "tolerance_registry_review"}:
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
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_OUTCOME
                ),
                "strict_suggested_next_packet_outcome": (
                    SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_STRICT_OUTCOME
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
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
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
