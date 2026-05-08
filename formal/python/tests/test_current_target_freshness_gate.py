from __future__ import annotations

import re
from pathlib import Path
from typing import Any

from formal.python.tests.strict_physics_state_helpers import (
    GOVERNANCE_MANIFEST_PATH,
    README_PATH,
    REGISTRY_PATH,
    REPO_ROOT,
    active_workstream,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_forbidden_promotions_closed,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
    loop_registry,
    read_text,
    workstream,
)
CROSS_PILLAR_FRONTIER_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "CrossPillarClosureFrontier.lean"
)
POST_SWEEP_QUEUE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "PostSweepTheoremQueue.lean"
)
QM_EVOLUTION_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMEvolutionPostBudgetCrossPillarReview.lean"
)
EM_QFT_PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "EMQFTPhysicsBlockerProtocolRow.lean"
)
EM_QFT_SHARED_DYNAMICS_BRIDGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "EM_QFT_SharedDynamicsResidualUnificationBridge.lean"
)
EM_QFT_INTERFACE_ALIGNMENT_BRIDGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "EM_QFT_InterfaceAlignmentSemanticBridge.lean"
)
EM_QFT_POST_BUDGET_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "EMQFTPostBudgetCrossPillarReview.lean"
)
MASTER_ACTION_CITATION_USAGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionRetainedAssumptionCitationUsage.lean"
)
MASTER_ACTION_CITATION_AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionCitationLanguageAudit.lean"
)
MASTER_ACTION_DEPENDENCY_GRAPH_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionDependencyGraphReview.lean"
)
MASTER_ACTION_RETAINED_BLOCKER_PRIORITIZATION_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionRetainedBlockerPrioritizationReview.lean"
)
QM_STAT_TRANSPORT_SEMANTICS_PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATTransportSemanticsRetainedBlockerProtocolRow.lean"
)
QM_STAT_TRANSPORT_SEMANTICS_READINESS_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATTransportSemanticsProtocolRowReadinessReview.lean"
)
QM_STAT_SOURCE_PROBABILITY_EXTRACTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QM_STAT_SourceProbabilityExtractionSemantics.lean"
)
QM_STAT_SOURCE_PROBABILITY_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATSourceProbabilityExtractionResultReview.lean"
)
MASTER_ACTION_POST_QMSTAT_PRIORITIZATION_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionPostQMSTATRetainedBlockerPrioritizationReview.lean"
)
QFT_GR_SOURCE_MAP_SEMANTICS_PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSourceMapSemanticsRetainedBlockerProtocolRow.lean"
)
QFT_GR_SOURCE_MAP_SEMANTICS_READINESS_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSourceMapSemanticsProtocolRowReadinessReview.lean"
)
QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_SEMANTICS_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StressEnergyOperatorDomainSemantics.lean"
)
QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRStressEnergyOperatorDomainResultReview.lean"
)
FULL_PILLAR_TARGET_MAP_REBASE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapRebase.lean"
)
FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapRebaseResultReview.lean"
)
POST_REBASE_NEXT_BOUNDED_ATTACK_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostRebaseNextBoundedAttackSelection.lean"
)
QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StateExpectationFunctionalSemantics.lean"
)
QFT_GR_STATE_EXPECTATION_FUNCTIONAL_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StateExpectationFunctionalSemanticsResultReview.lean"
)
QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_RenormalizedExpectationValueSemantics.lean"
)
QFT_GR_RENORMALIZED_EXPECTATION_VALUE_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_RenormalizedExpectationValueSemanticsResultReview.lean"
)
QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_ClassicalSourceAdmissibilitySemantics.lean"
)
QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_ClassicalSourceAdmissibilitySemanticsResultReview.lean"
)
QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_SEMANTICS_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_CovariantConservationObligationSemantics.lean"
)
QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_CovariantConservationObligationSemanticsResultReview.lean"
)
QFT_GR_BIANCHI_COMPATIBILITY_OBLIGATION_SEMANTICS_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_BianchiCompatibilityObligationSemantics.lean"
)
QFT_GR_BIANCHI_COMPATIBILITY_OBLIGATION_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_BianchiCompatibilityObligationSemanticsResultReview.lean"
)
QFT_GR_EINSTEIN_COUPLING_OBLIGATION_SEMANTICS_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_EinsteinCouplingObligationSemantics.lean"
)
QFT_GR_EINSTEIN_COUPLING_OBLIGATION_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_EinsteinCouplingObligationSemanticsResultReview.lean"
)
QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_SEMANTICS_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_WeakCurvatureSourceIdentificationObligationSemantics.lean"
)
QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_WeakCurvatureSourceIdentificationObligationSemanticsResultReview.lean"
)
QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_PoissonRecoveryObligationSemantics.lean"
)
QFT_GR_POISSON_RECOVERY_OBLIGATION_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_PoissonRecoveryObligationSemanticsResultReview.lean"
)
QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_SourceMapEligibilityLadderSummary.lean"
)
QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_SourceMapEligibilityLadderSummaryResultReview.lean"
)
POST_QFT_GR_LADDER_BOUNDED_ATTACK_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "PostQFTGRLadderBoundedAttackSelection.lean"
)
FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelection.lean"
)
PROOF_DEBT_LEDGER_DISCHARGE_LANE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ProofDebtLedgerDischargeLane.lean"
)
FNREP_NONALIAS_DEFAULT_DISCHARGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01Discharge.lean"
)
FNREP_NONALIAS_DEFAULT_DISCHARGE_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01DischargeResultReview.lean"
)
MASTER_ACTION_DEPENDENCY_GAP_PACKET_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionDependencyGapPacketResultReview.lean"
)
POST_READ_ONLY_VALIDATION_HYGIENE_BOUNDED_ATTACK_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostReadOnlyValidationHygieneBoundedAttackSelection.lean"
)
FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_READ_ONLY_HYGIENE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterReadOnlyHygiene.lean"
)

CITATION_USAGE_TARGET = "cite_only_bounded_retained_assumptions"
AUDIT_TARGET = "audit_master_action_citation_language_against_retained_boundaries"
REVIEW_TARGET = "review_master_action_dependency_graph_after_citation_language_audit"
PRIORITIZATION_TARGET = "prioritize_retained_blockers_after_master_action_dependency_graph_review"
PROTOCOL_PREPARATION_TARGET = "prepare_qm_stat_transport_semantics_retained_blocker_protocol_row"
READINESS_REVIEW_TARGET = "review_qm_stat_transport_semantics_protocol_row_readiness"
SOURCE_PROBABILITY_TARGET = "derive_or_refute_qm_stat_source_probability_extraction_semantics"
SOURCE_PROBABILITY_RESULT_REVIEW_TARGET = (
    "review_qm_stat_source_probability_extraction_semantics_result"
)
POST_QMSTAT_PRIORITIZATION_TARGET = (
    "prioritize_retained_blockers_after_qm_stat_source_probability_result_review"
)
QFT_GR_PROTOCOL_ROW_PREPARATION_TARGET = (
    "prepare_qft_gr_source_map_semantics_retained_blocker_protocol_row"
)
QFT_GR_PROTOCOL_ROW_READINESS_REVIEW_TARGET = (
    "review_qft_gr_source_map_semantics_protocol_row_readiness"
)
QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_TARGET = (
    "derive_or_refute_qft_gr_stress_energy_operator_domain_semantics"
)
QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_RESULT_REVIEW_TARGET = (
    "review_qft_gr_stress_energy_operator_domain_semantics_result"
)
FULL_PILLAR_TARGET_MAP_REBASE_TARGET = "prepare_full_pillar_target_map_rebase"
FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_TARGET = (
    "review_full_pillar_target_map_rebase_result"
)
POST_REBASE_NEXT_BOUNDED_ATTACK_SELECTION_TARGET = (
    "select_next_post_rebase_bounded_attack"
)
SELECTED_POST_REBASE_BOUNDED_ATTACK_TARGET = (
    "prepare_qft_gr_state_expectation_functional_semantics_bounded_attack"
)
QFT_GR_STATE_EXPECTATION_FUNCTIONAL_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_expectation_functional_semantics_result"
)
QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_TARGET = (
    "prepare_qft_gr_renormalized_expectation_value_semantics_bounded_attack"
)
QFT_GR_RENORMALIZED_EXPECTATION_VALUE_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalized_expectation_value_semantics_result"
)
QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_TARGET = (
    "prepare_qft_gr_classical_source_admissibility_semantics_bounded_attack"
)
QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_RESULT_REVIEW_TARGET = (
    "review_qft_gr_classical_source_admissibility_semantics_result"
)
QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_SEMANTICS_TARGET = (
    "prepare_qft_gr_covariant_conservation_obligation_semantics_bounded_attack"
)
QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_RESULT_REVIEW_TARGET = (
    "review_qft_gr_covariant_conservation_obligation_semantics_result"
)
QFT_GR_BIANCHI_COMPATIBILITY_OBLIGATION_SEMANTICS_TARGET = (
    "prepare_qft_gr_bianchi_compatibility_obligation_semantics_bounded_attack"
)
QFT_GR_BIANCHI_COMPATIBILITY_OBLIGATION_RESULT_REVIEW_TARGET = (
    "review_qft_gr_bianchi_compatibility_obligation_semantics_result"
)
QFT_GR_EINSTEIN_COUPLING_OBLIGATION_SEMANTICS_TARGET = (
    "prepare_qft_gr_einstein_coupling_obligation_semantics_bounded_attack"
)
QFT_GR_EINSTEIN_COUPLING_OBLIGATION_RESULT_REVIEW_TARGET = (
    "review_qft_gr_einstein_coupling_obligation_semantics_result"
)
QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_SEMANTICS_TARGET = (
    "prepare_qft_gr_weak_curvature_source_identification_obligation_semantics_bounded_attack"
)
QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_RESULT_REVIEW_TARGET = (
    "review_qft_gr_weak_curvature_source_identification_obligation_semantics_result"
)
QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_TARGET = (
    "prepare_qft_gr_poisson_recovery_obligation_semantics_bounded_attack"
)
QFT_GR_POISSON_RECOVERY_OBLIGATION_RESULT_REVIEW_TARGET = (
    "review_qft_gr_poisson_recovery_obligation_semantics_result"
)
QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_TARGET = (
    "prepare_qft_gr_source_map_eligibility_ladder_summary"
)
QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_RESULT_REVIEW_TARGET = (
    "review_qft_gr_source_map_eligibility_ladder_summary"
)
POST_QFT_GR_LADDER_BOUNDED_ATTACK_SELECTION_TARGET = (
    "select_next_post_qft_gr_ladder_bounded_attack"
)
FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_TARGET = (
    "return_to_full_pillar_target_map_next_lane_selection"
)
PROOF_DEBT_LEDGER_DISCHARGE_TARGET = "prepare_proof_debt_ledger_discharge_lane"
SELECTED_PROOF_DEBT_DISCHARGE_ITEM_TARGET = (
    "execute_selected_proof_debt_discharge_item"
)
FNREP_NONALIAS_DEFAULT_DISCHARGE_RESULT_REVIEW_TARGET = (
    "review_fnrep_nonalias_default_nonalias_discharge_result"
)
POST_PROOF_DEBT_DISCHARGE_BOUNDED_ATTACK_SELECTION_TARGET = (
    "select_next_post_proof_debt_discharge_bounded_attack"
)
MASTER_ACTION_DEPENDENCY_GAP_PACKET_RESULT_REVIEW_TARGET = (
    "review_master_action_dependency_gap_packet_result"
)
POST_MASTER_ACTION_GAP_PACKET_BOUNDED_ATTACK_SELECTION_TARGET = (
    "select_next_post_master_action_gap_packet_bounded_attack"
)
READ_ONLY_VALIDATION_HYGIENE_TARGET = "prepare_read_only_validation_hygiene_packet"
READ_ONLY_VALIDATION_HYGIENE_RESULT_REVIEW_TARGET = (
    "review_read_only_validation_hygiene_result"
)
POST_READ_ONLY_VALIDATION_HYGIENE_RESULT_TOKEN = (
    "POST_READ_ONLY_VALIDATION_HYGIENE_NEXT_ATTACK_SELECTED"
)
FULL_PILLAR_AFTER_HYGIENE_RESULT_TOKEN = (
    "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_READ_ONLY_HYGIENE"
)
ARTIFACT_RETENTION_ENFORCEMENT_RESULT_TOKEN = (
    "ARTIFACT_RETENTION_ENFORCEMENT_PLAN_PREPARED"
)
ARTIFACT_RETENTION_ENFORCEMENT_REVIEW_RESULT_TOKEN = (
    "ARTIFACT_RETENTION_ENFORCEMENT_PLAN_RESULT_REVIEW_CONSUMED"
)
POST_ARTIFACT_RETENTION_ENFORCEMENT_RESULT_TOKEN = (
    "POST_ARTIFACT_RETENTION_ENFORCEMENT_NEXT_ATTACK_SELECTED"
)
STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_TOKEN = (
    "STATUS_SURFACE_CANONICALIZATION_PLAN_PREPARED"
)
STATUS_SURFACE_CANONICALIZATION_RESULT_REVIEW_RESULT_TOKEN = (
    "STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_REVIEW_CONSUMED"
)
POST_STATUS_SURFACE_CANONICALIZATION_SELECTOR_RESULT_TOKEN = (
    "POST_STATUS_SURFACE_CANONICALIZATION_NEXT_ATTACK_SELECTED"
)
STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_RESULT_TOKEN = (
    "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_PREPARED"
)
STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_RESULT_REVIEW_RESULT_TOKEN = (
    "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_RESULT_REVIEW_CONSUMED"
)
POST_STATUS_SURFACE_ENFORCEMENT_SELECTOR_RESULT_TOKEN = (
    "POST_STATUS_SURFACE_ENFORCEMENT_NEXT_ATTACK_SELECTED"
)
ARTIFACT_RETENTION_ENFORCEMENT_TARGET = "prepare_artifact_retention_enforcement_plan"
ARTIFACT_RETENTION_ENFORCEMENT_RESULT_REVIEW_TARGET = (
    "review_artifact_retention_enforcement_plan_result"
)
POST_ARTIFACT_RETENTION_SELECTOR_TARGET = (
    "select_next_post_artifact_retention_enforcement_bounded_attack"
)
STATUS_SURFACE_CANONICALIZATION_PLAN_TARGET = (
    "prepare_status_surface_canonicalization_plan"
)
STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_REVIEW_TARGET = (
    "review_status_surface_canonicalization_plan_result"
)
POST_STATUS_SURFACE_CANONICALIZATION_SELECTOR_TARGET = (
    "select_next_post_status_surface_canonicalization_bounded_attack"
)
STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_TARGET = (
    "prepare_status_surface_canonicalization_enforcement_packet"
)
STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_RESULT_REVIEW_TARGET = (
    "review_status_surface_canonicalization_enforcement_packet_result"
)
POST_STATUS_SURFACE_ENFORCEMENT_SELECTOR_TARGET = (
    "select_next_post_status_surface_enforcement_bounded_attack"
)
LIVE_TARGET = FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_TARGET
PREVIOUS_TARGET = POST_STATUS_SURFACE_ENFORCEMENT_SELECTOR_TARGET
EM_QFT_POST_BUDGET_TARGET = "em_qft_post_budget_cross_pillar_review"
INTERFACE_TARGET = "derive_or_refute_em_qft_interface_alignment_semantic_bridge"
SHARED_DYNAMICS_TARGET = "derive_or_refute_em_qft_shared_dynamics_residual_unification_bridge"
EXTRACTION_TARGET = "extract_em_qft_physics_blocker_into_protocol_row"
QM_REVIEW_TARGET = "qm_evolution_post_budget_cross_pillar_review"
STALE_SCALAR_ACTION = "derive_or_refute_evolution_to_transport_semantic_bridge"
SCALAR_PAUSED_ACTION = "paused_no_scalar_reopen_until_dependency_graph_change"
HISTORICAL_QUEUE_TOKEN = "HISTORICAL_NONLIVE_FIRST_WAVE_QUEUE_v0"
CURRENT_TARGET_TOKEN = f"CURRENT_LIVE_NEXT_TARGET_v0: {LIVE_TARGET}"
EM_QFT_PRIMARY_BLOCKER = "shared_dynamics_and_residual_unification"
EM_QFT_SECONDARY_BLOCKER = "interface_alignment_semantic_bridge"
EM_QFT_FRESH_DELTA_ID = (
    "EM_QFT_INTERFACE_ALIGNMENT_SEMANTIC_BRIDGE_COUNTEREXAMPLE_FRESH_DELTA_v0"
)

PAUSED_LANES = {
    "scalar_qft_a2a15a1",
    "sr_covariance_cosmology_regime_transport",
    "qm_evolution_contract",
    "em_qft_physics_blocker_extraction",
    "qm_stat_transport_residual",
    "master_action_dependency_frontier",
    "qft_gr_source_map",
    "full_pillar_target_map_rebase",
    "full_pillar_target_map_rebase_result_review",
    "post_rebase_next_bounded_attack_selection",
    "qft_gr_state_expectation_functional_semantics_result_review",
    "qft_gr_renormalized_expectation_value_semantics_preparation",
    "qft_gr_renormalized_expectation_value_semantics_result_review",
    "qft_gr_classical_source_admissibility_semantics_preparation",
    "qft_gr_classical_source_admissibility_semantics_result_review",
    "qft_gr_covariant_conservation_obligation_semantics_preparation",
    "qft_gr_covariant_conservation_obligation_semantics_result_review",
    "qft_gr_bianchi_compatibility_obligation_semantics_preparation",
    "qft_gr_bianchi_compatibility_obligation_semantics_result_review",
    "qft_gr_einstein_coupling_obligation_semantics_preparation",
    "qft_gr_einstein_coupling_obligation_semantics_result_review",
    "qft_gr_weak_curvature_source_identification_obligation_semantics_preparation",
    "qft_gr_weak_curvature_source_identification_obligation_semantics_result_review",
    "qft_gr_poisson_recovery_obligation_semantics_preparation",
    "qft_gr_poisson_recovery_obligation_semantics_result_review",
    "qft_gr_source_map_eligibility_ladder_summary_preparation",
    "qft_gr_source_map_eligibility_ladder_summary_result_review",
    "post_qft_gr_ladder_bounded_attack_selection",
    "full_pillar_target_map_next_lane_selection",
    "full_pillar_target_map_next_lane_selection_after_gap_packet_review",
    "read_only_validation_hygiene",
    "post_read_only_validation_hygiene_bounded_attack_selection",
    "full_pillar_target_map_next_lane_selection_after_read_only_hygiene",
    "artifact_retention_enforcement_plan",
    "artifact_retention_enforcement_plan_result_review",
    "post_artifact_retention_enforcement_bounded_attack_selection",
    "status_surface_canonicalization_plan",
    "status_surface_canonicalization_plan_result_review",
    "post_status_surface_canonicalization_bounded_attack_selection",
    "status_surface_canonicalization_enforcement_packet",
    "status_surface_canonicalization_enforcement_packet_result_review",
}
FORBIDDEN_ASSERTIONS = {
    "phase2_authorized",
    "seam_closure_claimed",
    "master_action_promoted",
    "empirical_claimed",
    "governance_manifest_enrollment_authorized",
}


def _read(path: Path) -> str:
    return read_text(path)


def _registry() -> dict[str, Any]:
    return loop_registry()


def _control(payload: dict[str, Any], control_id: str) -> dict[str, Any]:
    for control in payload["controls"]:
        if control["control_id"] == control_id:
            return control
    raise AssertionError(f"Missing control: {control_id}")


def _workstream(payload: dict[str, Any], workstream_id: str) -> dict[str, Any]:
    return workstream(workstream_id, payload)


def _iter_key_values(value: Any, path: tuple[str, ...] = ()) -> list[tuple[tuple[str, ...], Any]]:
    if isinstance(value, dict):
        pairs: list[tuple[tuple[str, ...], Any]] = []
        for key, child in value.items():
            pairs.extend(_iter_key_values(child, path + (str(key),)))
        return pairs
    if isinstance(value, list):
        pairs = []
        for index, child in enumerate(value):
            pairs.extend(_iter_key_values(child, path + (str(index),)))
        return pairs
    return [(path, value)]


def test_single_live_target_is_machine_pinned_after_status_surface_enforcement_review() -> None:
    assert_current_target_consistent()
    payload = _registry()
    state = payload["current_target_state"]

    assert state["schema_id"] == "CURRENT_TARGET_STATE_v0"
    assert state["previous_live_next_target"] == PREVIOUS_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "PostStatusSurfaceEnforcementBoundedAttackSelection.lean"
    )
    assert state["post_sweep_queue_authority_status"] == HISTORICAL_QUEUE_TOKEN
    paused_ids = {
        item["workstream_id"] for item in payload["workstreams"] if item["status"] == "paused"
    }
    assert set(state["paused_lanes"]) == paused_ids
    assert (
        state["active_lane"]
        == "post_status_surface_enforcement_bounded_attack_selection"
    )

    current_active_workstream = active_workstream(payload)
    assert (
        current_active_workstream["workstream_id"]
        == "post_status_surface_enforcement_bounded_attack_selection"
    )
    assert current_active_workstream["authorized_next_strict_target"] == LIVE_TARGET
    assert current_active_workstream["consumed_target"] == PREVIOUS_TARGET
    assert (
        current_active_workstream["latest_surface"]
        == "post_status_surface_enforcement_bounded_attack_selection_v0"
    )
    assert (
        current_active_workstream["consumed_result_token"]
        == STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_RESULT_REVIEW_RESULT_TOKEN
    )
    assert (
        current_active_workstream["result_token"]
        == POST_STATUS_SURFACE_ENFORCEMENT_SELECTOR_RESULT_TOKEN
    )
    assert current_active_workstream["selected_next_target"] == LIVE_TARGET
    assert current_active_workstream["selected_next_target_kind"] == (
        "full_pillar_target_map_next_lane_selection"
    )
    assert current_active_workstream["authorized_effect"] == (
        "SELECT_EXACTLY_ONE_NEXT_BOUNDED_TARGET"
    )
    assert current_active_workstream["selector_executes_selected_target"] == "no"
    assert current_active_workstream["full_pillar_target_map_return_selected"] == "yes"
    assert current_active_workstream["active_live_target_mirror_parity_preserved"] == "yes"
    assert current_active_workstream["loop_registry_canonical_live_target_source"] == "yes"
    assert current_active_workstream["active_public_mirror_field_count"] == 2
    assert set(current_active_workstream["active_public_mirror_fields"]) == {
        "formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md::MASTER_ACTION_CURRENT_CITATION_TARGET_v0",
        "formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md::MASTER_ACTION_CURRENT_CITATION_TARGET_v0",
    }
    assert set(current_active_workstream["historical_packet_history_tokens_allowed"]) == {
        "review_read_only_validation_hygiene_result",
        "prepare_status_surface_canonicalization_enforcement_packet",
        "review_status_surface_canonicalization_enforcement_packet_result",
        "select_next_post_status_surface_enforcement_bounded_attack",
    }
    assert (
        current_active_workstream[
            "current_authoritative_surfaces_classify_sources_and_mirrors"
        ]
        == "yes"
    )
    assert current_active_workstream["ordinary_validation_mode"] == "read_only_by_default"
    assert (
        current_active_workstream["read_only_proof"]
        == "full_pytest_from_selector_implementation_followed_by_clean_diff_checks"
    )
    assert current_active_workstream["full_pytest_passed"] == 6614
    assert current_active_workstream["full_pytest_skipped"] == 230
    assert (
        current_active_workstream["full_pytest_is_prior_checkpoint_not_fresh_for_this_selector"]
        == "no"
    )
    assert current_active_workstream["full_pytest_fresh_for_this_selector"] == "yes"
    assert current_active_workstream["lean_build_jobs"] == 7985
    assert current_active_workstream["governance_suite_passed"] == "yes"
    assert current_active_workstream["new_large_tracked_snapshots_frozen_by_default"] == "yes"
    assert (
        current_active_workstream[
            "tracked_generated_output_mutation_forbidden_during_validation"
        ]
        == "yes"
    )
    assert current_active_workstream["read_only_validation_preserved"] == "yes"
    assert current_active_workstream["artifact_freeze_preserved"] == "yes"
    assert current_active_workstream["proof_debt_discharge_item_selected"] == "no"
    assert current_active_workstream["artifact_retention_migration_plan_selected"] == "no"
    assert current_active_workstream["qm_stat_reentry_selected"] == "no"
    assert current_active_workstream["sr_cosmo_followup_selected"] == "no"
    assert current_active_workstream["status_surface_enforcement_followup_selected"] == "no"
    assert current_active_workstream["candidate_target_count"] == 6
    assert set(current_active_workstream["candidate_targets"]) == {
        FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_TARGET,
        "prepare_next_proof_debt_ledger_discharge_item",
        "prepare_artifact_retention_migration_plan",
        "prepare_qm_stat_theorem_gap_reentry",
        "prepare_sr_cosmo_global_obstruction_followup",
        "prepare_status_surface_enforcement_followup_packet",
    }
    assert current_active_workstream["real_axiom_count"] == 60
    assert current_active_workstream["qft_gr_source_map_closure_authorized"] == "no"
    assert current_active_workstream["seam_closure_claim"] == "no"
    assert current_active_workstream["phase2_readiness_claim"] == "no"
    assert current_active_workstream["empirical_adequacy_claim"] == "no"
    assert current_active_workstream["master_action_promotion_authorized"] == "no"

    active_targets = {state["live_next_target"], current_active_workstream["authorized_next_strict_target"]}
    assert active_targets == {LIVE_TARGET}

    hygiene_workstream = _workstream(payload, "read_only_validation_hygiene")
    assert hygiene_workstream["status"] == "paused"
    assert hygiene_workstream["result_token"] == "READ_ONLY_VALIDATION_HYGIENE_ENFORCED"
    assert (
        hygiene_workstream["selected_next_target"]
        == READ_ONLY_VALIDATION_HYGIENE_RESULT_REVIEW_TARGET
    )
    assert hygiene_workstream["plain_pytest_tracked_output_mutation_allowed"] == "no"

    post_hygiene_workstream = _workstream(
        payload, "post_read_only_validation_hygiene_bounded_attack_selection"
    )
    assert post_hygiene_workstream["status"] == "paused"
    assert (
        post_hygiene_workstream["result_token"]
        == POST_READ_ONLY_VALIDATION_HYGIENE_RESULT_TOKEN
    )
    assert (
        post_hygiene_workstream["selected_next_target"]
        == FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_TARGET
    )

    after_hygiene_workstream = _workstream(
        payload, "full_pillar_target_map_next_lane_selection_after_read_only_hygiene"
    )
    assert after_hygiene_workstream["status"] == "paused"
    assert (
        after_hygiene_workstream["result_token"]
        == FULL_PILLAR_AFTER_HYGIENE_RESULT_TOKEN
    )
    assert after_hygiene_workstream["selected_next_target"] == (
        ARTIFACT_RETENTION_ENFORCEMENT_TARGET
    )

    artifact_plan_workstream = _workstream(payload, "artifact_retention_enforcement_plan")
    assert artifact_plan_workstream["status"] == "paused"
    assert artifact_plan_workstream["result_token"] == ARTIFACT_RETENTION_ENFORCEMENT_RESULT_TOKEN
    assert (
        artifact_plan_workstream["selected_next_target"]
        == ARTIFACT_RETENTION_ENFORCEMENT_RESULT_REVIEW_TARGET
    )
    assert artifact_plan_workstream["plan_executes_migration_or_deletion"] == "no"

    artifact_review_workstream = _workstream(
        payload, "artifact_retention_enforcement_plan_result_review"
    )
    assert artifact_review_workstream["status"] == "paused"
    assert (
        artifact_review_workstream["result_token"]
        == ARTIFACT_RETENTION_ENFORCEMENT_REVIEW_RESULT_TOKEN
    )
    assert (
        artifact_review_workstream["selected_next_target"]
        == POST_ARTIFACT_RETENTION_SELECTOR_TARGET
    )
    assert artifact_review_workstream["review_executes_migration_or_deletion"] == "no"

    post_artifact_workstream = _workstream(
        payload, "post_artifact_retention_enforcement_bounded_attack_selection"
    )
    assert post_artifact_workstream["status"] == "paused"
    assert (
        post_artifact_workstream["result_token"]
        == POST_ARTIFACT_RETENTION_ENFORCEMENT_RESULT_TOKEN
    )
    assert (
        post_artifact_workstream["selected_next_target"]
        == STATUS_SURFACE_CANONICALIZATION_PLAN_TARGET
    )
    assert post_artifact_workstream["selector_executes_selected_target"] == "no"

    status_plan_workstream = _workstream(payload, "status_surface_canonicalization_plan")
    assert status_plan_workstream["status"] == "paused"
    assert (
        status_plan_workstream["result_token"]
        == STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_TOKEN
    )
    assert (
        status_plan_workstream["selected_next_target"]
        == STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_REVIEW_TARGET
    )
    assert status_plan_workstream["broad_status_surface_rewrite_executed_here"] == "no"

    status_review_workstream = _workstream(
        payload, "status_surface_canonicalization_plan_result_review"
    )
    assert status_review_workstream["status"] == "paused"
    assert (
        status_review_workstream["result_token"]
        == STATUS_SURFACE_CANONICALIZATION_RESULT_REVIEW_RESULT_TOKEN
    )
    assert (
        status_review_workstream["selected_next_target"]
        == POST_STATUS_SURFACE_CANONICALIZATION_SELECTOR_TARGET
    )
    assert status_review_workstream["enforcement_packet_executed_here"] == "no"

    post_status_selector_workstream = _workstream(
        payload, "post_status_surface_canonicalization_bounded_attack_selection"
    )
    assert post_status_selector_workstream["status"] == "paused"
    assert (
        post_status_selector_workstream["result_token"]
        == POST_STATUS_SURFACE_CANONICALIZATION_SELECTOR_RESULT_TOKEN
    )
    assert (
        post_status_selector_workstream["selected_next_target"]
        == STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_TARGET
    )
    assert post_status_selector_workstream["selector_executes_selected_target"] == "no"

    enforcement_workstream = _workstream(
        payload, "status_surface_canonicalization_enforcement_packet"
    )
    assert enforcement_workstream["status"] == "paused"
    assert (
        enforcement_workstream["result_token"]
        == STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_RESULT_TOKEN
    )
    assert (
        enforcement_workstream["selected_next_target"]
        == STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_RESULT_REVIEW_TARGET
    )
    assert enforcement_workstream["broad_status_surface_rewrite_executed_here"] == "no"


def test_readme_registry_and_frontier_agree_on_live_target() -> None:
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()
    payload = _registry()
    readme_text = _read(README_PATH)
    frontier_text = _read(CROSS_PILLAR_FRONTIER_PATH)
    review_text = _read(QM_EVOLUTION_REVIEW_PATH)
    protocol_text = _read(EM_QFT_PROTOCOL_ROW_PATH)
    shared_bridge_text = _read(EM_QFT_SHARED_DYNAMICS_BRIDGE_PATH)
    interface_bridge_text = _read(EM_QFT_INTERFACE_ALIGNMENT_BRIDGE_PATH)
    em_qft_review_text = _read(EM_QFT_POST_BUDGET_REVIEW_PATH)
    citation_usage_text = _read(MASTER_ACTION_CITATION_USAGE_PATH)
    citation_audit_text = _read(MASTER_ACTION_CITATION_AUDIT_PATH)
    dependency_graph_review_text = _read(MASTER_ACTION_DEPENDENCY_GRAPH_REVIEW_PATH)
    prioritization_review_text = _read(
        MASTER_ACTION_RETAINED_BLOCKER_PRIORITIZATION_REVIEW_PATH
    )
    protocol_row_text = _read(QM_STAT_TRANSPORT_SEMANTICS_PROTOCOL_ROW_PATH)
    source_probability_text = _read(QM_STAT_SOURCE_PROBABILITY_EXTRACTION_PATH)
    source_probability_review_text = _read(QM_STAT_SOURCE_PROBABILITY_RESULT_REVIEW_PATH)
    post_qm_stat_prioritization_text = _read(
        MASTER_ACTION_POST_QMSTAT_PRIORITIZATION_REVIEW_PATH
    )
    qft_gr_protocol_row_text = _read(QFT_GR_SOURCE_MAP_SEMANTICS_PROTOCOL_ROW_PATH)
    qft_gr_readiness_review_text = _read(QFT_GR_SOURCE_MAP_SEMANTICS_READINESS_REVIEW_PATH)
    qft_gr_operator_domain_text = _read(QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_SEMANTICS_PATH)
    qft_gr_result_review_text = _read(
        QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_RESULT_REVIEW_PATH
    )
    full_pillar_target_map_text = _read(FULL_PILLAR_TARGET_MAP_REBASE_PATH)
    full_pillar_target_map_result_review_text = _read(
        FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_PATH
    )
    post_rebase_selection_text = _read(POST_REBASE_NEXT_BOUNDED_ATTACK_SELECTION_PATH)
    qft_gr_state_expectation_text = _read(
        QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_PATH
    )
    qft_gr_renormalized_expectation_text = _read(
        QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_PATH
    )
    qft_gr_renormalized_expectation_review_text = _read(
        QFT_GR_RENORMALIZED_EXPECTATION_VALUE_RESULT_REVIEW_PATH
    )
    qft_gr_classical_source_admissibility_text = _read(
        QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_PATH
    )
    qft_gr_classical_source_admissibility_review_text = _read(
        QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_RESULT_REVIEW_PATH
    )
    qft_gr_covariant_conservation_obligation_text = _read(
        QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_SEMANTICS_PATH
    )
    qft_gr_covariant_conservation_obligation_result_review_text = _read(
        QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_RESULT_REVIEW_PATH
    )
    qft_gr_bianchi_compatibility_obligation_text = _read(
        QFT_GR_BIANCHI_COMPATIBILITY_OBLIGATION_SEMANTICS_PATH
    )
    qft_gr_bianchi_compatibility_obligation_result_review_text = _read(
        QFT_GR_BIANCHI_COMPATIBILITY_OBLIGATION_RESULT_REVIEW_PATH
    )
    qft_gr_einstein_coupling_obligation_text = _read(
        QFT_GR_EINSTEIN_COUPLING_OBLIGATION_SEMANTICS_PATH
    )
    qft_gr_einstein_coupling_obligation_result_review_text = _read(
        QFT_GR_EINSTEIN_COUPLING_OBLIGATION_RESULT_REVIEW_PATH
    )
    qft_gr_weak_curvature_source_identification_obligation_text = _read(
        QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_SEMANTICS_PATH
    )
    qft_gr_weak_curvature_source_identification_obligation_result_review_text = _read(
        QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_RESULT_REVIEW_PATH
    )
    qft_gr_poisson_recovery_obligation_text = _read(
        QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_PATH
    )
    qft_gr_poisson_recovery_obligation_result_review_text = _read(
        QFT_GR_POISSON_RECOVERY_OBLIGATION_RESULT_REVIEW_PATH
    )
    qft_gr_source_map_eligibility_ladder_summary_text = _read(
        QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_PATH
    )
    qft_gr_source_map_eligibility_ladder_summary_result_review_text = _read(
        QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_RESULT_REVIEW_PATH
    )
    qft_gr_state_expectation_review_text = _read(
        QFT_GR_STATE_EXPECTATION_FUNCTIONAL_RESULT_REVIEW_PATH
    )
    qft_gr_renormalized_expectation_review_text = _read(
        QFT_GR_RENORMALIZED_EXPECTATION_VALUE_RESULT_REVIEW_PATH
    )

    assert CURRENT_TARGET_TOKEN in readme_text
    assert f'"live_next_target": "{LIVE_TARGET}"' in _read(REGISTRY_PATH)
    assert (
        'def currentLiveNextStrictTargetV0 : String :=\n'
        f'  "{LIVE_TARGET}"'
    ) in frontier_text
    assert (
        'def previousLiveNextStrictTargetV0 : String :=\n'
        f'  "{PREVIOUS_TARGET}"'
    ) in frontier_text
    assert (
        'def emQFTPhysicsBlockerExtractionTargetId : String :=\n'
        f'  "{EXTRACTION_TARGET}"'
    ) in review_text
    assert (
        'def emQFTSharedDynamicsResidualUnificationBridgeTargetId : String :=\n'
        f'  "{SHARED_DYNAMICS_TARGET}"'
    ) in protocol_text
    assert (
        'def emQFTInterfaceAlignmentSemanticBridgeTargetId : String :=\n'
        f'  "{INTERFACE_TARGET}"'
    ) in shared_bridge_text
    assert (
        'def emQFTPostBudgetCrossPillarReviewTargetId : String :=\n'
        f'  "{EM_QFT_POST_BUDGET_TARGET}"'
    ) in interface_bridge_text
    assert (
        'def masterActionCitationBoundaryTargetId : String :=\n'
        f'  "{CITATION_USAGE_TARGET}"'
    ) in em_qft_review_text
    assert (
        'def masterActionCitationUsageConsumedTargetId : String :=\n'
        f'  "{CITATION_USAGE_TARGET}"'
    ) in citation_usage_text
    assert (
        'def masterActionCitationLanguageAuditTargetId : String :=\n'
        f'  "{AUDIT_TARGET}"'
    ) in citation_usage_text
    assert (
        'def masterActionCitationLanguageAuditConsumedTargetId : String :=\n'
        f'  "{AUDIT_TARGET}"'
    ) in citation_audit_text
    assert (
        'def masterActionPostCitationAuditReviewTargetId : String :=\n'
        f'  "{REVIEW_TARGET}"'
    ) in citation_audit_text
    assert (
        'def masterActionDependencyGraphReviewConsumedTargetId : String :=\n'
        f'  "{REVIEW_TARGET}"'
    ) in dependency_graph_review_text
    assert (
        'def retainedBlockerPrioritizationReviewTargetId : String :=\n'
        f'  "{PRIORITIZATION_TARGET}"'
    ) in dependency_graph_review_text
    assert (
        'def retainedBlockerPrioritizationConsumedTargetId : String :=\n'
        f'  "{PRIORITIZATION_TARGET}"'
    ) in prioritization_review_text
    assert (
        'def qmStatTransportProtocolRowPreparationTargetId : String :=\n'
        f'  "{PROTOCOL_PREPARATION_TARGET}"'
    ) in prioritization_review_text
    assert (
        'def qmStatTransportSemanticsProtocolRowConsumedTargetId : String :=\n'
        f'  "{PROTOCOL_PREPARATION_TARGET}"'
    ) in protocol_row_text
    assert (
        'def qmStatTransportSemanticsReadinessReviewTargetId : String :=\n'
        f'  "{READINESS_REVIEW_TARGET}"'
    ) in protocol_row_text
    readiness_review_text = _read(QM_STAT_TRANSPORT_SEMANTICS_READINESS_REVIEW_PATH)
    assert (
        'def qmStatTransportSemanticsReadinessReviewConsumedTargetId : String :=\n'
        "  qmStatTransportSemanticsReadinessReviewTargetId"
    ) in readiness_review_text
    assert (
        'def qmStatSourceProbabilityExtractionSemanticsTargetId : String :=\n'
        f'  "{SOURCE_PROBABILITY_TARGET}"'
    ) in readiness_review_text
    assert (
        'def qmStatSourceProbabilityExtractionResultReviewTargetId : String :=\n'
        f'  "{SOURCE_PROBABILITY_RESULT_REVIEW_TARGET}"'
    ) in source_probability_text
    assert (
        'def qmStatSourceProbabilityExtractionResultReviewConsumedTargetId : String :=\n'
        "  qmStatSourceProbabilityExtractionResultReviewTargetId"
    ) in source_probability_review_text
    assert (
        'def qmStatPostSourceProbabilityRetainedBlockerPrioritizationTargetId : String :=\n'
        f'  "{POST_QMSTAT_PRIORITIZATION_TARGET}"'
    ) in source_probability_review_text
    assert (
        'def postQMSTATRetainedBlockerPrioritizationConsumedTargetId : String :=\n'
        "  qmStatPostSourceProbabilityRetainedBlockerPrioritizationTargetId"
    ) in post_qm_stat_prioritization_text
    assert (
        'def qftGRSourceMapProtocolRowPreparationTargetId : String :=\n'
        f'  "{QFT_GR_PROTOCOL_ROW_PREPARATION_TARGET}"'
    ) in post_qm_stat_prioritization_text
    assert (
        'def qftGRSourceMapSemanticsProtocolRowConsumedTargetId : String :=\n'
        "  qftGRSourceMapProtocolRowPreparationTargetId"
    ) in qft_gr_protocol_row_text
    assert (
        'def qftGRSourceMapSemanticsReadinessReviewTargetId : String :=\n'
        f'  "{QFT_GR_PROTOCOL_ROW_READINESS_REVIEW_TARGET}"'
    ) in qft_gr_protocol_row_text
    assert (
        'def qftGRSourceMapSemanticsReadinessReviewConsumedTargetId : String :=\n'
        "  qftGRSourceMapSemanticsReadinessReviewTargetId"
    ) in qft_gr_readiness_review_text
    assert (
        'def qftGRStressEnergyOperatorDomainSemanticsTargetId : String :=\n'
        f'  "{QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_TARGET}"'
    ) in qft_gr_readiness_review_text
    assert (
        'def qftGRStressEnergyOperatorDomainSemanticsConsumedTargetId : String :=\n'
        "  qftGRStressEnergyOperatorDomainSemanticsTargetId"
    ) in qft_gr_operator_domain_text
    assert (
        'def qftGRStressEnergyOperatorDomainResultReviewTargetId : String :=\n'
        f'  "{QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_RESULT_REVIEW_TARGET}"'
    ) in qft_gr_operator_domain_text
    assert (
        'def qftGRStressEnergyOperatorDomainResultReviewConsumedTargetId : String :=\n'
        "  qftGRStressEnergyOperatorDomainResultReviewTargetId"
    ) in qft_gr_result_review_text
    assert (
        'def fullPillarTargetMapRebasePreparationTargetId : String :=\n'
        f'  "{FULL_PILLAR_TARGET_MAP_REBASE_TARGET}"'
    ) in qft_gr_result_review_text
    assert (
        'def fullPillarTargetMapRebaseConsumedTargetId : String :=\n'
        "  fullPillarTargetMapRebasePreparationTargetId"
    ) in full_pillar_target_map_text
    assert (
        'def fullPillarTargetMapRebaseResultReviewTargetId : String :=\n'
        f'  "{FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_TARGET}"'
    ) in full_pillar_target_map_text
    assert "def fullPillarTargetMapRebaseResultReviewConsumedTargetId : String :=" in (
        full_pillar_target_map_result_review_text
    )
    assert (
        'def postRebaseNextBoundedAttackSelectionTargetId : String :=\n'
        f'  "{POST_REBASE_NEXT_BOUNDED_ATTACK_SELECTION_TARGET}"'
    ) in full_pillar_target_map_result_review_text
    assert (
        'def postRebaseNextBoundedAttackSelectionConsumedTargetId : String :=\n'
        "  postRebaseNextBoundedAttackSelectionTargetId"
    ) in post_rebase_selection_text
    assert (
        'def selectedPostRebaseBoundedAttackTargetV0 : String :=\n'
        f'  "{SELECTED_POST_REBASE_BOUNDED_ATTACK_TARGET}"'
    ) in post_rebase_selection_text
    assert (
        'def qftGRStateExpectationFunctionalSemanticsConsumedTargetId : String :=\n'
        "  qftGRStateExpectationFunctionalSemanticsTargetId"
    ) in qft_gr_state_expectation_text
    assert (
        'def qftGRStateExpectationFunctionalResultReviewTargetId : String :=\n'
        f'  "{QFT_GR_STATE_EXPECTATION_FUNCTIONAL_RESULT_REVIEW_TARGET}"'
    ) in qft_gr_state_expectation_text
    assert (
        'def qftGRStateExpectationFunctionalResultReviewConsumedTargetId : String :=\n'
        "  qftGRStateExpectationFunctionalResultReviewTargetId"
    ) in qft_gr_state_expectation_review_text
    assert (
        'def qftGRRenormalizedExpectationValueSemanticsPreparationTargetId : String :=\n'
        f'  "{QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_TARGET}"'
    ) in qft_gr_state_expectation_review_text
    assert (
        'def qftGRRenormalizedExpectationValueSemanticsConsumedTargetId : String :=\n'
        "  qftGRRenormalizedExpectationValueSemanticsTargetId"
    ) in qft_gr_renormalized_expectation_text
    assert (
        'def qftGRRenormalizedExpectationValueResultReviewTargetId : String :=\n'
        f'  "{QFT_GR_RENORMALIZED_EXPECTATION_VALUE_RESULT_REVIEW_TARGET}"'
    ) in qft_gr_renormalized_expectation_text
    assert (
        'def qftGRRenormalizedExpectationValueResultReviewConsumedTargetId : String :=\n'
        "  qftGRRenormalizedExpectationValueResultReviewTargetId"
    ) in qft_gr_renormalized_expectation_review_text
    assert (
        'def qftGRClassicalSourceAdmissibilitySemanticsPreparationTargetId : String :=\n'
        f'  "{QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_TARGET}"'
    ) in qft_gr_renormalized_expectation_review_text
    assert (
        'def qftGRClassicalSourceAdmissibilityResultReviewTargetId : String :=\n'
        f'  "{QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_RESULT_REVIEW_TARGET}"'
    ) in qft_gr_classical_source_admissibility_text
    assert (
        'def qftGRCovariantConservationObligationSemanticsPreparationTargetId : String :=\n'
        f'  "{QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_SEMANTICS_TARGET}"'
    ) in qft_gr_classical_source_admissibility_review_text
    assert (
        'def qftGRCovariantConservationObligationSemanticsConsumedTargetId : String :=\n'
        "  qftGRCovariantConservationObligationSemanticsTargetId"
    ) in qft_gr_covariant_conservation_obligation_text
    assert (
        'def qftGRCovariantConservationObligationResultReviewTargetId : String :=\n'
        f'  "{QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_RESULT_REVIEW_TARGET}"'
    ) in qft_gr_covariant_conservation_obligation_text
    assert (
        'def qftGRCovariantConservationObligationResultReviewConsumedTargetId : String :=\n'
        "  qftGRCovariantConservationObligationResultReviewTargetId"
    ) in qft_gr_covariant_conservation_obligation_result_review_text
    assert (
        'def qftGRBianchiCompatibilityObligationSemanticsPreparationTargetId : String :=\n'
        f'  "{QFT_GR_BIANCHI_COMPATIBILITY_OBLIGATION_SEMANTICS_TARGET}"'
    ) in qft_gr_covariant_conservation_obligation_result_review_text
    assert (
        'def qftGRBianchiCompatibilityObligationResultReviewTargetId : String :=\n'
        f'  "{QFT_GR_BIANCHI_COMPATIBILITY_OBLIGATION_RESULT_REVIEW_TARGET}"'
    ) in qft_gr_bianchi_compatibility_obligation_text
    assert (
        'def qftGRBianchiCompatibilityObligationSemanticsConsumedTargetId : String :=\n'
        "  qftGRBianchiCompatibilityObligationSemanticsTargetId"
    ) in qft_gr_bianchi_compatibility_obligation_text
    assert (
        'def qftGREinsteinCouplingObligationSemanticsPreparationTargetId : String :=\n'
        f'  "{QFT_GR_EINSTEIN_COUPLING_OBLIGATION_SEMANTICS_TARGET}"'
    ) in qft_gr_bianchi_compatibility_obligation_result_review_text
    assert (
        'def qftGREinsteinCouplingObligationSemanticsConsumedTargetId : String :=\n'
        "  qftGREinsteinCouplingObligationSemanticsTargetId"
    ) in qft_gr_einstein_coupling_obligation_text
    assert (
        'def qftGREinsteinCouplingObligationResultReviewTargetId : String :=\n'
        f'  "{QFT_GR_EINSTEIN_COUPLING_OBLIGATION_RESULT_REVIEW_TARGET}"'
    ) in qft_gr_einstein_coupling_obligation_text
    assert (
        'def qftGRWeakCurvatureSourceIdentificationObligationSemanticsPreparationTargetId :\n'
        "    String :=\n"
        f'  "{QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_SEMANTICS_TARGET}"'
    ) in qft_gr_einstein_coupling_obligation_result_review_text
    assert (
        'def qftGRWeakCurvatureSourceIdentificationObligationSemanticsConsumedTargetId :\n'
        "    String :=\n"
        "  qftGRWeakCurvatureSourceIdentificationObligationSemanticsTargetId"
    ) in qft_gr_weak_curvature_source_identification_obligation_text
    assert (
        'def qftGRWeakCurvatureSourceIdentificationObligationResultReviewTargetId :\n'
        "    String :=\n"
        f'  "{QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_RESULT_REVIEW_TARGET}"'
    ) in qft_gr_weak_curvature_source_identification_obligation_text
    assert (
        'def qftGRWeakCurvatureSourceIdentificationObligationResultReviewConsumedTargetId :\n'
        "    String :=\n"
        "  qftGRWeakCurvatureSourceIdentificationObligationResultReviewTargetId"
    ) in qft_gr_weak_curvature_source_identification_obligation_result_review_text
    assert (
        'def qftGRPoissonRecoveryObligationSemanticsPreparationTargetId : String :=\n'
        f'  "{QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_TARGET}"'
    ) in qft_gr_weak_curvature_source_identification_obligation_result_review_text
    assert (
        'def qftGRPoissonRecoveryObligationSemanticsConsumedTargetId : String :=\n'
        "  qftGRPoissonRecoveryObligationSemanticsTargetId"
    ) in qft_gr_poisson_recovery_obligation_text
    assert (
        'def qftGRPoissonRecoveryObligationResultReviewTargetId : String :=\n'
        f'  "{QFT_GR_POISSON_RECOVERY_OBLIGATION_RESULT_REVIEW_TARGET}"'
    ) in qft_gr_poisson_recovery_obligation_text
    assert (
        'def qftGRPoissonRecoveryObligationResultReviewConsumedTargetId : String :=\n'
        "  qftGRPoissonRecoveryObligationResultReviewTargetId"
    ) in qft_gr_poisson_recovery_obligation_result_review_text
    assert (
        'def qftGRSourceMapEligibilityLadderSummaryPreparationTargetId : String :=\n'
        f'  "{QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_TARGET}"'
    ) in qft_gr_poisson_recovery_obligation_result_review_text
    assert (
        'def qftGRSourceMapEligibilityLadderSummaryConsumedTargetId : String :=\n'
        "  qftGRSourceMapEligibilityLadderSummaryPreparationTargetId"
    ) in qft_gr_source_map_eligibility_ladder_summary_text
    assert (
        'def qftGRSourceMapEligibilityLadderSummaryResultReviewTargetId : String :=\n'
        f'  "{QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_RESULT_REVIEW_TARGET}"'
    ) in qft_gr_source_map_eligibility_ladder_summary_text
    assert (
        'def qftGRSourceMapEligibilityLadderSummaryResultReviewConsumedTargetId : String :=\n'
        "  qftGRSourceMapEligibilityLadderSummaryResultReviewTargetId"
    ) in qft_gr_source_map_eligibility_ladder_summary_result_review_text
    assert (
        'def qftGRPostLadderBoundedAttackSelectionTargetId : String :=\n'
        f'  "{POST_QFT_GR_LADDER_BOUNDED_ATTACK_SELECTION_TARGET}"'
    ) in qft_gr_source_map_eligibility_ladder_summary_result_review_text
    assert (
        'def qftGRClassicalSourceAdmissibilitySemanticsConsumedTargetId : String :=\n'
        "  qftGRClassicalSourceAdmissibilitySemanticsTargetId"
    ) in qft_gr_classical_source_admissibility_text
    assert payload["current_target_state"]["live_next_target"] == LIVE_TARGET


def test_no_stale_live_next_action_survives_in_registry() -> None:
    payload = _registry()
    scalar = _control(payload, "scalar_post_capstone_anti_loop")
    assert scalar["status"] == "paused"
    assert scalar["next_action"] == SCALAR_PAUSED_ACTION

    stale_live_paths: list[str] = []
    checked_key_suffixes = {"next_action", "next_strict_target", "next_action_after_retention"}
    for path, value in _iter_key_values(payload):
        if path and path[-1] in checked_key_suffixes and value == STALE_SCALAR_ACTION:
            stale_live_paths.append(".".join(path))
    assert not stale_live_paths, (
        "Completed bridge target still appears as a live next action: "
        + ", ".join(stale_live_paths)
    )

    qm_evolution = _workstream(payload, "qm_evolution_contract")
    assert qm_evolution["post_budget_review_status"] == "completed"
    assert qm_evolution["same_lane_continuation"] == "not_authorized"
    assert qm_evolution["next_strict_target"] == EXTRACTION_TARGET
    assert qm_evolution["next_action_after_retention"] == EXTRACTION_TARGET
    assert qm_evolution["stronger_qm_dynamics_bridge_derivation"] == "not_supplied"

    em_qft = _workstream(payload, "em_qft_physics_blocker_extraction")
    assert em_qft["status"] == "paused"
    assert em_qft["post_budget_review_status"] == "completed"
    assert em_qft["post_budget_review_evidence"] == str(
        EM_QFT_POST_BUDGET_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert em_qft["same_lane_continuation"] == "not_authorized_attempt_budget_reached"
    assert em_qft["source_current_bridge_slice_authorized"] == "not_authorized"
    assert em_qft["gauge_quantization_bridge_slice_authorized"] == "not_authorized"

    qft_gr = _workstream(payload, "qft_gr_source_map")
    assert qft_gr["status"] == "paused"
    assert qft_gr["authorized_next_strict_target"] == LIVE_TARGET
    assert qft_gr["protocol_row_preparation_target"] == QFT_GR_PROTOCOL_ROW_PREPARATION_TARGET
    assert (
        qft_gr["protocol_row_preparation_status"]
        == "completed_protocol_row_prepared"
    )
    assert qft_gr["protocol_row_preparation_authorized"] == "preparation_only_no_theorem_work"
    assert qft_gr["protocol_row_status"] == "prepared_from_post_qm_stat_prioritization"
    assert qft_gr["protocol_row_evidence"] == str(
        QFT_GR_SOURCE_MAP_SEMANTICS_PROTOCOL_ROW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert qft_gr["protocol_row_next_review"] == QFT_GR_PROTOCOL_ROW_READINESS_REVIEW_TARGET
    assert qft_gr["source_map_semantics_primary_blocker"] == "full_source_map_semantic_closure"
    assert (
        qft_gr["stress_energy_operator_domain_obligation"]
        == "retained_as_supplied_semantics_not_package_derived"
    )
    assert qft_gr["stress_energy_operator_domain_semantics_status"] == (
        "completed_supplied_route_available_package_only_refuted"
    )
    assert qft_gr["stress_energy_operator_domain_supplied_route_available"] == "yes"
    assert qft_gr["stress_energy_operator_domain_package_only_refuted"] == "yes"
    assert qft_gr["stress_energy_operator_domain_derived_from_source_map_package_alone"] == "no"
    assert qft_gr["state_expectation_functional_semantics_status"] == (
        "completed_supplied_route_available_package_only_refuted"
    )
    assert qft_gr["state_expectation_functional_supplied_route_available"] == "yes"
    assert qft_gr["state_expectation_functional_package_only_refuted"] == "yes"
    assert (
        qft_gr["state_expectation_functional_derived_from_source_map_package_alone"]
        == "no"
    )
    assert qft_gr["state_expectation_functional_result_token"] == (
        "QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_SUPPLIED_ONLY"
    )
    assert qft_gr["state_expectation_functional_result_review_target"] == (
        QFT_GR_STATE_EXPECTATION_FUNCTIONAL_RESULT_REVIEW_TARGET
    )
    assert (
        qft_gr["state_expectation_functional_result_review_status"] == "completed"
    )
    assert qft_gr["state_expectation_functional_result_review_evidence"] == str(
        QFT_GR_STATE_EXPECTATION_FUNCTIONAL_RESULT_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert qft_gr["qft_state_expectation_functional_obligation"] == (
        "retained_as_supplied_semantics_not_package_derived"
    )
    assert qft_gr["renormalized_expectation_obligation"] == (
        "retained_as_supplied_semantics_not_state_expectation_derived"
    )
    assert qft_gr["gr_weak_curvature_source_identification_obligation"] == "still_required"
    assert qft_gr["covariance_conservation_obligation"] == "still_required"
    assert qft_gr["qft_state_expectation_functional_semantics_authorized"] == (
        "supplied_only_retained"
    )
    assert qft_gr["renormalized_expectation_semantics_authorized"] == "no"
    assert qft_gr["renormalized_expectation_value_semantics_status"] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_SUPPLIED_ONLY"
    )
    assert (
        qft_gr["renormalized_expectation_value_semantics_supplied_route_available"]
        == "yes"
    )
    assert (
        qft_gr["renormalized_expectation_value_state_expectation_only_refuted"]
        == "yes"
    )
    assert (
        qft_gr["renormalized_expectation_value_derived_from_state_expectation_alone"]
        == "no"
    )
    assert qft_gr["gr_weak_curvature_source_identification_semantics_authorized"] == "no"
    assert qft_gr["covariance_conservation_semantics_authorized"] == "no"
    assert qft_gr["full_source_map_semantic_closure_authorized"] == "no"
    assert qft_gr["readiness_review_status"] == "completed"
    assert qft_gr["readiness_review_evidence"] == str(
        QFT_GR_SOURCE_MAP_SEMANTICS_READINESS_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert qft_gr["readiness_review_decision"] == (
        "authorize_bounded_stress_energy_operator_domain_semantics"
    )
    assert qft_gr["bounded_stress_energy_operator_domain_slice_authorized"] == "completed"
    assert qft_gr["stress_energy_operator_domain_result_review_status"] == "completed"
    assert qft_gr["stress_energy_operator_domain_result_review_evidence"] == str(
        QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_RESULT_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert qft_gr["stress_energy_operator_domain_result_review_decision"] == (
        "pause_qft_gr_and_prepare_full_pillar_target_map_rebase"
    )
    assert (
        qft_gr["stress_energy_operator_domain_result_review_target"]
        == QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_RESULT_REVIEW_TARGET
    )
    assert qft_gr["theorem_work_authorized"] == (
        "gap_packet_result_review_completed_selector_only_no_promotion_claim"
    )
    assert qft_gr["same_lane_continuation"] == (
        "post_gap_packet_selector_only_no_promotion_claim"
    )
    assert qft_gr["einstein_coupling_obligation_semantics_surface"] == str(
        QFT_GR_EINSTEIN_COUPLING_OBLIGATION_SEMANTICS_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert qft_gr["einstein_coupling_obligation_semantics_result_token"] == (
        "QFT_GR_EINSTEIN_COUPLING_OBLIGATION_SEMANTICS_SUPPLIED_ONLY"
    )
    assert qft_gr["einstein_coupling_obligation_bianchi_only_refuted"] == "yes"
    assert qft_gr["einstein_coupling_witness_derived_from_bianchi_obligation_alone"] == (
        "no"
    )
    assert qft_gr["einstein_coupling_witness_authorized"] == "no"
    assert qft_gr["actual_einstein_equation_coupling_authorized"] == "no"
    assert qft_gr["einstein_coupling_obligation_semantics_result_review_status"] == (
        "completed"
    )
    assert qft_gr["einstein_coupling_obligation_semantics_result_review_evidence"] == str(
        QFT_GR_EINSTEIN_COUPLING_OBLIGATION_RESULT_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert qft_gr[
        "weak_curvature_source_identification_obligation_semantics_preparation_target"
    ] == QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_SEMANTICS_TARGET
    assert qft_gr[
        "weak_curvature_source_identification_obligation_semantics_authorized"
    ] == "supplied_only_retained"
    assert qft_gr["weak_curvature_source_identification_obligation_semantics_surface"] == str(
        QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_SEMANTICS_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert qft_gr[
        "weak_curvature_source_identification_obligation_semantics_result_token"
    ] == "QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_SEMANTICS_SUPPLIED_ONLY"
    assert qft_gr[
        "weak_curvature_source_identification_obligation_result_review_status"
    ] == "completed"
    assert qft_gr[
        "weak_curvature_source_identification_obligation_result_review_evidence"
    ] == str(
        QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_RESULT_REVIEW_PATH.relative_to(
            REPO_ROOT
        )
    ).replace("\\", "/")
    assert qft_gr[
        "weak_curvature_source_identification_obligation_result_review_token"
    ] == (
        "QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_SEMANTICS_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
    )
    assert qft_gr["poisson_recovery_obligation_semantics_preparation_target"] == (
        QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_TARGET
    )
    assert qft_gr["poisson_recovery_obligation_semantics_authorized"] == (
        "supplied_only_retained"
    )
    assert qft_gr["poisson_recovery_obligation_semantics_constructed"] == "yes"
    assert qft_gr["poisson_recovery_obligation_semantics_surface"] == str(
        QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert qft_gr["poisson_recovery_obligation_semantics_result_token"] == (
        "QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_SUPPLIED_ONLY"
    )
    assert qft_gr["poisson_recovery_obligation_result_review_status"] == "completed"
    assert qft_gr["poisson_recovery_obligation_result_review_evidence"] == str(
        QFT_GR_POISSON_RECOVERY_OBLIGATION_RESULT_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert qft_gr["source_map_eligibility_ladder_summary_preparation_target"] == (
        QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_TARGET
    )
    assert qft_gr["source_map_eligibility_ladder_summary_authorized"] == (
        "preparation_only"
    )
    assert qft_gr["source_map_eligibility_ladder_summary_constructed"] == (
        "yes_obligation_ladder_only"
    )
    assert qft_gr["source_map_eligibility_ladder_summary_status"] == "completed"
    assert qft_gr["source_map_eligibility_ladder_summary_evidence"] == str(
        QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert qft_gr["source_map_eligibility_ladder_summary_result_token"] == (
        "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_CONSTRUCTED_CLOSURE_NOT_AUTHORIZED"
    )
    assert qft_gr["source_map_eligibility_ladder_summary_result_review_target"] == (
        QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_RESULT_REVIEW_TARGET
    )
    assert qft_gr[
        "qft_gr_source_map_eligibility_ladder_summary_result_review_status"
    ] == "completed"
    assert qft_gr[
        "qft_gr_source_map_eligibility_ladder_summary_result_review_evidence"
    ] == str(
        QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_RESULT_REVIEW_PATH.relative_to(
            REPO_ROOT
        )
    ).replace("\\", "/")
    assert qft_gr[
        "qft_gr_source_map_eligibility_ladder_summary_result_review_token"
    ] == (
        "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_RESULT_REVIEW_CONSUMED_CLOSURE_NOT_AUTHORIZED"
    )
    assert qft_gr["source_map_eligibility_ladder_constructed"] == (
        "yes_obligation_ladder_only"
    )
    assert qft_gr["witness_chain_status"] == "absent"
    assert qft_gr["witness_search_micro_lane_authorized"] == "no"
    assert qft_gr["poisson_recovery_weak_curvature_obligation_only_refuted"] == "yes"
    assert qft_gr[
        "poisson_recovery_witness_derived_from_weak_curvature_obligation_alone"
    ] == "no"
    assert qft_gr["weak_curvature_source_identification_einstein_only_refuted"] == (
        "yes"
    )
    assert qft_gr[
        "source_identification_witness_derived_from_einstein_obligation_alone"
    ] == "no"
    assert qft_gr["actual_weak_curvature_source_identification_authorized"] == "no"
    assert qft_gr["poisson_limit_recovery_authorized"] == "no"
    assert qft_gr["newtonian_limit_recovery_authorized"] == "no"
    assert (
        qft_gr["full_pillar_target_map_rebase_target"]
        == FULL_PILLAR_TARGET_MAP_REBASE_TARGET
    )

    qm_stat = _workstream(payload, "qm_stat_transport_residual")
    assert qm_stat["status"] == "paused"
    assert qm_stat["authorized_next_strict_target"] == POST_QMSTAT_PRIORITIZATION_TARGET
    assert qm_stat["authorization_evidence"] == str(
        QM_STAT_SOURCE_PROBABILITY_EXTRACTION_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert qm_stat["latest_surface"] == "QM_STAT_SOURCE_PROBABILITY_EXTRACTION_SEMANTICS_v0"
    assert qm_stat["bounded_source_probability_slice_authorized"] == "completed"
    assert qm_stat["source_probability_extraction_contract_only_refuted"] == "yes"
    assert qm_stat["source_probability_extraction_derived_from_contract_alone"] == "no"
    assert qm_stat["theorem_work_authorized"] == "no_result_review_completed_same_lane_paused"
    assert qm_stat["source_probability_result_review_status"] == "completed"
    assert qm_stat["source_probability_result_review_evidence"] == str(
        QM_STAT_SOURCE_PROBABILITY_RESULT_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert (
        qm_stat["source_probability_result_review_decision"]
        == "pause_qm_stat_and_prioritize_retained_blockers"
    )
    assert qm_stat["target_entropy_semantics_authorized"] == "no"
    assert qm_stat["transport_map_semantics_authorized"] == "no"
    assert qm_stat["coarse_graining_irreversibility_authorized"] == "no"
    assert qm_stat["residual_package_semantic_closure_authorized"] == "no"

    master_action = _workstream(payload, "master_action_dependency_frontier")
    assert master_action["status"] == "paused"
    assert master_action["citation_usage_status"] == "completed"
    assert master_action["citation_language_audit_status"] == "completed"
    assert master_action["dependency_graph_review_status"] == "completed"
    assert master_action["qm_stat_transport_semantics_protocol_row_status"] == "prepared"
    assert master_action["readiness_review_status"] == "completed"
    assert master_action["source_probability_extraction_status"] == (
        "completed_supplied_route_available_contract_only_refuted"
    )
    assert master_action["source_probability_result_review_status"] == "completed"
    assert master_action["source_probability_result_review_evidence"] == str(
        QM_STAT_SOURCE_PROBABILITY_RESULT_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert (
        master_action["source_probability_result_review_decision"]
        == "pause_qm_stat_and_prioritize_retained_blockers"
    )
    assert master_action["post_qm_stat_retained_blocker_prioritization_status"] == "completed"
    assert master_action["post_qm_stat_retained_blocker_prioritization_evidence"] == str(
        MASTER_ACTION_POST_QMSTAT_PRIORITIZATION_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert (
        master_action["post_qm_stat_top_retained_blocker"]
        == "PHASE1-BLOCKER-QFTGR-STRESS-ENERGY-EXPECTATION-SOURCE-MAP-RETAINED"
    )
    assert (
        master_action["qft_gr_source_map_protocol_row_preparation_target"]
        == QFT_GR_PROTOCOL_ROW_PREPARATION_TARGET
    )
    assert (
        master_action["qft_gr_source_map_protocol_row_preparation_status"]
        == "completed_protocol_row_prepared"
    )
    assert master_action["qft_gr_source_map_protocol_row_status"] == "prepared"
    assert master_action["qft_gr_protocol_row_authority_row"] == "ROW-SEAM-QFT-GR-001"
    assert master_action["qft_gr_protocol_row_seam"] == "SEAM-QFT-GR"
    assert (
        master_action["qft_gr_protocol_row_next_review"]
        == QFT_GR_PROTOCOL_ROW_READINESS_REVIEW_TARGET
    )
    assert master_action["qft_gr_protocol_row_evidence"] == str(
        QFT_GR_SOURCE_MAP_SEMANTICS_PROTOCOL_ROW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert master_action["qft_gr_protocol_row_primary_blocker"] == (
        "full_source_map_semantic_closure"
    )
    assert master_action["qft_gr_protocol_row_readiness_review_status"] == "completed"
    assert master_action["qft_gr_protocol_row_readiness_review_evidence"] == str(
        QFT_GR_SOURCE_MAP_SEMANTICS_READINESS_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert master_action["qft_gr_protocol_row_readiness_review_decision"] == (
        "authorize_bounded_stress_energy_operator_domain_semantics"
    )
    assert master_action["qft_gr_stress_energy_operator_domain_semantics_status"] == (
        "completed_supplied_route_available_package_only_refuted"
    )
    assert master_action["qft_gr_stress_energy_operator_domain_semantics_evidence"] == str(
        QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_SEMANTICS_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert master_action["qft_gr_stress_energy_operator_domain_result_review_status"] == (
        "completed"
    )
    assert master_action["qft_gr_stress_energy_operator_domain_result_review_evidence"] == str(
        QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_RESULT_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert master_action["qft_gr_stress_energy_operator_domain_result_review_decision"] == (
        "pause_qft_gr_and_prepare_full_pillar_target_map_rebase"
    )
    assert master_action["state_expectation_functional_semantics_status"] == (
        "completed_supplied_route_available_package_only_refuted"
    )
    assert master_action["state_expectation_functional_semantics_evidence"] == str(
        QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert master_action["state_expectation_functional_result_token"] == (
        "QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_SUPPLIED_ONLY"
    )
    assert master_action["state_expectation_functional_result_review_status"] == (
        "completed"
    )
    assert master_action["state_expectation_functional_result_review_evidence"] == str(
        QFT_GR_STATE_EXPECTATION_FUNCTIONAL_RESULT_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert master_action["theorem_work_authorized"] == (
        "gap_packet_result_review_completed_selector_only_no_promotion_claim"
    )
    assert master_action["authorized_next_strict_target"] == LIVE_TARGET
    assert (
        master_action["next_action_scope"]
        == "return_to_full_pillar_target_map_next_lane_selection"
    )
    assert master_action["qft_gr_source_map_eligibility_ladder_summary_status"] == (
        "completed"
    )
    assert master_action["qft_gr_source_map_eligibility_ladder_summary_evidence"] == str(
        QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert master_action[
        "qft_gr_source_map_eligibility_ladder_summary_result_review_status"
    ] == "completed"
    assert master_action[
        "qft_gr_source_map_eligibility_ladder_summary_result_review_evidence"
    ] == str(
        QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_RESULT_REVIEW_PATH.relative_to(
            REPO_ROOT
        )
    ).replace("\\", "/")
    assert master_action["source_map_eligibility_ladder_constructed"] == (
        "yes_obligation_ladder_only"
    )
    assert master_action["witness_chain_status"] == "absent"
    assert master_action["witness_search_micro_lane_authorized"] == "no"
    assert master_action["full_source_map_closure_authorized"] == "no"
    assert master_action["dependency_graph_changed"] == "no"
    assert master_action["lane_unblocked"] == "no"
    assert master_action["promotion_authorized"] == "no"
    assert master_action["master_action_dependency_gap_packet_result_review_status"] == (
        "completed"
    )
    assert master_action["master_action_dependency_gap_packet_result_review_token"] == (
        "MASTER_ACTION_DEPENDENCY_GAP_PACKET_RESULT_REVIEW_CONSUMED_NONPROMOTED"
    )

    full_target_map = _workstream(payload, "full_pillar_target_map_rebase")
    assert full_target_map["status"] == "paused"
    assert (
        full_target_map["authorized_next_strict_target"]
        == FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_TARGET
    )
    assert (
        full_target_map["consumed_target"]
        == QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_RESULT_REVIEW_TARGET
    )
    assert full_target_map["latest_surface"] == "FULL_PILLAR_TARGET_MAP_REBASE_v0"
    assert full_target_map["target_map_evidence"] == str(
        FULL_PILLAR_TARGET_MAP_REBASE_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert full_target_map["target_map_document"] == (
        "formal/docs/paper/FULL_PILLAR_TARGET_MAP_REBASE_v0.md"
    )
    assert full_target_map["route_source_required"] == "yes"
    assert full_target_map["completion_scale_required"] == "yes"
    assert full_target_map["claim_posture_taxonomy_bound"] == "yes"
    assert full_target_map["master_action_status"] == "MASTER_ACTION_CITATION_BOUND"
    assert full_target_map["full_pillar_completion_claim"] == "no"
    assert full_target_map["master_action_promotion_authorized"] == "no"
    assert full_target_map["theorem_work_authorized"] == (
        "result_review_only_after_target_map_rebase"
    )
    assert full_target_map["same_lane_continuation"] == (
        "result_review_only_after_target_map_rebase"
    )
    assert (
        full_target_map["target_map_result_review_target"]
        == FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_TARGET
    )
    assert full_target_map["target_map_result_review_surface"] == str(
        FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert (
        full_target_map["target_map_result_review_report"]
        == "formal/docs/release/FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_20260503_v0.json"
    )
    assert (
        full_target_map["target_map_result_review_status"]
        == "prepared_for_live_result_review"
    )

    full_target_map_review = _workstream(
        payload, "full_pillar_target_map_rebase_result_review"
    )
    assert full_target_map_review["status"] == "paused"
    assert (
        full_target_map_review["authorized_next_strict_target"]
        == POST_REBASE_NEXT_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert (
        full_target_map_review["consumed_target"]
        == FULL_PILLAR_TARGET_MAP_REBASE_TARGET
    )
    assert (
        full_target_map_review["latest_surface"]
        == "full_pillar_target_map_rebase_result_review_v0"
    )
    assert full_target_map_review["target_map_authority_only"] == "yes"
    assert full_target_map_review["unauthorized_claims_introduced"] == "no"
    assert full_target_map_review["next_physics_attack_selected"] == "no"
    assert (
        full_target_map_review["selection_target"]
        == POST_REBASE_NEXT_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert full_target_map_review["selection_surface"] == str(
        POST_REBASE_NEXT_BOUNDED_ATTACK_SELECTION_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")

    post_rebase_selection = _workstream(
        payload, "post_rebase_next_bounded_attack_selection"
    )
    assert post_rebase_selection["status"] == "paused"
    assert (
        post_rebase_selection["authorized_next_strict_target"]
        == SELECTED_POST_REBASE_BOUNDED_ATTACK_TARGET
    )
    assert (
        post_rebase_selection["consumed_target"]
        == FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_TARGET
    )
    assert post_rebase_selection["selected_class"] == (
        "QFT_GR_SOURCE_MAP_CLOSURE_ELIGIBILITY_LANE"
    )
    assert post_rebase_selection["selected_next_target"] == (
        SELECTED_POST_REBASE_BOUNDED_ATTACK_TARGET
    )
    assert post_rebase_selection["selection_executes_attack"] == "no"
    assert (
        post_rebase_selection["state_expectation_functional_result_review_target"]
        == QFT_GR_STATE_EXPECTATION_FUNCTIONAL_RESULT_REVIEW_TARGET
    )

    state_expectation_review = _workstream(
        payload, "qft_gr_state_expectation_functional_semantics_result_review"
    )
    assert state_expectation_review["status"] == "paused"
    assert state_expectation_review["authorized_next_strict_target"] == (
        QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_TARGET
    )
    assert state_expectation_review["consumed_target"] == (
        QFT_GR_STATE_EXPECTATION_FUNCTIONAL_RESULT_REVIEW_TARGET
    )
    assert state_expectation_review["latest_surface"] == (
        "qft_gr_state_expectation_functional_semantics_result_review_v0"
    )
    assert state_expectation_review["result_review_status"] == (
        "completed"
    )

    renormalized_prep = _workstream(
        payload, "qft_gr_renormalized_expectation_value_semantics_preparation"
    )
    assert renormalized_prep["status"] == "paused"
    assert renormalized_prep["authorized_next_strict_target"] == (
        QFT_GR_RENORMALIZED_EXPECTATION_VALUE_RESULT_REVIEW_TARGET
    )
    assert (
        renormalized_prep["consumed_target"]
        == QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_TARGET
    )
    assert renormalized_prep["latest_surface"] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_v0"
    )
    assert renormalized_prep["renormalized_expectation_semantics_authorized"] == "no"

    renormalized_review = _workstream(
        payload, "qft_gr_renormalized_expectation_value_semantics_result_review"
    )
    assert renormalized_review["status"] == "paused"
    assert renormalized_review["authorized_next_strict_target"] == (
        QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_TARGET
    )
    assert renormalized_review["consumed_target"] == (
        QFT_GR_RENORMALIZED_EXPECTATION_VALUE_RESULT_REVIEW_TARGET
    )
    assert renormalized_review["latest_surface"] == (
        "qft_gr_renormalized_expectation_value_semantics_result_review_v0"
    )
    assert renormalized_review["result_token"] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_SUPPLIED_ONLY"
    )
    assert renormalized_review["review_result_token"] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
    )

    classical_source_prep = _workstream(
        payload, "qft_gr_classical_source_admissibility_semantics_preparation"
    )
    assert classical_source_prep["status"] == "paused"
    assert classical_source_prep["authorized_next_strict_target"] == (
        QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_RESULT_REVIEW_TARGET
    )
    assert classical_source_prep["consumed_target"] == (
        QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_TARGET
    )
    assert classical_source_prep["latest_surface"] == (
        "QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_v0"
    )
    assert (
        classical_source_prep["classical_source_admissibility_semantics_authorized"]
        == "supplied_only_retained"
    )
    assert classical_source_prep["result_review_status"] == (
        "prepared_for_live_result_review"
    )

    classical_source_review = _workstream(
        payload, "qft_gr_classical_source_admissibility_semantics_result_review"
    )
    assert classical_source_review["status"] == "paused"
    assert classical_source_review["authorized_next_strict_target"] == (
        QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_SEMANTICS_TARGET
    )
    assert classical_source_review["consumed_target"] == (
        QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_RESULT_REVIEW_TARGET
    )
    assert classical_source_review["latest_surface"] == (
        "qft_gr_classical_source_admissibility_semantics_result_review_v0"
    )
    assert classical_source_review["review_result_token"] == (
        "QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
    )

    covariant_prep = _workstream(
        payload, "qft_gr_covariant_conservation_obligation_semantics_preparation"
    )
    assert covariant_prep["status"] == "paused"
    assert covariant_prep["authorized_next_strict_target"] == (
        QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_RESULT_REVIEW_TARGET
    )
    assert covariant_prep["consumed_target"] == (
        QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_SEMANTICS_TARGET
    )
    assert covariant_prep["latest_surface"] == (
        "QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_SEMANTICS_v0"
    )
    assert covariant_prep["covariant_conservation_obligation_semantics_authorized"] == (
        "supplied_only_retained"
    )
    assert covariant_prep["conservation_witness_authorized"] == "no"
    assert covariant_prep["actual_covariant_conservation_authorized"] == "no"
    assert covariant_prep["result_review_status"] == (
        "prepared_for_live_result_review"
    )


def test_paused_lanes_do_not_advertise_active_continuation() -> None:
    payload = _registry()

    for lane in payload["current_target_state"]["paused_lanes"]:
        workstream = _workstream(payload, lane)
        assert workstream["status"] == "paused", lane

        continuation_values = [
            value
            for key, value in workstream.items()
            if "continuation" in key or key.endswith("_reopen") or key == "same_lane_continuation"
        ]
        assert "authorized" not in continuation_values, lane

    assert _workstream(payload, "qm_evolution_contract")["scalar_reopen"] == "not_authorized"
    assert _workstream(payload, "qm_evolution_contract")["qm_stat_reopen"] == "not_authorized"
    assert _workstream(payload, "qm_evolution_contract")["qft_gr_reopen"] == "not_authorized"
    assert _workstream(payload, "qm_evolution_contract")["sr_cosmo_reopen"] == "not_authorized"


def test_historical_post_sweep_queue_cannot_override_live_target() -> None:
    payload = _registry()
    queue_text = _read(POST_SWEEP_QUEUE_PATH)

    assert HISTORICAL_QUEUE_TOKEN in queue_text
    assert "live_next_target_source := False" in queue_text
    assert (
        _control(payload, "post_sweep_queue_discipline")["authority_status"]
        == HISTORICAL_QUEUE_TOKEN
    )
    assert _control(payload, "post_sweep_queue_discipline")["live_next_target_authority"] is False

    historical_targets = set(re.findall(r'target\s*:=\s*"([^"]+)"', queue_text))
    assert historical_targets
    assert LIVE_TARGET not in historical_targets
    assert PREVIOUS_TARGET not in historical_targets
    assert SOURCE_PROBABILITY_TARGET not in historical_targets
    assert PRIORITIZATION_TARGET not in historical_targets
    assert CITATION_USAGE_TARGET not in historical_targets
    assert EM_QFT_POST_BUDGET_TARGET not in historical_targets
    assert INTERFACE_TARGET not in historical_targets
    assert SHARED_DYNAMICS_TARGET not in historical_targets
    assert EXTRACTION_TARGET not in historical_targets
    assert QM_REVIEW_TARGET not in historical_targets


def test_forbidden_promotion_boundaries_remain_fail_closed() -> None:
    assert_forbidden_promotions_closed()
    payload = _registry()
    assertions = payload["non_promotion_assertions"]
    assert set(assertions) == FORBIDDEN_ASSERTIONS
    assert not any(assertions.values())

    state = payload["current_target_state"]
    assert set(state["forbidden_promotions"]) == {
        "phase2_authorization",
        "seam_closure",
        "empirical_claim",
        "master_action_promotion",
        "governance_manifest_enrollment",
    }

    protocol_text = _read(EM_QFT_PROTOCOL_ROW_PATH)
    shared_bridge_text = _read(EM_QFT_SHARED_DYNAMICS_BRIDGE_PATH)
    interface_bridge_text = _read(EM_QFT_INTERFACE_ALIGNMENT_BRIDGE_PATH)
    em_qft_review_text = _read(EM_QFT_POST_BUDGET_REVIEW_PATH)
    citation_usage_text = _read(MASTER_ACTION_CITATION_USAGE_PATH)
    citation_audit_text = _read(MASTER_ACTION_CITATION_AUDIT_PATH)
    dependency_graph_review_text = _read(MASTER_ACTION_DEPENDENCY_GRAPH_REVIEW_PATH)
    prioritization_review_text = _read(
        MASTER_ACTION_RETAINED_BLOCKER_PRIORITIZATION_REVIEW_PATH
    )
    protocol_row_text = _read(QM_STAT_TRANSPORT_SEMANTICS_PROTOCOL_ROW_PATH)
    readiness_review_text = _read(QM_STAT_TRANSPORT_SEMANTICS_READINESS_REVIEW_PATH)
    source_probability_text = _read(QM_STAT_SOURCE_PROBABILITY_EXTRACTION_PATH)
    source_probability_review_text = _read(QM_STAT_SOURCE_PROBABILITY_RESULT_REVIEW_PATH)
    post_qm_stat_prioritization_text = _read(
        MASTER_ACTION_POST_QMSTAT_PRIORITIZATION_REVIEW_PATH
    )
    qft_gr_protocol_row_text = _read(QFT_GR_SOURCE_MAP_SEMANTICS_PROTOCOL_ROW_PATH)
    qft_gr_readiness_review_text = _read(QFT_GR_SOURCE_MAP_SEMANTICS_READINESS_REVIEW_PATH)
    qft_gr_operator_domain_text = _read(QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_SEMANTICS_PATH)
    qft_gr_result_review_text = _read(
        QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_RESULT_REVIEW_PATH
    )
    full_pillar_target_map_text = _read(FULL_PILLAR_TARGET_MAP_REBASE_PATH)
    full_pillar_target_map_result_review_text = _read(
        FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_PATH
    )
    post_rebase_selection_text = _read(POST_REBASE_NEXT_BOUNDED_ATTACK_SELECTION_PATH)
    qft_gr_state_expectation_text = _read(
        QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_PATH
    )
    qft_gr_state_expectation_review_text = _read(
        QFT_GR_STATE_EXPECTATION_FUNCTIONAL_RESULT_REVIEW_PATH
    )
    qft_gr_renormalized_expectation_review_text = _read(
        QFT_GR_RENORMALIZED_EXPECTATION_VALUE_RESULT_REVIEW_PATH
    )
    qft_gr_classical_source_admissibility_text = _read(
        QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_PATH
    )
    qft_gr_classical_source_admissibility_review_text = _read(
        QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_RESULT_REVIEW_PATH
    )
    qft_gr_covariant_conservation_obligation_text = _read(
        QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_SEMANTICS_PATH
    )
    qft_gr_covariant_conservation_obligation_result_review_text = _read(
        QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_RESULT_REVIEW_PATH
    )
    qft_gr_bianchi_compatibility_obligation_text = _read(
        QFT_GR_BIANCHI_COMPATIBILITY_OBLIGATION_SEMANTICS_PATH
    )
    qft_gr_bianchi_compatibility_obligation_result_review_text = _read(
        QFT_GR_BIANCHI_COMPATIBILITY_OBLIGATION_RESULT_REVIEW_PATH
    )
    qft_gr_einstein_coupling_obligation_text = _read(
        QFT_GR_EINSTEIN_COUPLING_OBLIGATION_SEMANTICS_PATH
    )
    qft_gr_einstein_coupling_obligation_result_review_text = _read(
        QFT_GR_EINSTEIN_COUPLING_OBLIGATION_RESULT_REVIEW_PATH
    )
    qft_gr_weak_curvature_source_identification_obligation_text = _read(
        QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_SEMANTICS_PATH
    )
    qft_gr_weak_curvature_source_identification_obligation_result_review_text = _read(
        QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_OBLIGATION_RESULT_REVIEW_PATH
    )
    qft_gr_poisson_recovery_obligation_text = _read(
        QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_PATH
    )
    for theorem_name in [
        "em_qft_protocol_row_phase2_not_authorized_v0",
        "em_qft_protocol_row_seam_not_closed_v0",
        "em_qft_protocol_row_master_action_not_promoted_v0",
        "em_qft_protocol_row_no_empirical_claim_v0",
        "em_qft_protocol_row_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in protocol_text
    for theorem_name in [
        "em_qft_shared_dynamics_phase2_not_authorized_v0",
        "em_qft_shared_dynamics_no_seam_closure_v0",
        "em_qft_shared_dynamics_master_action_not_promoted_v0",
        "em_qft_shared_dynamics_no_empirical_claim_v0",
        "em_qft_shared_dynamics_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in shared_bridge_text
    for theorem_name in [
        "em_qft_interface_alignment_phase2_not_authorized_v0",
        "em_qft_interface_alignment_no_seam_closure_v0",
        "em_qft_interface_alignment_master_action_not_promoted_v0",
        "em_qft_interface_alignment_no_empirical_claim_v0",
        "em_qft_interface_alignment_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in interface_bridge_text
    for theorem_name in [
        "em_qft_post_budget_phase2_not_authorized_v0",
        "em_qft_post_budget_em_qft_seam_not_closed_v0",
        "em_qft_post_budget_master_action_not_promoted_v0",
        "em_qft_post_budget_no_empirical_claim_v0",
        "em_qft_post_budget_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in em_qft_review_text
    for theorem_name in [
        "master_action_citation_usage_no_seam_closure_v0",
        "master_action_citation_usage_phase2_not_authorized_v0",
        "master_action_citation_usage_master_action_not_promoted_v0",
        "master_action_citation_usage_no_empirical_claim_v0",
        "master_action_citation_usage_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in citation_usage_text
    for theorem_name in [
        "master_action_citation_language_audit_no_seam_closure_v0",
        "master_action_citation_language_audit_phase2_not_authorized_v0",
        "master_action_citation_language_audit_master_action_not_promoted_v0",
        "master_action_citation_language_audit_no_empirical_claim_v0",
        "master_action_citation_language_audit_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in citation_audit_text
    for theorem_name in [
        "master_action_dependency_graph_review_no_seam_closure_v0",
        "master_action_dependency_graph_review_phase2_not_authorized_v0",
        "master_action_dependency_graph_review_master_action_not_promoted_v0",
        "master_action_dependency_graph_review_no_empirical_claim_v0",
        "master_action_dependency_graph_review_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in dependency_graph_review_text
    for theorem_name in [
        "retained_blocker_prioritization_no_seam_closure_v0",
        "retained_blocker_prioritization_phase2_not_authorized_v0",
        "retained_blocker_prioritization_master_action_not_promoted_v0",
        "retained_blocker_prioritization_no_empirical_claim_v0",
        "retained_blocker_prioritization_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in prioritization_review_text
    for theorem_name in [
        "qm_stat_transport_semantics_protocol_row_no_seam_closure_v0",
        "qm_stat_transport_semantics_protocol_row_phase2_not_authorized_v0",
        "qm_stat_transport_semantics_protocol_row_master_action_not_promoted_v0",
        "qm_stat_transport_semantics_protocol_row_no_empirical_claim_v0",
        "qm_stat_transport_semantics_protocol_row_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in protocol_row_text
    for theorem_name in [
        "qm_stat_transport_semantics_readiness_review_no_seam_closure_v0",
        "qm_stat_transport_semantics_readiness_review_no_stat_mechanics_claim_v0",
        "qm_stat_transport_semantics_readiness_review_phase2_not_authorized_v0",
        "qm_stat_transport_semantics_readiness_review_master_action_not_promoted_v0",
        "qm_stat_transport_semantics_readiness_review_no_empirical_claim_v0",
        "qm_stat_transport_semantics_readiness_review_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in readiness_review_text
    for theorem_name in [
        "qm_stat_source_probability_extraction_no_seam_closure_v0",
        "qm_stat_source_probability_extraction_no_stat_mechanics_claim_v0",
        "qm_stat_source_probability_extraction_phase2_not_authorized_v0",
        "qm_stat_source_probability_extraction_master_action_not_promoted_v0",
        "qm_stat_source_probability_extraction_no_empirical_claim_v0",
        "qm_stat_source_probability_extraction_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in source_probability_text
    for theorem_name in [
        "qm_stat_source_probability_result_review_no_seam_closure_v0",
        "qm_stat_source_probability_result_review_no_stat_mechanics_claim_v0",
        "qm_stat_source_probability_result_review_phase2_not_authorized_v0",
        "qm_stat_source_probability_result_review_master_action_not_promoted_v0",
        "qm_stat_source_probability_result_review_no_empirical_claim_v0",
        "qm_stat_source_probability_result_review_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in source_probability_review_text
    for theorem_name in [
        "post_qm_stat_retained_blocker_prioritization_no_qft_gr_seam_closure_v0",
        "post_qm_stat_retained_blocker_prioritization_no_semiclassical_gravity_claim_v0",
        "post_qm_stat_retained_blocker_prioritization_no_einstein_equation_claim_v0",
        "post_qm_stat_retained_blocker_prioritization_phase2_not_authorized_v0",
        "post_qm_stat_retained_blocker_prioritization_master_action_not_promoted_v0",
        "post_qm_stat_retained_blocker_prioritization_no_empirical_claim_v0",
        "post_qm_stat_retained_blocker_prioritization_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in post_qm_stat_prioritization_text
    for theorem_name in [
        "qft_gr_source_map_semantics_protocol_row_no_seam_closure_v0",
        "qft_gr_source_map_semantics_protocol_row_no_semiclassical_gravity_claim_v0",
        "qft_gr_source_map_semantics_protocol_row_no_einstein_equation_claim_v0",
        "qft_gr_source_map_semantics_protocol_row_phase2_not_authorized_v0",
        "qft_gr_source_map_semantics_protocol_row_master_action_not_promoted_v0",
        "qft_gr_source_map_semantics_protocol_row_no_empirical_claim_v0",
        "qft_gr_source_map_semantics_protocol_row_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_protocol_row_text
    for theorem_name in [
        "qft_gr_source_map_semantics_readiness_review_no_seam_closure_v0",
        "qft_gr_source_map_semantics_readiness_review_no_semiclassical_gravity_claim_v0",
        "qft_gr_source_map_semantics_readiness_review_no_einstein_equation_claim_v0",
        "qft_gr_source_map_semantics_readiness_review_phase2_not_authorized_v0",
        "qft_gr_source_map_semantics_readiness_review_master_action_not_promoted_v0",
        "qft_gr_source_map_semantics_readiness_review_no_empirical_claim_v0",
        "qft_gr_source_map_semantics_readiness_review_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_readiness_review_text
    for theorem_name in [
        "qft_gr_stress_energy_operator_domain_no_seam_closure_v0",
        "qft_gr_stress_energy_operator_domain_no_semiclassical_gravity_claim_v0",
        "qft_gr_stress_energy_operator_domain_no_einstein_equation_claim_v0",
        "qft_gr_stress_energy_operator_domain_phase2_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_master_action_not_promoted_v0",
        "qft_gr_stress_energy_operator_domain_no_empirical_claim_v0",
        "qft_gr_stress_energy_operator_domain_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_operator_domain_text
    for theorem_name in [
        "qft_gr_stress_energy_operator_domain_result_review_no_seam_closure_v0",
        "qft_gr_stress_energy_operator_domain_result_review_no_semiclassical_gravity_claim_v0",
        "qft_gr_stress_energy_operator_domain_result_review_no_einstein_equation_claim_v0",
        "qft_gr_stress_energy_operator_domain_result_review_phase2_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_result_review_master_action_not_promoted_v0",
        "qft_gr_stress_energy_operator_domain_result_review_no_empirical_claim_v0",
        "qft_gr_stress_energy_operator_domain_result_review_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_result_review_text
    for theorem_name in [
        "full_pillar_target_map_rebase_phase2_not_authorized_v0",
        "full_pillar_target_map_rebase_no_seam_closure_claim_v0",
        "full_pillar_target_map_rebase_no_full_pillar_completion_claim_v0",
        "full_pillar_target_map_rebase_master_action_not_promoted_v0",
        "full_pillar_target_map_rebase_no_empirical_claim_v0",
    ]:
        assert theorem_name in full_pillar_target_map_text
    for theorem_name in [
        "full_pillar_target_map_rebase_result_review_no_unauthorized_claims_v0",
        "full_pillar_target_map_rebase_result_review_no_next_attack_selected_v0",
        "full_pillar_target_map_rebase_result_review_phase2_not_authorized_v0",
        "full_pillar_target_map_rebase_result_review_no_seam_closure_claim_v0",
        "full_pillar_target_map_rebase_result_review_no_full_pillar_completion_v0",
        "full_pillar_target_map_rebase_result_review_master_action_not_promoted_v0",
        "full_pillar_target_map_rebase_result_review_no_empirical_claim_v0",
    ]:
        assert theorem_name in full_pillar_target_map_result_review_text
    for theorem_name in [
        "post_rebase_next_bounded_attack_selection_does_not_execute_attack_v0",
        "post_rebase_next_bounded_attack_selection_no_full_pillar_completion_v0",
        "post_rebase_next_bounded_attack_selection_no_seam_closure_v0",
        "post_rebase_next_bounded_attack_selection_phase2_not_authorized_v0",
        "post_rebase_next_bounded_attack_selection_master_action_not_promoted_v0",
        "post_rebase_next_bounded_attack_selection_no_empirical_claim_v0",
    ]:
        assert theorem_name in post_rebase_selection_text
    for theorem_name in [
        "qft_gr_state_expectation_functional_semantics_renormalized_expectation_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_hadamard_state_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_self_adjointness_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_domain_density_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_weak_curvature_source_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_covariance_conservation_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_full_source_map_closure_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_no_seam_closure_v0",
        "qft_gr_state_expectation_functional_semantics_no_semiclassical_gravity_claim_v0",
        "qft_gr_state_expectation_functional_semantics_no_einstein_equation_claim_v0",
        "qft_gr_state_expectation_functional_semantics_phase2_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_master_action_not_promoted_v0",
        "qft_gr_state_expectation_functional_semantics_no_empirical_claim_v0",
        "qft_gr_state_expectation_functional_semantics_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_state_expectation_text
    for theorem_name in [
        "qft_gr_state_expectation_functional_result_review_source_map_package_only_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_renormalized_expectation_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_hadamard_state_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_self_adjointness_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_domain_density_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_weak_curvature_source_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_covariance_conservation_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_full_source_map_closure_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_no_seam_closure_v0",
        "qft_gr_state_expectation_functional_result_review_no_semiclassical_gravity_claim_v0",
        "qft_gr_state_expectation_functional_result_review_no_einstein_equation_claim_v0",
        "qft_gr_state_expectation_functional_result_review_phase2_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_master_action_not_promoted_v0",
        "qft_gr_state_expectation_functional_result_review_no_empirical_claim_v0",
        "qft_gr_state_expectation_functional_result_review_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_state_expectation_review_text
    for theorem_name in [
        "qft_gr_renorm_expectation_value_result_review_scheme_not_authorized_v0",
        "qft_gr_renorm_expectation_value_result_review_hadamard_not_authorized_v0",
        "qft_gr_renorm_expectation_value_result_review_finiteness_not_authorized_v0",
        "qft_gr_renorm_expectation_value_result_review_self_adjoint_not_authorized_v0",
        "qft_gr_renorm_expectation_value_result_review_domain_density_not_authorized_v0",
        "qft_gr_renorm_expectation_value_result_review_conservation_not_authorized_v0",
        "qft_gr_renorm_expectation_value_result_review_classical_source_not_authorized_v0",
        "qft_gr_renorm_expectation_value_result_review_weak_source_not_authorized_v0",
        "qft_gr_renorm_expectation_value_result_review_semiclassical_eq_not_authorized_v0",
        "qft_gr_renorm_expectation_value_result_review_source_map_not_authorized_v0",
        "qft_gr_renorm_expectation_value_result_review_no_seam_closure_v0",
        "qft_gr_renorm_expectation_value_result_review_no_semiclassical_claim_v0",
        "qft_gr_renorm_expectation_value_result_review_no_einstein_claim_v0",
        "qft_gr_renorm_expectation_value_result_review_phase2_not_authorized_v0",
        "qft_gr_renorm_expectation_value_result_review_master_action_not_promoted_v0",
        "qft_gr_renorm_expectation_value_result_review_no_empirical_claim_v0",
        "qft_gr_renorm_expectation_value_result_review_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_renormalized_expectation_review_text
    for theorem_name in [
        "qft_gr_classical_source_admissibility_semantics_scheme_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_finite_tensor_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_hadamard_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_self_adjoint_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_domain_density_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_conservation_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_bianchi_source_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_einstein_coupling_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_weak_source_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_poisson_limit_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_semiclassical_eq_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_source_map_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_no_seam_closure_v0",
        "qft_gr_classical_source_admissibility_semantics_no_semiclassical_gravity_claim_v0",
        "qft_gr_classical_source_admissibility_semantics_no_einstein_claim_v0",
        "qft_gr_classical_source_admissibility_semantics_phase2_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_master_action_not_promoted_v0",
        "qft_gr_classical_source_admissibility_semantics_no_empirical_claim_v0",
        "qft_gr_classical_source_admissibility_semantics_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_classical_source_admissibility_text

    for theorem_name in [
        "qft_gr_classical_source_admissibility_result_review_scheme_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_finiteness_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_hadamard_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_self_adjoint_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_domain_density_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_conservation_obligation_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_conservation_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_bianchi_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_einstein_coupling_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_weak_source_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_poisson_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_semiclassical_eq_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_source_map_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_no_seam_closure_v0",
        "qft_gr_classical_source_admissibility_result_review_no_semiclassical_claim_v0",
        "qft_gr_classical_source_admissibility_result_review_no_einstein_claim_v0",
        "qft_gr_classical_source_admissibility_result_review_phase2_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_master_action_not_promoted_v0",
        "qft_gr_classical_source_admissibility_result_review_no_empirical_claim_v0",
        "qft_gr_classical_source_admissibility_result_review_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_classical_source_admissibility_review_text

    for theorem_name in [
        "qft_gr_covariant_conservation_obligation_semantics_scheme_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_finite_tensor_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_hadamard_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_self_adjoint_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_domain_density_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_witness_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_actual_conservation_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_bianchi_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_einstein_coupling_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_weak_source_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_poisson_limit_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_semiclassical_eq_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_source_map_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_no_seam_closure_v0",
        "qft_gr_covariant_conservation_obligation_semantics_no_semiclassical_gravity_claim_v0",
        "qft_gr_covariant_conservation_obligation_semantics_no_einstein_claim_v0",
        "qft_gr_covariant_conservation_obligation_semantics_phase2_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_semantics_master_action_not_promoted_v0",
        "qft_gr_covariant_conservation_obligation_semantics_no_empirical_claim_v0",
        "qft_gr_covariant_conservation_obligation_semantics_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_covariant_conservation_obligation_text

    for theorem_name in [
        "qft_gr_covariant_conservation_obligation_result_review_scheme_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_finiteness_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_hadamard_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_self_adjoint_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_domain_density_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_witness_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_actual_conservation_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_bianchi_obligation_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_bianchi_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_einstein_coupling_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_weak_source_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_poisson_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_semiclassical_eq_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_source_map_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_no_seam_closure_v0",
        "qft_gr_covariant_conservation_obligation_result_review_no_semiclassical_claim_v0",
        "qft_gr_covariant_conservation_obligation_result_review_no_einstein_claim_v0",
        "qft_gr_covariant_conservation_obligation_result_review_phase2_not_authorized_v0",
        "qft_gr_covariant_conservation_obligation_result_review_master_action_not_promoted_v0",
        "qft_gr_covariant_conservation_obligation_result_review_no_empirical_claim_v0",
        "qft_gr_covariant_conservation_obligation_result_review_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_covariant_conservation_obligation_result_review_text

    for theorem_name in [
        "qft_gr_bianchi_compatibility_obligation_semantics_scheme_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_finite_tensor_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_hadamard_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_self_adjoint_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_domain_density_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_conservation_witness_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_actual_conservation_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_bianchi_witness_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_actual_bianchi_compatibility_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_einstein_coupling_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_weak_source_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_poisson_limit_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_semiclassical_eq_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_source_map_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_no_seam_closure_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_no_semiclassical_gravity_claim_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_no_einstein_claim_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_phase2_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_master_action_not_promoted_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_no_empirical_claim_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_bianchi_compatibility_obligation_text

    for theorem_name in [
        "qft_gr_bianchi_compatibility_obligation_result_review_scheme_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_finiteness_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_hadamard_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_self_adjoint_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_domain_density_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_conservation_witness_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_actual_conservation_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_bianchi_witness_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_actual_bianchi_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_einstein_obligation_not_constructed_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_einstein_coupling_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_weak_source_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_poisson_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_semiclassical_eq_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_source_map_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_no_seam_closure_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_no_semiclassical_claim_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_no_einstein_claim_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_phase2_not_authorized_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_master_action_not_promoted_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_no_empirical_claim_v0",
        "qft_gr_bianchi_compatibility_obligation_result_review_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_bianchi_compatibility_obligation_result_review_text

    for theorem_name in [
        "qft_gr_einstein_coupling_obligation_semantics_scheme_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_finite_tensor_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_hadamard_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_self_adjoint_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_domain_density_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_conservation_witness_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_actual_conservation_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_bianchi_witness_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_actual_bianchi_compatibility_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_einstein_witness_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_actual_coupling_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_weak_source_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_poisson_limit_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_semiclassical_eq_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_source_map_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_no_seam_closure_v0",
        "qft_gr_einstein_coupling_obligation_semantics_no_semiclassical_gravity_claim_v0",
        "qft_gr_einstein_coupling_obligation_semantics_no_einstein_claim_v0",
        "qft_gr_einstein_coupling_obligation_semantics_phase2_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_master_action_not_promoted_v0",
        "qft_gr_einstein_coupling_obligation_semantics_no_empirical_claim_v0",
        "qft_gr_einstein_coupling_obligation_semantics_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_einstein_coupling_obligation_text

    for theorem_name in [
        "qft_gr_einstein_coupling_obligation_result_review_same_lane_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_scheme_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_finiteness_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_hadamard_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_self_adjoint_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_domain_density_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_conservation_witness_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_actual_conservation_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_bianchi_witness_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_actual_bianchi_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_einstein_witness_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_actual_coupling_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_weak_source_obligation_not_constructed_v0",
        "qft_gr_einstein_coupling_obligation_result_review_weak_source_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_poisson_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_semiclassical_eq_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_source_map_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_no_seam_closure_v0",
        "qft_gr_einstein_coupling_obligation_result_review_no_semiclassical_claim_v0",
        "qft_gr_einstein_coupling_obligation_result_review_no_einstein_claim_v0",
        "qft_gr_einstein_coupling_obligation_result_review_phase2_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_result_review_master_action_not_promoted_v0",
        "qft_gr_einstein_coupling_obligation_result_review_no_empirical_claim_v0",
        "qft_gr_einstein_coupling_obligation_result_review_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_einstein_coupling_obligation_result_review_text

    for theorem_name in [
        "qft_gr_weak_curvature_source_identification_obligation_semantics_scheme_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_finite_tensor_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_hadamard_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_self_adjoint_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_domain_density_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_conservation_witness_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_actual_conservation_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_bianchi_witness_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_actual_bianchi_compatibility_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_einstein_witness_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_actual_coupling_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_source_witness_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_actual_source_identification_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_poisson_limit_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_newtonian_limit_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_semiclassical_eq_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_source_map_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_no_seam_closure_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_no_semiclassical_gravity_claim_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_no_einstein_claim_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_phase2_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_master_action_not_promoted_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_no_empirical_claim_v0",
        "qft_gr_weak_curvature_source_identification_obligation_semantics_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_weak_curvature_source_identification_obligation_text

    for theorem_name in [
        "qft_gr_weak_curvature_source_identification_obligation_result_review_same_lane_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_scheme_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_finiteness_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_hadamard_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_self_adjoint_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_domain_density_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_conservation_witness_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_actual_conservation_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_bianchi_witness_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_actual_bianchi_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_einstein_witness_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_actual_coupling_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_source_witness_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_actual_source_identification_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_poisson_obligation_not_constructed_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_poisson_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_newtonian_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_semiclassical_eq_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_source_map_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_no_seam_closure_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_no_semiclassical_claim_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_no_einstein_claim_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_phase2_not_authorized_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_master_action_not_promoted_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_no_empirical_claim_v0",
        "qft_gr_weak_curvature_source_identification_obligation_result_review_manifest_not_enrolled_v0",
    ]:
        assert (
            theorem_name
            in qft_gr_weak_curvature_source_identification_obligation_result_review_text
        )

    for theorem_name in [
        "qft_gr_poisson_recovery_obligation_semantics_scheme_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_finite_tensor_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_hadamard_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_self_adjoint_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_domain_density_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_conservation_witness_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_actual_conservation_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_bianchi_witness_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_actual_bianchi_compatibility_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_einstein_witness_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_actual_coupling_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_source_witness_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_actual_source_identification_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_poisson_witness_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_actual_poisson_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_newtonian_limit_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_weak_field_proof_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_semiclassical_eq_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_source_map_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_no_seam_closure_v0",
        "qft_gr_poisson_recovery_obligation_semantics_no_semiclassical_gravity_claim_v0",
        "qft_gr_poisson_recovery_obligation_semantics_no_einstein_claim_v0",
        "qft_gr_poisson_recovery_obligation_semantics_phase2_not_authorized_v0",
        "qft_gr_poisson_recovery_obligation_semantics_master_action_not_promoted_v0",
        "qft_gr_poisson_recovery_obligation_semantics_no_empirical_claim_v0",
        "qft_gr_poisson_recovery_obligation_semantics_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_poisson_recovery_obligation_text


def test_current_target_gate_is_not_governance_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled("test_current_target_freshness_gate.py")


