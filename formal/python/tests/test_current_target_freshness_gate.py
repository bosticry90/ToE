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
FNREP_SAMPLEREP32_DISCHARGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01SampleRep32Discharge.lean"
)
FNREP_SAMPLEREP32_DISCHARGE_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01SampleRep32DischargeResultReview.lean"
)
POST_FNREP_SAMPLEREP32_DISCHARGE_BOUNDED_ATTACK_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostFNRepSampleRep32DischargeBoundedAttackSelection.lean"
)
AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "AxiomLedgerAuditRefreshAfterSampleRep32.lean"
)
AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "AxiomLedgerAuditRefreshAfterSampleRep32ResultReview.lean"
)
POST_SAMPLEREP32_AXIOM_AUDIT_BOUNDED_ATTACK_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostSampleRep32AxiomAuditBoundedAttackSelection.lean"
)
FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_SAMPLEREP32_AXIOM_AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterSampleRep32AxiomAudit.lean"
)
QM_STAT_THEOREM_GAP_REENTRY_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTheoremGapReentry.lean"
)
QM_STAT_THEOREM_GAP_REENTRY_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTheoremGapReentryResultReview.lean"
)
QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTargetStatEntropySemanticsTheoremGap.lean"
)
QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTargetStatEntropySemanticsTheoremGapResultReview.lean"
)
POST_QM_STAT_ENTROPY_SEMANTICS_GAP_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostQMStatEntropySemanticsGapBoundedAttackSelection.lean"
)
FULL_PILLAR_AFTER_QM_STAT_ENTROPY_SEMANTICS_GAP_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGap.lean"
)
QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropySemanticsSupportingAssumptionMap.lean"
)
QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropySemanticsSupportingAssumptionMapResultReview.lean"
)
POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostQMStatEntropyAssumptionMapBoundedAttackSelection.lean"
)
QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropyAssumptionReductionCandidateSelection.lean"
)
QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropyLogDomainZeroHandlingReduction.lean"
)
QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropyLogDomainZeroHandlingReductionResultReview.lean"
)
POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostQMStatEntropyLogDomainReductionBoundedAttackSelection.lean"
)
V01_ALPHA_GOVERNANCE_MANIFEST_ENROLLMENT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "V01AlphaGovernanceManifestEnrollmentResultReview.lean"
)
V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche006ReleasePolicyAdjudicationPacket.lean"
)
V01_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004ReleaseReadinessAdjudicationPacket.lean"
)
V01_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004ReleaseReadinessAdjudicationPacketResultReview.lean"
)
V01_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004ReleaseReadinessAdjudication.lean"
)
V01_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004ReleaseReadinessAdjudicationResultReview.lean"
)
V01_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01ReleaseHoldPacketDueToRetainedTranche004SourceMapBlocker.lean"
)
V01_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01ReleaseHoldPacketDueToRetainedTranche004SourceMapBlockerResultReview.lean"
)
V01_POST_HOLD_ROUTING_PACKET_DUE_TO_RETAINED_TRANCHE_004_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01PostHoldRoutingPacketDueToRetainedTranche004.lean"
)
V01_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004FutureRemediationProgram.lean"
)
V01_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004FutureRemediationProgramResultReview.lean"
)
V01_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004BoundedSourceMapWitnessChainResearchPacket.lean"
)
V01_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004BoundedSourceMapWitnessChainResearchPacketResultReview.lean"
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
FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_STATUS_SURFACE_ENFORCEMENT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterStatusSurfaceEnforcement.lean"
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
FULL_PILLAR_AFTER_STATUS_SURFACE_ENFORCEMENT_RESULT_TOKEN = (
    "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_STATUS_SURFACE_ENFORCEMENT"
)
NEXT_PROOF_DEBT_ITEM_RESULT_TOKEN = "NEXT_PROOF_DEBT_LEDGER_DISCHARGE_ITEM_SELECTED"
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
NEXT_PROOF_DEBT_LEDGER_DISCHARGE_ITEM_TARGET = (
    "prepare_next_proof_debt_ledger_discharge_item"
)
FNREP_SAMPLEREP32_DISCHARGE_RESULT_REVIEW_TARGET = (
    "review_fnrep_nonalias_samplerep32_discharge_result"
)
FNREP_SAMPLEREP32_DISCHARGE_RESULT_TOKEN = (
    "FNREP_NONALIAS_SAMPLEREP32_DISCHARGED_LEAN_BACKED_CONSTRUCTOR"
)
FNREP_SAMPLEREP32_DISCHARGE_RESULT_REVIEW_TOKEN = (
    "FNREP_NONALIAS_SAMPLEREP32_DISCHARGE_RESULT_REVIEW_CONSUMED_LEAN_BACKED_CONSTRUCTOR"
)
POST_FNREP_SAMPLEREP32_DISCHARGE_BOUNDED_ATTACK_SELECTION_TARGET = (
    "select_next_post_fnrep_samplerep32_discharge_bounded_attack"
)
POST_FNREP_SAMPLEREP32_DISCHARGE_NEXT_ATTACK_SELECTED = (
    "POST_FNREP_SAMPLEREP32_DISCHARGE_NEXT_ATTACK_SELECTED"
)
AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_TOKEN = (
    "AXIOM_LEDGER_AUDIT_REFRESH_CONFIRMED_59_REAL_AXIOMS"
)
AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_TOKEN = (
    "AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_CONSUMED_59_REAL_AXIOMS_CONFIRMED"
)
POST_SAMPLEREP32_AXIOM_AUDIT_NEXT_ATTACK_SELECTED = (
    "POST_SAMPLEREP32_AXIOM_AUDIT_NEXT_ATTACK_SELECTED"
)
POST_SAMPLEREP32_AXIOM_AUDIT_BOUNDED_ATTACK_SELECTION_TARGET = (
    "select_next_post_samplerep32_axiom_audit_bounded_attack"
)
FULL_PILLAR_AFTER_SAMPLEREP32_AXIOM_AUDIT_RESULT_TOKEN = (
    "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_SAMPLEREP32_AXIOM_AUDIT"
)
QM_STAT_THEOREM_GAP_REENTRY_RESULT_TOKEN = "QM_STAT_THEOREM_GAP_REENTRY_PREPARED"
QM_STAT_THEOREM_GAP_REENTRY_TARGET = "prepare_qm_stat_theorem_gap_reentry"
QM_STAT_THEOREM_GAP_REENTRY_SELECTED_GAP = (
    "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0"
)
QM_STAT_THEOREM_GAP_REENTRY_SELECTED_OBLIGATION = (
    "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_OBLIGATION_v0"
)
QM_STAT_THEOREM_GAP_REENTRY_RESULT_REVIEW_TOKEN = (
    "QM_STAT_THEOREM_GAP_REENTRY_RESULT_REVIEW_CONSUMED"
)
QM_STAT_THEOREM_GAP_REENTRY_RESULT_REVIEW_TARGET = (
    "review_qm_stat_theorem_gap_reentry_result"
)
QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_ATTACK_TARGET = (
    "prepare_qm_stat_target_stat_entropy_semantics_theorem_gap_bounded_attack"
)
QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_RESULT_TOKEN = (
    "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_SUPPLIED_ONLY"
)
QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_RESULT_REVIEW_TARGET = (
    "review_qm_stat_target_stat_entropy_semantics_theorem_gap_result"
)
QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_RESULT_REVIEW_TOKEN = (
    "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
)
POST_QM_STAT_ENTROPY_SEMANTICS_GAP_BOUNDED_ATTACK_SELECTION_TARGET = (
    "select_next_post_qm_stat_entropy_semantics_gap_bounded_attack"
)
POST_QM_STAT_ENTROPY_SEMANTICS_GAP_NEXT_ATTACK_SELECTED = (
    "POST_QM_STAT_ENTROPY_SEMANTICS_GAP_NEXT_ATTACK_SELECTED"
)
FULL_PILLAR_AFTER_QM_STAT_ENTROPY_SEMANTICS_GAP_RESULT_TOKEN = (
    "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_QM_STAT_ENTROPY_SEMANTICS_GAP"
)
QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_TARGET = (
    "prepare_qm_stat_entropy_semantics_supporting_assumption_map"
)
QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_RESULT_REVIEW_TARGET = (
    "review_qm_stat_entropy_semantics_supporting_assumption_map_result"
)
QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_RESULT_TOKEN = (
    "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_PREPARED"
)
QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_RESULT_REVIEW_TOKEN = (
    "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_RESULT_REVIEW_CONSUMED"
)
POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_BOUNDED_ATTACK_SELECTION_TARGET = (
    "select_next_post_qm_stat_entropy_assumption_map_bounded_attack"
)
POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_NEXT_ATTACK_SELECTED = (
    "POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_NEXT_ATTACK_SELECTED"
)
QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_TARGET = (
    "prepare_qm_stat_entropy_assumption_reduction_candidate_selection"
)
QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_RESULT_TOKEN = (
    "QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTED"
)
SELECTED_QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_BOUNDED_ATTACK_TARGET = (
    "prepare_selected_qm_stat_entropy_assumption_reduction_bounded_attack"
)
SELECTED_QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE = (
    "log_domain_zero_handling_convention_required"
)
QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_TOKEN = (
    "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_ASSUMPTION_REDUCED_LEAN_BACKED"
)
QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_TARGET = (
    "review_qm_stat_entropy_log_domain_zero_handling_reduction_result"
)
QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_TOKEN = (
    "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_CONSUMED_LEAN_BACKED"
)
POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_BOUNDED_ATTACK_SELECTION_TARGET = (
    "select_next_post_qm_stat_entropy_log_domain_reduction_bounded_attack"
)
POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_NEXT_ATTACK_SELECTED = (
    "POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_NEXT_ATTACK_SELECTED"
)
POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_RECOMMENDED_NEXT_CANDIDATE = (
    "normalization_or_probability_mass_condition_required"
)
V01_ALPHA_GOVERNANCE_MANIFEST_ENROLLMENT_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_governance_manifest_enrollment_result"
)
POST_V01_ALPHA_MANIFEST_ENROLLMENT_BOUNDED_ATTACK_SELECTION_TARGET = (
    "select_next_post_v01_alpha_manifest_enrollment_bounded_attack"
)
V01_ALPHA_RELEASE_GATE_ENROLLED_TOKEN = "TOE_V01_ALPHA_RELEASE_GATE_ENROLLED"
V01_ALPHA_GOVERNANCE_MANIFEST_ENROLLMENT_RESULT_REVIEW_TOKEN = (
    "TOE_V01_ALPHA_GOVERNANCE_MANIFEST_ENROLLMENT_RESULT_REVIEW_CONSUMED"
)
V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_TARGET = (
    "prepare_v01_alpha_release_packet_gap_review"
)
V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_TARGET = (
    "prepare_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet"
)
V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result"
)
V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_RESULT_REVIEW_TOKEN = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_RESULT_REVIEW_ACCEPTS_EXACT_LEAN_DEPENDENCY_EVIDENCE_AND_AUTHORIZES_RELEASE_POLICY_ADJUDICATION_PACKET_PREPARATION_ONLY"
)
V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_TOKEN = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_PREPARED_WITH_NO_POLICY_DECISION_OR_RELEASE_PROMOTION"
)
V01_ALPHA_DEPENDENCY_REMEDIATION_SUMMARY_AFTER_TRANCHE_006_MOVEMENT_TOKEN = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_SUMMARY_PREPARED_AFTER_TRANCHE_006_MOVEMENT_WITH_TRANCHE_004_RETAINED_RELEASE_BLOCKER"
)
V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet"
)
V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_TOKEN = (
    "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_PREPARED_WITH_NO_RELEASE_ASSEMBLY_OR_READINESS_PROMOTION"
)
V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_TOKEN = (
    "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_ACCEPTS_RETAINED_BLOCKER_ADJUDICATION_QUESTION_AND_AUTHORIZES_ADJUDICATION_EXECUTION_ONLY"
)
V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_EXECUTION_TARGET = (
    "execute_v01_alpha_retained_tranche_004_release_readiness_adjudication"
)
V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_release_readiness_adjudication_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_TOKEN = (
    "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_EXECUTED_RELEASE_HOLD_DUE_TO_RETAINED_SOURCE_MAP_BLOCKER_WITH_NO_PROMOTION"
)
V01_ALPHA_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_TARGET = (
    "prepare_v01_alpha_release_hold_packet_due_to_retained_tranche_004_source_map_blocker"
)
V01_ALPHA_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_release_hold_packet_due_to_retained_tranche_004_source_map_blocker_result"
)
V01_ALPHA_POST_HOLD_ROUTING_PACKET_DUE_TO_RETAINED_TRANCHE_004_TARGET = (
    "prepare_v01_alpha_post_hold_routing_packet_due_to_retained_tranche_004"
)
V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_future_remediation_program"
)
V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_future_remediation_program_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_packet"
)
V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_packet_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_EXECUTION_TARGET = (
    "execute_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt"
)
V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_RESEARCH_CANDIDATE_EXECUTION_TARGET = (
    "execute_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_RESEARCH_CANDIDATE_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_PACKET_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_PACKET_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_EXECUTION_TARGET = (
    "execute_v01_alpha_retained_tranche_004_source_map_authorization_adjudication"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_PACKET_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_closure_adjudication_packet_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_PACKET_RESULT_REVIEW_TARGET = (
    "execute_v01_alpha_retained_tranche_004_source_map_closure_adjudication"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_closure_adjudication_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_source_map_closure_registration_packet"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_closure_registration_packet_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_EXECUTION_TARGET = (
    "execute_v01_alpha_retained_tranche_004_source_map_closure_registration"
)
V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_closure_registration_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_AFTER_SOURCE_MAP_CLOSURE_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure"
)
V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_SOURCE_MAP_CLOSURE_EXECUTION_TARGET = (
    "execute_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure"
)
V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result"
)
V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_MOVEMENT_TARGET = (
    "prepare_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement"
)
V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_MOVEMENT_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_result"
)
V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_CLOSEOUT_TARGET = (
    "prepare_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout"
)
V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_CLOSEOUT_PACKET_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_result"
)
V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_CLOSEOUT_EXECUTION_TARGET = (
    "execute_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout"
)
V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_CLOSEOUT_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_result"
)
V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_REVIEW_TOKEN = (
    "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_REVIEW_ACCEPTS_RELEASE_HOLD_AND_AUTHORIZES_RELEASE_HOLD_PACKET_PREPARATION_ONLY"
)
V01_ALPHA_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_TOKEN = (
    "V01_ALPHA_RELEASE_HOLD_PACKET_PREPARED_DUE_TO_RETAINED_TRANCHE_004_SOURCE_MAP_BLOCKER_WITH_NO_RELEASE_PROMOTION"
)
V01_ALPHA_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_RESULT_REVIEW_TOKEN = (
    "V01_ALPHA_RELEASE_HOLD_PACKET_RESULT_REVIEW_ACCEPTS_RELEASE_HOLD_DUE_TO_RETAINED_TRANCHE_004_SOURCE_MAP_BLOCKER_AND_AUTHORIZES_POST_HOLD_ROUTING_ONLY"
)
V01_ALPHA_POST_HOLD_ROUTING_PACKET_DUE_TO_RETAINED_TRANCHE_004_TOKEN = (
    "V01_ALPHA_POST_HOLD_ROUTING_PACKET_PREPARED_DUE_TO_RETAINED_TRANCHE_004_WITH_NO_RELEASE_PROMOTION"
)
V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_TOKEN = (
    "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_PREPARED_WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
)
V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_RESULT_REVIEW_TOKEN = (
    "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_RESULT_REVIEW_ACCEPTS_REMEDIATION_PROGRAM_AND_SELECTS_NEXT_BOUNDED_ROUTE_ONLY"
)
V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_TOKEN = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_PREPARED_WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
)
V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_RESULT_REVIEW_TOKEN = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_RESULT_REVIEW_ACCEPTS_RESEARCH_PACKET_AND_SELECTS_BOUNDED_NEXT_ACTION_ONLY"
)
AUDIT_REFRESH_TARGET = "prepare_axiom_ledger_audit_refresh"
AXIOM_AUDIT_RESULT_REVIEW_TARGET = (
    "review_axiom_ledger_audit_refresh_after_samplerep32_result"
)
ACTIVE_LANE = (
    "qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet"
)
PREVIOUS_TARGET = (
    "prepare_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet"
)
LIVE_TARGET = (
    "review_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result"
)
LIVE_TARGET_EVIDENCE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_CovariantConservationProofObjectObstructionRefinementPacket.lean"
)
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
    "post_status_surface_enforcement_bounded_attack_selection",
    "full_pillar_target_map_next_lane_selection_after_status_surface_enforcement",
    "next_proof_debt_ledger_discharge_item",
    "fnrep_nonalias_samplerep32_discharge",
    "post_fnrep_samplerep32_discharge_bounded_attack_selection",
    "axiom_ledger_audit_refresh_after_samplerep32",
    "axiom_ledger_audit_refresh_after_samplerep32_result_review",
    "post_samplerep32_axiom_audit_bounded_attack_selection",
    "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit",
    "qm_stat_theorem_gap_reentry",
    "qm_stat_theorem_gap_reentry_result_review",
    "post_qm_stat_entropy_semantics_gap_bounded_attack_selection",
    "v01_alpha_retained_tranche_004_future_remediation_program_result_review",
    "v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_packet",
    "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate",
    "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_result_review",
    "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate",
    "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_result_review",
    "v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet",
    "v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet_result_review",
    "v01_alpha_retained_tranche_004_source_map_authorization_adjudication",
    "v01_alpha_retained_tranche_004_source_map_authorization_adjudication_result_review",
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


def test_single_live_target_is_machine_pinned_after_samplerep32_audit_selector() -> None:
    assert_current_target_consistent()
    payload = _registry()
    state = payload["current_target_state"]

    assert state["schema_id"] == "CURRENT_TARGET_STATE_v0"
    assert state["previous_live_next_target"] == PREVIOUS_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == str(
        LIVE_TARGET_EVIDENCE_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert state["post_sweep_queue_authority_status"] == HISTORICAL_QUEUE_TOKEN
    paused_ids = {
        item["workstream_id"] for item in payload["workstreams"] if item["status"] == "paused"
    }
    assert set(state["paused_lanes"]) == paused_ids
    assert state["active_lane"] == ACTIVE_LANE

    previous_fnrep_workstream = _workstream(payload, "fnrep_nonalias_samplerep32_discharge")
    assert previous_fnrep_workstream["status"] == "paused"
    assert previous_fnrep_workstream["authorized_next_strict_target"] == (
        POST_FNREP_SAMPLEREP32_DISCHARGE_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert previous_fnrep_workstream["consumed_target"] == (
        FNREP_SAMPLEREP32_DISCHARGE_RESULT_REVIEW_TARGET
    )
    assert (
        previous_fnrep_workstream["latest_surface"]
        == "fnrep_nonalias_samplerep32_discharge_result_review_v0"
    )
    assert previous_fnrep_workstream["review_result_token"] == (
        FNREP_SAMPLEREP32_DISCHARGE_RESULT_REVIEW_TOKEN
    )
    assert previous_fnrep_workstream["selected_next_target"] == (
        POST_FNREP_SAMPLEREP32_DISCHARGE_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert previous_fnrep_workstream["real_axiom_count_after"] == 59
    assert previous_fnrep_workstream["real_axiom_file_count_after"] == 14
    assert previous_fnrep_workstream["debt_item_discharged"] == "yes"
    assert previous_fnrep_workstream["default_nonalias_remains_discharged"] == "yes"

    previous_selector_workstream = _workstream(
        payload, "post_fnrep_samplerep32_discharge_bounded_attack_selection"
    )
    assert previous_selector_workstream["status"] == "paused"
    assert previous_selector_workstream["authorized_next_strict_target"] == AUDIT_REFRESH_TARGET
    assert previous_selector_workstream["consumed_target"] == (
        POST_FNREP_SAMPLEREP32_DISCHARGE_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert (
        previous_selector_workstream["latest_surface"]
        == "post_fnrep_samplerep32_discharge_bounded_attack_selection_v0"
    )
    assert previous_selector_workstream["output_token"] == (
        POST_FNREP_SAMPLEREP32_DISCHARGE_NEXT_ATTACK_SELECTED
    )
    assert previous_selector_workstream["selected_next_target"] == AUDIT_REFRESH_TARGET
    assert previous_selector_workstream["real_axiom_count"] == 59
    assert previous_selector_workstream["real_axiom_file_count"] == 14

    previous_audit_workstream = _workstream(
        payload, "axiom_ledger_audit_refresh_after_samplerep32"
    )
    assert previous_audit_workstream["status"] == "paused"
    assert (
        previous_audit_workstream["authorized_next_strict_target"]
        == AXIOM_AUDIT_RESULT_REVIEW_TARGET
    )
    assert previous_audit_workstream["consumed_target"] == AUDIT_REFRESH_TARGET
    assert (
        previous_audit_workstream["latest_surface"]
        == "axiom_ledger_audit_refresh_after_samplerep32_v0"
    )
    assert (
        previous_audit_workstream["result_token"]
        == AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_TOKEN
    )
    assert previous_audit_workstream["selected_next_target"] == AXIOM_AUDIT_RESULT_REVIEW_TARGET
    assert previous_audit_workstream["real_axiom_count"] == 59
    assert previous_audit_workstream["real_axiom_file_count"] == 14

    previous_review_workstream = _workstream(
        payload, "axiom_ledger_audit_refresh_after_samplerep32_result_review"
    )
    assert previous_review_workstream["status"] == "paused"
    assert previous_review_workstream["authorized_next_strict_target"] == (
        POST_SAMPLEREP32_AXIOM_AUDIT_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert previous_review_workstream["consumed_target"] == AXIOM_AUDIT_RESULT_REVIEW_TARGET
    assert (
        previous_review_workstream["latest_surface"]
        == "axiom_ledger_audit_refresh_after_samplerep32_result_review_v0"
    )
    assert (
        previous_review_workstream["review_token"]
        == AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_TOKEN
    )
    assert previous_review_workstream["selected_next_target"] == (
        POST_SAMPLEREP32_AXIOM_AUDIT_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert previous_review_workstream["real_axiom_count"] == 59
    assert previous_review_workstream["real_axiom_file_count"] == 14

    post_audit_selector_workstream = _workstream(
        payload, "post_samplerep32_axiom_audit_bounded_attack_selection"
    )
    assert (
        post_audit_selector_workstream["workstream_id"]
        == "post_samplerep32_axiom_audit_bounded_attack_selection"
    )
    assert post_audit_selector_workstream["status"] == "paused"
    assert (
        post_audit_selector_workstream["authorized_next_strict_target"]
        == FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_TARGET
    )
    assert (
        post_audit_selector_workstream["consumed_target"]
        == POST_SAMPLEREP32_AXIOM_AUDIT_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert (
        post_audit_selector_workstream["latest_surface"]
        == "post_samplerep32_axiom_audit_bounded_attack_selection_v0"
    )
    assert (
        post_audit_selector_workstream["consumed_review_token"]
        == AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_TOKEN
    )
    assert (
        post_audit_selector_workstream["output_token"]
        == POST_SAMPLEREP32_AXIOM_AUDIT_NEXT_ATTACK_SELECTED
    )
    assert post_audit_selector_workstream["source_review_surface"] == str(
        AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_PATH.relative_to(
            REPO_ROOT
        )
    ).replace("\\", "/")
    assert post_audit_selector_workstream["source_review_report"] == (
        "formal/docs/release/AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_20260505_v0.json"
    )
    assert post_audit_selector_workstream["selection_report"] == (
        "formal/docs/release/POST_SAMPLEREP32_AXIOM_AUDIT_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
    )
    assert (
        post_audit_selector_workstream["selected_next_target"]
        == FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_TARGET
    )
    assert post_audit_selector_workstream["selected_target_count"] == 1
    assert post_audit_selector_workstream["selection_executes_target"] == "no"
    assert post_audit_selector_workstream["real_axiom_count"] == 59
    assert post_audit_selector_workstream["real_axiom_file_count"] == 14
    assert post_audit_selector_workstream["real_sorry_or_admit_count"] == 0
    assert (
        post_audit_selector_workstream["default_nonalias_absent_from_unresolved_axiom_debt"]
        == "yes"
    )
    assert (
        post_audit_selector_workstream["sample_rep32_absent_from_unresolved_axiom_debt"]
        == "yes"
    )
    assert post_audit_selector_workstream["default_nonalias_remains_discharged"] == "yes"
    assert post_audit_selector_workstream["sample_rep32_discharged"] == "yes"
    assert post_audit_selector_workstream["stale_active_60_axiom_posture"] == "absent"
    assert post_audit_selector_workstream["prior_60_axiom_audit_status"] == "historical_only"
    assert post_audit_selector_workstream["qft_gr_source_map_closure_authorized"] == "no"
    assert post_audit_selector_workstream["seam_closure_claim"] == "no"
    assert post_audit_selector_workstream["phase2_readiness_claim"] == "no"
    assert post_audit_selector_workstream["empirical_adequacy_claim"] == "no"
    assert post_audit_selector_workstream["canonical_toe_claim"] == "no"
    assert post_audit_selector_workstream["governance_manifest_enrollment_authorized"] == "no"
    assert post_audit_selector_workstream["master_action_promotion_authorized"] == "no"

    previous_full_pillar_workstream = _workstream(
        payload, "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit"
    )
    assert (
        previous_full_pillar_workstream["workstream_id"]
        == "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit"
    )
    assert previous_full_pillar_workstream["status"] == "paused"
    assert previous_full_pillar_workstream["authorized_next_strict_target"] == (
        QM_STAT_THEOREM_GAP_REENTRY_TARGET
    )
    assert previous_full_pillar_workstream["consumed_target"] == (
        FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_TARGET
    )
    assert (
        previous_full_pillar_workstream["latest_surface"]
        == "full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_v0"
    )
    assert (
        previous_full_pillar_workstream["consumed_selector_token"]
        == POST_SAMPLEREP32_AXIOM_AUDIT_NEXT_ATTACK_SELECTED
    )
    assert (
        previous_full_pillar_workstream["result_token"]
        == FULL_PILLAR_AFTER_SAMPLEREP32_AXIOM_AUDIT_RESULT_TOKEN
    )
    assert (
        previous_full_pillar_workstream["selected_lane"]
        == "QM_STAT_THEOREM_GAP_RE_ENTRY_LANE"
    )
    assert previous_full_pillar_workstream["selected_next_target"] == (
        QM_STAT_THEOREM_GAP_REENTRY_TARGET
    )
    assert previous_full_pillar_workstream["selection_executes_lane"] == "no"
    assert previous_full_pillar_workstream["proof_debt_discharge_item_selected"] == "no"
    assert previous_full_pillar_workstream["qm_stat_reentry_selected"] == "yes"
    assert previous_full_pillar_workstream["qm_stat_target_map_row"] == (
        "FULL_SEAM_QM_STAT_TARGET_MAP_v0"
    )
    assert previous_full_pillar_workstream["qm_stat_target_map_next_admissible_action"] == (
        "map_qm_stat_full_probability_entropy_transport_obligations"
    )
    assert previous_full_pillar_workstream["bounded_theorem_gap_item_ready"] == "yes"
    assert previous_full_pillar_workstream["real_axiom_count"] == 59
    assert previous_full_pillar_workstream["real_axiom_file_count"] == 14
    assert previous_full_pillar_workstream["real_sorry_or_admit_count"] == 0
    assert previous_full_pillar_workstream["qft_gr_source_map_closure_authorized"] == "no"
    assert previous_full_pillar_workstream["seam_closure_claim"] == "no"
    assert previous_full_pillar_workstream["phase2_readiness_claim"] == "no"
    assert previous_full_pillar_workstream["empirical_adequacy_claim"] == "no"
    assert previous_full_pillar_workstream["canonical_toe_claim"] == "no"
    assert previous_full_pillar_workstream["governance_manifest_enrollment_authorized"] == "no"
    assert previous_full_pillar_workstream["master_action_promotion_authorized"] == "no"

    previous_reentry_workstream = _workstream(payload, "qm_stat_theorem_gap_reentry")
    assert previous_reentry_workstream["status"] == "paused"
    assert previous_reentry_workstream["authorized_next_strict_target"] == (
        QM_STAT_THEOREM_GAP_REENTRY_RESULT_REVIEW_TARGET
    )
    assert previous_reentry_workstream["consumed_target"] == QM_STAT_THEOREM_GAP_REENTRY_TARGET
    assert previous_reentry_workstream["latest_surface"] == "qm_stat_theorem_gap_reentry_v0"
    assert previous_reentry_workstream["consumed_selector_token"] == (
        FULL_PILLAR_AFTER_SAMPLEREP32_AXIOM_AUDIT_RESULT_TOKEN
    )
    assert previous_reentry_workstream["result_token"] == QM_STAT_THEOREM_GAP_REENTRY_RESULT_TOKEN
    assert previous_reentry_workstream["selected_gap"] == QM_STAT_THEOREM_GAP_REENTRY_SELECTED_GAP
    assert (
        previous_reentry_workstream["selected_obligation"]
        == QM_STAT_THEOREM_GAP_REENTRY_SELECTED_OBLIGATION
    )
    assert previous_reentry_workstream["selected_next_target"] == (
        QM_STAT_THEOREM_GAP_REENTRY_RESULT_REVIEW_TARGET
    )
    assert previous_reentry_workstream["selection_executes_gap_discharge"] == "no"
    assert previous_reentry_workstream["target_entropy_gap_selected"] == "yes"
    assert previous_reentry_workstream["theorem_gap_discharged"] == "no"
    assert previous_reentry_workstream["broader_qm_stat_theorem_work_authorized"] == "no"
    assert previous_reentry_workstream["qft_gr_source_map_closure_authorized"] == "no"
    assert previous_reentry_workstream["seam_closure_claim"] == "no"
    assert previous_reentry_workstream["phase2_readiness_claim"] == "no"
    assert previous_reentry_workstream["empirical_adequacy_claim"] == "no"
    assert previous_reentry_workstream["canonical_toe_claim"] == "no"
    assert previous_reentry_workstream["governance_manifest_enrollment_authorized"] == "no"
    assert previous_reentry_workstream["master_action_promotion_authorized"] == "no"

    previous_reentry_review_workstream = _workstream(
        payload, "qm_stat_theorem_gap_reentry_result_review"
    )
    assert previous_reentry_review_workstream["status"] == "paused"
    assert previous_reentry_review_workstream["authorized_next_strict_target"] == (
        QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_ATTACK_TARGET
    )
    assert previous_reentry_review_workstream["consumed_target"] == (
        QM_STAT_THEOREM_GAP_REENTRY_RESULT_REVIEW_TARGET
    )
    assert (
        previous_reentry_review_workstream["latest_surface"]
        == "qm_stat_theorem_gap_reentry_result_review_v0"
    )
    assert previous_reentry_review_workstream["consumed_result_token"] == (
        QM_STAT_THEOREM_GAP_REENTRY_RESULT_TOKEN
    )
    assert (
        previous_reentry_review_workstream["review_token"]
        == QM_STAT_THEOREM_GAP_REENTRY_RESULT_REVIEW_TOKEN
    )
    assert previous_reentry_review_workstream["selected_gap"] == (
        QM_STAT_THEOREM_GAP_REENTRY_SELECTED_GAP
    )
    assert (
        previous_reentry_review_workstream["selected_obligation"]
        == QM_STAT_THEOREM_GAP_REENTRY_SELECTED_OBLIGATION
    )
    assert previous_reentry_review_workstream["selected_next_target"] == (
        QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_ATTACK_TARGET
    )
    assert previous_reentry_review_workstream["bounded_attack_preparation_authorized"] == "yes"
    assert previous_reentry_review_workstream["review_executes_bounded_attack"] == "no"
    assert previous_reentry_review_workstream["entropy_semantics_theorem_claimed"] == "no"
    assert previous_reentry_review_workstream["theorem_gap_discharged"] == "no"
    assert previous_reentry_review_workstream["qft_gr_source_map_closure_authorized"] == "no"
    assert previous_reentry_review_workstream["seam_closure_claim"] == "no"
    assert previous_reentry_review_workstream["phase2_readiness_claim"] == "no"
    assert previous_reentry_review_workstream["empirical_adequacy_claim"] == "no"
    assert previous_reentry_review_workstream["canonical_toe_claim"] == "no"
    assert previous_reentry_review_workstream["governance_manifest_enrollment_authorized"] == "no"
    assert previous_reentry_review_workstream["master_action_promotion_authorized"] == "no"

    previous_target_entropy_review_workstream = _workstream(
        payload, "qm_stat_target_stat_entropy_semantics_theorem_gap_result_review"
    )
    assert (
        previous_target_entropy_review_workstream["workstream_id"]
        == "qm_stat_target_stat_entropy_semantics_theorem_gap_result_review"
    )
    assert previous_target_entropy_review_workstream["status"] == "paused"
    assert previous_target_entropy_review_workstream["authorized_next_strict_target"] == (
        POST_QM_STAT_ENTROPY_SEMANTICS_GAP_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert previous_target_entropy_review_workstream["consumed_target"] == (
        QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_RESULT_REVIEW_TARGET
    )
    assert (
        previous_target_entropy_review_workstream["latest_surface"]
        == "qm_stat_target_stat_entropy_semantics_theorem_gap_result_review_v0"
    )
    assert previous_target_entropy_review_workstream["consumed_result_token"] == (
        QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_RESULT_TOKEN
    )
    assert previous_target_entropy_review_workstream["review_token"] == (
        QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_RESULT_REVIEW_TOKEN
    )
    assert previous_target_entropy_review_workstream["selected_gap"] == (
        QM_STAT_THEOREM_GAP_REENTRY_SELECTED_GAP
    )
    assert (
        previous_target_entropy_review_workstream["selected_obligation"]
        == QM_STAT_THEOREM_GAP_REENTRY_SELECTED_OBLIGATION
    )
    assert previous_target_entropy_review_workstream["selected_next_target"] == (
        POST_QM_STAT_ENTROPY_SEMANTICS_GAP_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert (
        previous_target_entropy_review_workstream[
            "target_stat_entropy_semantics_lean_backed"
        ]
        == "no"
    )
    assert (
        previous_target_entropy_review_workstream[
            "target_stat_entropy_semantics_supplied_only"
        ]
        == "yes"
    )
    assert previous_target_entropy_review_workstream["theorem_gap_discharged"] == "no"
    assert (
        previous_target_entropy_review_workstream[
            "qft_gr_source_map_closure_authorized"
        ]
        == "no"
    )
    assert previous_target_entropy_review_workstream["seam_closure_claim"] == "no"
    assert previous_target_entropy_review_workstream["phase2_readiness_claim"] == "no"
    assert previous_target_entropy_review_workstream["empirical_adequacy_claim"] == "no"
    assert previous_target_entropy_review_workstream["canonical_toe_claim"] == "no"
    assert (
        previous_target_entropy_review_workstream[
            "governance_manifest_enrollment_authorized"
        ]
        == "no"
    )
    assert (
        previous_target_entropy_review_workstream["master_action_promotion_authorized"]
        == "no"
    )

    previous_post_qm_selector_workstream = _workstream(
        payload, "post_qm_stat_entropy_semantics_gap_bounded_attack_selection"
    )
    assert (
        previous_post_qm_selector_workstream["workstream_id"]
        == "post_qm_stat_entropy_semantics_gap_bounded_attack_selection"
    )
    assert previous_post_qm_selector_workstream["status"] == "paused"
    assert previous_post_qm_selector_workstream["authorized_next_strict_target"] == (
        FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_TARGET
    )
    assert previous_post_qm_selector_workstream["consumed_target"] == (
        POST_QM_STAT_ENTROPY_SEMANTICS_GAP_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert (
        previous_post_qm_selector_workstream["latest_surface"]
        == "post_qm_stat_entropy_semantics_gap_bounded_attack_selection_v0"
    )
    assert previous_post_qm_selector_workstream["authorization_evidence"] == str(
        POST_QM_STAT_ENTROPY_SEMANTICS_GAP_SELECTOR_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert previous_post_qm_selector_workstream["consumed_result_token"] == (
        QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_RESULT_TOKEN
    )
    assert previous_post_qm_selector_workstream["consumed_review_token"] == (
        QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_RESULT_REVIEW_TOKEN
    )
    assert (
        previous_post_qm_selector_workstream["selected_gap"]
        == QM_STAT_THEOREM_GAP_REENTRY_SELECTED_GAP
    )
    assert (
        previous_post_qm_selector_workstream["output_token"]
        == POST_QM_STAT_ENTROPY_SEMANTICS_GAP_NEXT_ATTACK_SELECTED
    )
    assert previous_post_qm_selector_workstream["selected_next_target"] == (
        FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_TARGET
    )
    assert previous_post_qm_selector_workstream["selected_decision"] == (
        FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_TARGET
    )
    assert previous_post_qm_selector_workstream["selection_count"] == 1
    assert previous_post_qm_selector_workstream["candidate_target_count"] == 2
    assert previous_post_qm_selector_workstream["selection_executes_target"] == "no"
    assert previous_post_qm_selector_workstream["target_stat_entropy_semantics_lean_backed"] == "no"
    assert previous_post_qm_selector_workstream["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert previous_post_qm_selector_workstream["theorem_gap_discharged"] == "no"
    assert previous_post_qm_selector_workstream["qft_gr_source_map_closure_authorized"] == "no"
    assert previous_post_qm_selector_workstream["seam_closure_claim"] == "no"
    assert previous_post_qm_selector_workstream["phase2_readiness_claim"] == "no"
    assert previous_post_qm_selector_workstream["empirical_adequacy_claim"] == "no"
    assert previous_post_qm_selector_workstream["canonical_toe_claim"] == "no"
    assert (
        previous_post_qm_selector_workstream["governance_manifest_enrollment_authorized"]
        == "no"
    )
    assert previous_post_qm_selector_workstream["master_action_promotion_authorized"] == "no"

    previous_result_review_workstream = _workstream(
        payload, "qm_stat_entropy_semantics_supporting_assumption_map_result_review"
    )
    assert previous_result_review_workstream["status"] == "paused"
    assert previous_result_review_workstream["authorized_next_strict_target"] == (
        POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert previous_result_review_workstream["consumed_target"] == (
        QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_RESULT_REVIEW_TARGET
    )
    assert (
        previous_result_review_workstream["latest_surface"]
        == "qm_stat_entropy_semantics_supporting_assumption_map_result_review_v0"
    )
    assert previous_result_review_workstream["review_token"] == (
        QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_RESULT_REVIEW_TOKEN
    )
    assert previous_result_review_workstream["selected_next_target"] == (
        POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert previous_result_review_workstream["dependency_map_only"] == "yes"
    assert previous_result_review_workstream["assumption_class_count"] == 8
    assert previous_result_review_workstream["target_stat_entropy_semantics_lean_backed"] == "no"
    assert previous_result_review_workstream["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert previous_result_review_workstream["theorem_gap_discharged"] == "no"

    previous_post_selector_workstream = _workstream(
        payload, "post_qm_stat_entropy_assumption_map_bounded_attack_selection"
    )
    assert previous_post_selector_workstream["status"] == "paused"
    assert previous_post_selector_workstream["authorized_next_strict_target"] == (
        QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_TARGET
    )
    assert previous_post_selector_workstream["consumed_target"] == (
        POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert (
        previous_post_selector_workstream["latest_surface"]
        == "post_qm_stat_entropy_assumption_map_bounded_attack_selection_v0"
    )
    assert previous_post_selector_workstream["output_token"] == (
        POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_NEXT_ATTACK_SELECTED
    )
    assert previous_post_selector_workstream["selected_next_target"] == (
        QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_TARGET
    )
    assert previous_post_selector_workstream["selection_count"] == 1
    assert previous_post_selector_workstream["candidate_target_count"] == 2
    assert previous_post_selector_workstream["selection_executes_target"] == "no"
    assert previous_post_selector_workstream["dependency_map_only"] == "yes"
    assert previous_post_selector_workstream["assumption_class_count"] == 8
    assert previous_post_selector_workstream["theorem_gap_discharged"] == "no"

    previous_candidate_workstream = _workstream(
        payload, "qm_stat_entropy_assumption_reduction_candidate_selection"
    )
    assert previous_candidate_workstream["status"] == "paused"
    assert previous_candidate_workstream["authorized_next_strict_target"] == (
        SELECTED_QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_BOUNDED_ATTACK_TARGET
    )
    assert previous_candidate_workstream["consumed_target"] == (
        QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_TARGET
    )
    assert (
        previous_candidate_workstream["latest_surface"]
        == "qm_stat_entropy_assumption_reduction_candidate_selection_v0"
    )
    assert previous_candidate_workstream["authorization_evidence"] == str(
        QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_PATH.relative_to(
            REPO_ROOT
        )
    ).replace("\\", "/")
    assert previous_candidate_workstream["consumed_selector_token"] == (
        POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_NEXT_ATTACK_SELECTED
    )
    assert previous_candidate_workstream["result_token"] == (
        QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_RESULT_TOKEN
    )
    assert previous_candidate_workstream["selected_gap"] == (
        QM_STAT_THEOREM_GAP_REENTRY_SELECTED_GAP
    )
    assert previous_candidate_workstream["selected_next_target"] == (
        SELECTED_QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_BOUNDED_ATTACK_TARGET
    )
    assert previous_candidate_workstream["selected_assumption_class_id"] == (
        SELECTED_QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE
    )
    assert previous_candidate_workstream["selection_count"] == 1
    assert previous_candidate_workstream["assumption_class_count"] == 8
    assert previous_candidate_workstream["selection_criteria_count"] == 5
    assert previous_candidate_workstream["reduction_executed"] == "no"
    assert previous_candidate_workstream["target_stat_entropy_semantics_lean_backed"] == "no"
    assert previous_candidate_workstream["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert previous_candidate_workstream["theorem_gap_discharged"] == "no"
    assert previous_candidate_workstream["assumption_discharge_claim"] == "no"

    previous_reduction_workstream = _workstream(
        payload, "qm_stat_entropy_log_domain_zero_handling_reduction"
    )
    assert previous_reduction_workstream["status"] == "paused"
    assert previous_reduction_workstream["authorized_next_strict_target"] == (
        QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_TARGET
    )
    assert previous_reduction_workstream["consumed_target"] == (
        SELECTED_QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_BOUNDED_ATTACK_TARGET
    )
    assert (
        previous_reduction_workstream["latest_surface"]
        == "qm_stat_entropy_log_domain_zero_handling_reduction_v0"
    )
    assert previous_reduction_workstream["authorization_evidence"] == str(
        QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert previous_reduction_workstream["consumed_candidate_token"] == (
        QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_RESULT_TOKEN
    )
    assert previous_reduction_workstream["result_token"] == (
        QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_TOKEN
    )
    assert previous_reduction_workstream["selected_next_target"] == (
        QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_TARGET
    )
    assert previous_reduction_workstream["addressed_assumption_class_id"] == (
        SELECTED_QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE
    )
    assert previous_reduction_workstream["addressed_assumption_count"] == 1
    assert previous_reduction_workstream["source_assumption_class_count"] == 8
    assert previous_reduction_workstream["assumption_authority_after"] == (
        "Lean-backed local convention"
    )
    assert previous_reduction_workstream["zero_probability_uses_zero_contribution"] == "yes"
    assert previous_reduction_workstream["only_selected_assumption_addressed"] == "yes"
    assert previous_reduction_workstream["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert previous_reduction_workstream["entropy_semantics_theorem_discharged"] == "no"

    previous_log_domain_review_workstream = _workstream(
        payload, "qm_stat_entropy_log_domain_zero_handling_reduction_result_review"
    )
    assert previous_log_domain_review_workstream["status"] == "paused"
    assert previous_log_domain_review_workstream["authorized_next_strict_target"] == (
        POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert previous_log_domain_review_workstream["consumed_target"] == (
        QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_TARGET
    )
    assert (
        previous_log_domain_review_workstream["latest_surface"]
        == "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_v0"
    )
    assert previous_log_domain_review_workstream["authorization_evidence"] == str(
        QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_PATH.relative_to(
            REPO_ROOT
        )
    ).replace("\\", "/")
    assert previous_log_domain_review_workstream["consumed_reduction_token"] == (
        QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_TOKEN
    )
    assert previous_log_domain_review_workstream["review_token"] == (
        QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_TOKEN
    )
    assert previous_log_domain_review_workstream["selected_next_target"] == (
        POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert previous_log_domain_review_workstream["reduced_assumption_class_id"] == (
        SELECTED_QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE
    )
    assert previous_log_domain_review_workstream["reduced_assumption_authority"] == (
        "Lean-backed local convention"
    )
    assert previous_log_domain_review_workstream["local_convention_reduction_only"] == "yes"
    assert previous_log_domain_review_workstream["remaining_assumption_class_count"] == 7
    assert (
        previous_log_domain_review_workstream["remaining_supporting_assumptions_active"]
        == "yes"
    )
    assert previous_log_domain_review_workstream[
        "target_stat_entropy_semantics_supplied_only"
    ] == "yes"
    assert previous_log_domain_review_workstream[
        "entropy_semantics_theorem_discharged"
    ] == "no"

    previous_log_domain_selector_workstream = _workstream(
        payload, "post_qm_stat_entropy_log_domain_reduction_bounded_attack_selection"
    )
    assert (
        previous_log_domain_selector_workstream["workstream_id"]
        == "post_qm_stat_entropy_log_domain_reduction_bounded_attack_selection"
    )
    assert previous_log_domain_selector_workstream["status"] == "paused"
    assert previous_log_domain_selector_workstream["authorized_next_strict_target"] == (
        QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_TARGET
    )
    assert previous_log_domain_selector_workstream["consumed_target"] == (
        POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_BOUNDED_ATTACK_SELECTION_TARGET
    )
    assert (
        previous_log_domain_selector_workstream["latest_surface"]
        == "post_qm_stat_entropy_log_domain_reduction_bounded_attack_selection_v0"
    )
    assert previous_log_domain_selector_workstream["authorization_evidence"] == str(
        POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_SELECTOR_PATH.relative_to(
            REPO_ROOT
        )
    ).replace("\\", "/")
    assert previous_log_domain_selector_workstream["consumed_review_token"] == (
        QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_TOKEN
    )
    assert previous_log_domain_selector_workstream["output_token"] == (
        POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_NEXT_ATTACK_SELECTED
    )
    assert previous_log_domain_selector_workstream["selected_next_target"] == (
        QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_TARGET
    )
    assert previous_log_domain_selector_workstream["selected_decision"] == (
        QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_TARGET
    )
    assert previous_log_domain_selector_workstream["recommended_next_candidate"] == (
        POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_RECOMMENDED_NEXT_CANDIDATE
    )
    assert previous_log_domain_selector_workstream["selection_count"] == 1
    assert previous_log_domain_selector_workstream["candidate_target_count"] == 2
    assert previous_log_domain_selector_workstream["selection_executes_target"] == "no"
    assert (
        previous_log_domain_selector_workstream["local_convention_reduction_only"]
        == "yes"
    )
    assert previous_log_domain_selector_workstream["remaining_assumption_class_count"] == 7
    assert (
        previous_log_domain_selector_workstream["remaining_supporting_assumptions_active"]
        == "yes"
    )
    assert (
        previous_log_domain_selector_workstream["target_stat_entropy_semantics_lean_backed"]
        == "no"
    )
    assert (
        previous_log_domain_selector_workstream["target_stat_entropy_semantics_supplied_only"]
        == "yes"
    )
    assert (
        previous_log_domain_selector_workstream["entropy_semantics_theorem_discharged"]
        == "no"
    )
    assert previous_log_domain_selector_workstream["assumption_discharge_claim"] == "no"
    assert (
        previous_log_domain_selector_workstream["qft_gr_source_map_closure_authorized"]
        == "no"
    )
    assert previous_log_domain_selector_workstream["seam_closure_claim"] == "no"
    assert previous_log_domain_selector_workstream["phase2_readiness_claim"] == "no"
    assert previous_log_domain_selector_workstream["empirical_adequacy_claim"] == "no"
    assert previous_log_domain_selector_workstream["canonical_toe_claim"] == "no"
    assert (
        previous_log_domain_selector_workstream[
            "governance_manifest_enrollment_authorized"
        ]
        == "no"
    )
    assert (
        previous_log_domain_selector_workstream["master_action_promotion_authorized"]
        == "no"
    )

    current_active_workstream = active_workstream(payload)
    assert current_active_workstream["workstream_id"] == ACTIVE_LANE
    assert current_active_workstream["authorized_next_strict_target"] == LIVE_TARGET
    assert current_active_workstream["consumed_target"] == PREVIOUS_TARGET
    assert (
        current_active_workstream["latest_surface"]
        == "qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_v0"
    )
    assert current_active_workstream["authorization_evidence"] == str(
        LIVE_TARGET_EVIDENCE_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert current_active_workstream["construction_packet_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapWitnessChainConstructionPacketFromResearchCandidate.lean"
    )
    assert current_active_workstream["construction_packet_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_20260523_v0.json"
    )
    assert current_active_workstream["result_review_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01CriticizabilityReadinessAdjudicationResultReview.lean"
    )
    assert current_active_workstream["result_review_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_RESULT_REVIEW_20260525_v0.json"
    )
    assert current_active_workstream["construction_execution_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapWitnessChainConstructionFromResearchCandidate.lean"
    )
    assert current_active_workstream["construction_execution_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_RESEARCH_CANDIDATE_20260523_v0.json"
    )
    assert current_active_workstream["construction_result_review_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapWitnessChainConstructionResultReview.lean"
    )
    assert current_active_workstream["construction_result_review_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_RESULT_REVIEW_20260523_v0.json"
    )
    assert current_active_workstream["consumed_construction_execution_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapWitnessChainConstructionFromResearchCandidate.lean"
    )
    assert current_active_workstream["consumed_construction_execution_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_RESEARCH_CANDIDATE_20260523_v0.json"
    )
    assert current_active_workstream["source_map_authorization_adjudication_packet_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapAuthorizationAdjudicationPacket.lean"
    )
    assert current_active_workstream["source_map_authorization_adjudication_packet_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_PACKET_20260523_v0.json"
    )
    assert current_active_workstream[
        "source_map_authorization_adjudication_packet_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapAuthorizationAdjudicationPacketResultReview.lean"
    )
    assert current_active_workstream[
        "source_map_authorization_adjudication_packet_result_review_report"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_PACKET_RESULT_REVIEW_20260523_v0.json"
    )
    assert current_active_workstream["source_map_authorization_adjudication_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapAuthorizationAdjudication.lean"
    )
    assert current_active_workstream["source_map_authorization_adjudication_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_20260523_v0.json"
    )
    assert current_active_workstream[
        "source_map_authorization_adjudication_execution_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapAuthorizationAdjudication.lean"
    )
    assert current_active_workstream[
        "source_map_authorization_adjudication_execution_report"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_20260523_v0.json"
    )
    assert current_active_workstream[
        "source_map_authorization_adjudication_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapAuthorizationAdjudicationResultReview.lean"
    )
    assert current_active_workstream[
        "source_map_authorization_adjudication_result_review_report"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_RESULT_REVIEW_20260523_v0.json"
    )
    assert current_active_workstream["source_map_closure_adjudication_packet_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapClosureAdjudicationPacket.lean"
    )
    assert current_active_workstream["source_map_closure_adjudication_packet_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_PACKET_20260523_v0.json"
    )
    assert current_active_workstream[
        "source_map_closure_adjudication_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapClosureAdjudicationResultReview.lean"
    )
    assert current_active_workstream[
        "source_map_closure_adjudication_result_review_report"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_RESULT_REVIEW_20260523_v0.json"
    )
    assert current_active_workstream[
        "source_map_closure_registration_packet_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapClosureRegistrationPacket.lean"
    )
    assert current_active_workstream[
        "source_map_closure_registration_packet_report"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_20260523_v0.json"
    )
    assert current_active_workstream[
        "source_map_closure_registration_packet_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapClosureRegistrationPacketResultReview.lean"
    )
    assert current_active_workstream[
        "source_map_closure_registration_packet_result_review_report"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_RESULT_REVIEW_20260523_v0.json"
    )
    assert current_active_workstream["source_map_closure_registration_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapClosureRegistration.lean"
    )
    assert current_active_workstream["source_map_closure_registration_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_20260523_v0.json"
    )
    assert current_active_workstream[
        "consumed_source_map_closure_registration_packet_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapClosureRegistrationPacket.lean"
    )
    assert current_active_workstream[
        "consumed_source_map_closure_registration_packet_report"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_20260523_v0.json"
    )
    assert current_active_workstream[
        "consumed_source_map_closure_adjudication_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapClosureAdjudicationResultReview.lean"
    )
    assert current_active_workstream[
        "consumed_source_map_closure_adjudication_result_review_report"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_RESULT_REVIEW_20260523_v0.json"
    )
    assert current_active_workstream[
        "consumed_source_map_authorization_adjudication_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapAuthorizationAdjudicationResultReview.lean"
    )
    assert current_active_workstream[
        "consumed_source_map_authorization_adjudication_result_review_report"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_RESULT_REVIEW_20260523_v0.json"
    )
    assert current_active_workstream[
        "consumed_source_map_authorization_adjudication_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapAuthorizationAdjudication.lean"
    )
    assert current_active_workstream[
        "consumed_source_map_authorization_adjudication_report"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_20260523_v0.json"
    )
    assert current_active_workstream[
        "consumed_source_map_authorization_adjudication_packet_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapAuthorizationAdjudicationPacketResultReview.lean"
    )
    assert current_active_workstream[
        "consumed_source_map_authorization_adjudication_packet_result_review_report"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_PACKET_RESULT_REVIEW_20260523_v0.json"
    )
    assert current_active_workstream[
        "consumed_source_map_authorization_adjudication_packet_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapAuthorizationAdjudicationPacket.lean"
    )
    assert current_active_workstream[
        "consumed_source_map_authorization_adjudication_packet_report"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_PACKET_20260523_v0.json"
    )
    assert current_active_workstream["consumed_construction_result_review_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapWitnessChainConstructionResultReview.lean"
    )
    assert current_active_workstream["consumed_construction_result_review_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_RESULT_REVIEW_20260523_v0.json"
    )
    assert current_active_workstream[
        "consumed_construction_packet_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapWitnessChainConstructionPacketFromResearchCandidateResultReview.lean"
    )
    assert current_active_workstream["consumed_construction_packet_result_review_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_RESULT_REVIEW_20260523_v0.json"
    )
    assert current_active_workstream["consumed_result_review_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004BoundedSourceMapWitnessChainResearchAttemptResultReview.lean"
    )
    assert current_active_workstream["consumed_result_review_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_RESULT_REVIEW_20260523_v0.json"
    )
    assert current_active_workstream["research_attempt_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_20260523_v0.json"
    )
    assert current_active_workstream["research_packet_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_20260522_v0.json"
    )
    assert current_active_workstream["future_remediation_program_result_review_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_RESULT_REVIEW_20260522_v0.json"
    )
    assert current_active_workstream["future_remediation_program_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_20260522_v0.json"
    )
    assert current_active_workstream["post_hold_routing_packet_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_POST_HOLD_ROUTING_PACKET_DUE_TO_RETAINED_TRANCHE_004_20260522_v0.json"
    )
    assert current_active_workstream["release_hold_packet_result_review_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_SOURCE_MAP_BLOCKER_RESULT_REVIEW_20260522_v0.json"
    )
    assert current_active_workstream["hold_packet_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_SOURCE_MAP_BLOCKER_20260522_v0.json"
    )
    assert current_active_workstream["adjudication_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_20260522_v0.json"
    )
    assert current_active_workstream["consumed_result_review_token"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_RESULT_REVIEW_ACCEPTS_PARTIAL_CANDIDATE_AND_AUTHORIZES_CONSTRUCTION_PACKET_PREPARATION_ONLY"
    )
    assert current_active_workstream["output_token"] == (
        "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_PACKET_PREPARED_WITH_NO_QFT_GR_SEAM_CLOSURE_OR_EMPIRICAL_VALIDATION"
    )
    assert current_active_workstream["source_map_closure_registration_packet_token"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_PREPARED_WITH_NO_SEAM_CLOSURE_OR_RELEASE_PROMOTION"
    )
    assert (
        current_active_workstream["source_map_closure_registration_packet_classification"]
        == "source_map_closure_registration_packet_prepared_no_seam_closure_or_release_promotion"
    )
    assert current_active_workstream[
        "source_map_closure_registration_packet_result_review_token"
    ] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_CLOSURE_REGISTRATION_EXECUTION_ONLY"
    )
    assert (
        current_active_workstream[
            "source_map_closure_registration_packet_result_review_classification"
        ]
        == "source_map_closure_registration_packet_accepted_closure_registration_execution_authorized_only"
    )
    assert current_active_workstream[
        "consumed_source_map_closure_registration_packet_result_review_token"
    ] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_CLOSURE_REGISTRATION_EXECUTION_ONLY"
    )
    assert (
        current_active_workstream[
            "consumed_source_map_closure_registration_packet_result_review_classification"
        ]
        == "source_map_closure_registration_packet_accepted_closure_registration_execution_authorized_only"
    )
    assert current_active_workstream["source_map_closure_registration_token"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_EXECUTED_WITH_NO_QFT_GR_SEAM_CLOSURE_OR_RELEASE_PROMOTION"
    )
    assert current_active_workstream["source_map_closure_registration_result_review_token"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_RESULT_REVIEW_ACCEPTS_REGISTERED_SOURCE_MAP_CLOSURE_AND_AUTHORIZES_TRANCHE_004_BLOCKER_MOVEMENT_PACKET_PREPARATION_ONLY"
    )
    assert (
        current_active_workstream[
            "source_map_closure_registration_result_review_classification"
        ]
        == "registered_source_map_closure_accepted_blocker_movement_packet_preparation_only"
    )
    assert (
        current_active_workstream["source_map_closure_registration_result_classification"]
        == "source_map_closure_registered_pending_result_review"
    )
    assert (
        current_active_workstream["source_map_closure_registration_result_classification_count"]
        == "1"
    )
    assert current_active_workstream[
        "consumed_source_map_closure_registration_packet_token"
    ] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_PREPARED_WITH_NO_SEAM_CLOSURE_OR_RELEASE_PROMOTION"
    )
    assert (
        current_active_workstream[
            "consumed_source_map_closure_registration_packet_classification"
        ]
        == "source_map_closure_registration_packet_prepared_no_seam_closure_or_release_promotion"
    )
    assert current_active_workstream[
        "consumed_source_map_closure_adjudication_result_review_token"
    ] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_RESULT_REVIEW_ACCEPTS_SOURCE_MAP_CLOSURE_AUTHORIZATION_AND_AUTHORIZES_CLOSURE_REGISTRATION_PREPARATION_ONLY"
    )
    assert (
        current_active_workstream[
            "consumed_source_map_closure_adjudication_result_review_classification"
        ]
        == "source_map_closure_authorization_accepted_closure_registration_packet_preparation_only"
    )
    assert current_active_workstream["consumed_source_map_closure_adjudication_token"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_EXECUTED_WITH_NO_RELEASE_PROMOTION"
    )
    assert (
        current_active_workstream[
            "consumed_source_map_closure_adjudication_classification"
        ]
        == "source_map_closure_authorized_pending_result_review"
    )
    assert current_active_workstream[
        "consumed_source_map_authorization_adjudication_result_review_token"
    ] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_RESULT_REVIEW_ACCEPTS_REQUIREMENTS_SATISFIED_AND_AUTHORIZES_SOURCE_MAP_CLOSURE_ADJUDICATION_PREPARATION_ONLY"
    )
    assert current_active_workstream[
        "consumed_source_map_authorization_adjudication_token"
    ] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_EXECUTED_REQUIREMENTS_SATISFIED_PENDING_RESULT_REVIEW_WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
    )
    assert current_active_workstream[
        "consumed_source_map_authorization_adjudication_packet_token"
    ] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_PACKET_PREPARED_WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
    )
    assert current_active_workstream["consumed_construction_result_review_token"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_RESULT_REVIEW_ACCEPTS_WITNESS_CHAIN_CONSTRUCTION_AND_AUTHORIZES_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_PACKET_PREPARATION_ONLY"
    )
    assert current_active_workstream["consumed_construction_execution_token"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_RESEARCH_CANDIDATE_EXECUTED_WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
    )
    assert current_active_workstream["consumed_construction_packet_result_review_token"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_RESULT_REVIEW_ACCEPTS_CONSTRUCTION_PACKET_AND_AUTHORIZES_BOUNDED_CONSTRUCTION_EXECUTION_ONLY"
    )
    assert current_active_workstream["consumed_construction_packet_token"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_PREPARED_WITH_NO_WITNESS_CONSTRUCTION_OR_SOURCE_MAP_CLOSURE"
    )
    assert current_active_workstream["selected_route"] == (
        "qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result_review_after_packet_preparation"
    )
    assert current_active_workstream["selected_finding"] == "V01-ALPHA-DEP-REM-004"
    assert current_active_workstream["selected_tranche"] == "V01-ALPHA-DEP-REM-TRANCHE-004"
    assert current_active_workstream["selected_dependency"] == (
        "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0"
    )
    assert current_active_workstream["blocked_object"] == "QFT-GR source-map semantic closure"
    assert current_active_workstream["missing_object"] == "source-map witness chain"
    assert current_active_workstream["carried_prior_missing_object"] == "source-map witness chain"
    assert current_active_workstream["tranche_001_status"] == "documented_dependency_nonblocking"
    assert current_active_workstream["tranche_002_status"] == "documented_dependency_nonblocking"
    assert current_active_workstream["tranche_003_status"] == "documented_dependency_nonblocking"
    assert current_active_workstream["tranche_004_status"] == (
        "documented_source_map_closed_nonblocking"
    )
    assert current_active_workstream["tranche_005_status"] == "documented_dependency_nonblocking"
    assert current_active_workstream["tranche_006_status"] == "documented_dependency_nonblocking"
    assert current_active_workstream["simple_dependency_queue_exhausted"] == "yes"
    assert current_active_workstream["retained_tranche_004_release_blocker"] == (
        "discharged_after_dependency_remediation_closeout_pending_release_readiness_adjudication"
    )
    assert current_active_workstream["release_readiness_adjudication_executed"] == "yes"
    assert current_active_workstream["release_readiness_question_answered"] == "yes"
    assert current_active_workstream["release_readiness_decision_made"] == "yes"
    assert current_active_workstream["release_readiness_decision_status"] == (
        "release_readiness_adjudication_preparation_authorized_after_dependency_remediation_closeout_no_readiness_marking"
    )
    assert current_active_workstream["release_readiness_held"] == "yes"
    assert current_active_workstream["release_readiness_hold_accepted"] == "yes"
    assert current_active_workstream["release_readiness_proceed_authorized"] == "no"
    assert current_active_workstream["release_hold_packet_prepared"] == "yes"
    assert current_active_workstream["release_hold_packet_reviewed"] == "yes"
    assert current_active_workstream["release_hold_packet_accepted"] == "yes"
    assert current_active_workstream["release_hold_registered"] == "no"
    assert current_active_workstream["post_hold_routing_authorized"] == "yes"
    assert current_active_workstream["post_hold_routing_packet_prepared"] == "yes"
    assert (
        current_active_workstream[
            "future_remediation_program_authorized_for_preparation"
        ]
        == "yes"
    )
    assert current_active_workstream["future_remediation_program_prepared"] == "yes"
    assert current_active_workstream["future_remediation_program_executed"] == "no"
    assert current_active_workstream["future_remediation_program_result_reviewed"] == "yes"
    assert current_active_workstream["future_remediation_program_accepted_as_planning_only"] == "yes"
    assert current_active_workstream["evidence_requirements_defined"] == "yes"
    assert current_active_workstream["proof_surface_requirements_defined"] == "yes"
    assert current_active_workstream["documentation_limits_defined"] == "yes"
    assert current_active_workstream["failure_conditions_defined"] == "yes"
    assert current_active_workstream["success_conditions_defined"] == "yes"
    assert current_active_workstream["current_packet_lane"] == "release_control_plane"
    assert current_active_workstream["substantive_future_work_lane"] == (
        "qft_gr_conserved_renormalized_stress_energy_source_witness_attempt_after_packet_review"
    )
    assert current_active_workstream["source_map_witness_chain_research_packet_prepared"] == "yes"
    assert current_active_workstream["research_packet_prepared_only"] == "yes"
    assert current_active_workstream["research_packet_result_reviewed"] == "yes"
    assert current_active_workstream["research_packet_accepted_as_preparation_only"] == "yes"
    assert current_active_workstream["packet_accepted_as_closure_evidence"] == "no"
    assert current_active_workstream["candidate_witness_chain_components_defined"] == "yes"
    assert current_active_workstream["required_lean_theory_surfaces_defined"] == "yes"
    assert current_active_workstream["required_evidence_surfaces_defined"] == "yes"
    assert current_active_workstream["sandbox_research_mode_boundary_defined"] == "yes"
    assert current_active_workstream["promotion_firewall_defined"] == "yes"
    assert (
        current_active_workstream[
            "bounded_source_map_witness_chain_research_packet_authorized_for_preparation"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "bounded_source_map_witness_chain_research_packet_prepared"
        ]
        == "yes"
    )
    assert current_active_workstream["future_research_execution_target"] == (
        "execute_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt"
    )
    assert current_active_workstream["post_research_review_target"] == (
        "review_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result"
    )
    assert (
        current_active_workstream[
            "bounded_source_map_witness_chain_research_attempt_authorized_for_execution"
        ]
        == "yes"
    )
    assert current_active_workstream["source_map_witness_chain_research_execution_authorized"] == "yes"
    assert current_active_workstream["research_executed"] == "yes"
    assert current_active_workstream["bounded_source_map_witness_chain_research_attempt_executed"] == "yes"
    assert current_active_workstream["witness_chain_research_started"] == "yes"
    assert current_active_workstream["research_attempt_result_classification"] == (
        "partial_witness_chain_candidate_pending_review"
    )
    assert current_active_workstream["result_classification_count"] == "1"
    assert current_active_workstream["partial_witness_chain_candidate_produced"] == "yes"
    assert current_active_workstream["research_attempt_result_reviewed"] == "yes"
    assert current_active_workstream["research_attempt_result_review_accepted"] == "yes"
    assert current_active_workstream["consumed_result_review_classification"] == (
        "partial_witness_chain_candidate_accepted_for_construction_packet_preparation_only"
    )
    assert current_active_workstream["result_review_classification"] == (
        "qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_"
        "prepared_primary_insufficient_assumptions_for_conservation_no_closure_or_"
        "empirical_validation"
    )
    assert current_active_workstream["consumed_construction_result_review_classification"] == (
        "witness_chain_construction_accepted_source_map_authorization_adjudication_packet_preparation_only"
    )
    assert current_active_workstream["construction_packet_result_review_classification"] == (
        "construction_packet_accepted_bounded_construction_execution_authorized_only"
    )
    assert current_active_workstream[
        "source_map_authorization_adjudication_packet_result_review_classification"
    ] == (
        "source_map_authorization_adjudication_packet_accepted_bounded_adjudication_execution_authorized_only"
    )
    assert current_active_workstream[
        "source_map_authorization_adjudication_result_review_classification"
    ] == (
        "source_map_authorization_requirements_satisfied_accepted_source_map_closure_adjudication_packet_preparation_only"
    )
    assert (
        current_active_workstream[
            "partial_witness_chain_candidate_accepted_for_construction_packet_preparation_only"
        ]
        == "yes"
    )
    assert current_active_workstream["construction_packet_preparation_authorized"] == "yes"
    assert current_active_workstream["construction_packet_preparation_only"] == "yes"
    assert (
        current_active_workstream["source_map_witness_chain_construction_packet_prepared"]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_witness_chain_construction_packet_prepared_from_research_candidate"
        ]
        == "yes"
    )
    assert current_active_workstream["candidate_witness_chain_components_carried"] == "yes"
    assert current_active_workstream["required_proof_surfaces_defined"] == "yes"
    assert current_active_workstream["required_evidence_surfaces_defined"] == "yes"
    assert current_active_workstream["success_criteria_defined"] == "yes"
    assert current_active_workstream["failure_criteria_defined"] == "yes"
    assert current_active_workstream["construction_execution_boundary_defined"] == "yes"
    assert current_active_workstream["construction_target"] == (
        "construct_repo_local_source_map_witness_chain_for_retained_tranche_004_from_accepted_partial_research_candidate"
    )
    assert current_active_workstream["future_construction_execution_target"] == (
        V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_RESEARCH_CANDIDATE_EXECUTION_TARGET
    )
    assert current_active_workstream["post_packet_result_review_target"] == (
        V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_RESULT_REVIEW_TARGET
    )
    assert current_active_workstream["construction_execution_authorized_by_packet"] == "no"
    assert current_active_workstream["construction_packet_result_reviewed"] == "yes"
    assert current_active_workstream["construction_packet_result_review_accepted"] == "yes"
    assert (
        current_active_workstream[
            "construction_packet_accepted_for_bounded_construction_execution_only"
        ]
        == "yes"
    )
    assert current_active_workstream["bounded_construction_execution_authorized"] == "yes"
    assert (
        current_active_workstream["bounded_construction_execution_authorized_by_review"]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_witness_chain_construction_execution_authorized"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_witness_chain_construction_execution_authorized_by_review"
        ]
        == "yes"
    )
    assert current_active_workstream["construction_execution_target"] == (
        V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_RESEARCH_CANDIDATE_EXECUTION_TARGET
    )
    assert current_active_workstream["post_construction_result_review_target"] == (
        V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_RESEARCH_CANDIDATE_RESULT_REVIEW_TARGET
    )
    assert current_active_workstream["source_map_witness_chain_construction_executed"] == "yes"
    assert (
        current_active_workstream[
            "source_map_witness_chain_construction_executed_from_research_candidate"
        ]
        == "yes"
    )
    assert current_active_workstream["bounded_construction_execution_executed"] == "yes"
    assert current_active_workstream["bounded_construction_execution_only"] == "yes"
    assert current_active_workstream["construction_result_classification"] == (
        "witness_chain_constructed_pending_result_review"
    )
    assert current_active_workstream["construction_result_classification_count"] == "1"
    assert (
        current_active_workstream[
            "candidate_witness_chain_constructed_pending_result_review"
        ]
        == "yes"
    )
    assert (
        current_active_workstream["witness_chain_constructed_pending_result_review"]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_witness_chain_constructed_pending_result_review"
        ]
        == "yes"
    )
    assert current_active_workstream["construction_result_reviewed"] == "yes"
    assert current_active_workstream["construction_result_accepted"] == "yes"
    assert current_active_workstream["witness_chain_construction_accepted"] == "yes"
    assert current_active_workstream["source_map_witness_chain_construction_accepted"] == "yes"
    assert current_active_workstream["witness_chain_constructed_accepted_by_review"] == "yes"
    assert (
        current_active_workstream["source_map_witness_chain_constructed_accepted_by_review"]
        == "yes"
    )
    assert (
        current_active_workstream[
            "accepted_for_source_map_authorization_adjudication_packet_preparation_only"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_authorization_adjudication_packet_preparation_authorized"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_authorization_adjudication_packet_preparation_only"
        ]
        == "yes"
    )
    assert current_active_workstream["source_map_authorization_adjudication_packet_classification"] == (
        "source_map_authorization_adjudication_packet_prepared_no_closure_or_release_promotion"
    )
    assert current_active_workstream["source_map_authorization_adjudication_packet_prepared"] == "yes"
    assert current_active_workstream["source_map_authorization_adjudication_packet_preparation_only"] == "yes"
    assert current_active_workstream["source_map_authorization_adjudication_prepared"] == "no"
    assert (
        current_active_workstream[
            "source_map_authorization_adjudication_execution_authorized_by_packet"
        ]
        == "no"
    )
    assert (
        current_active_workstream["source_map_authorization_adjudication_execution_authorized"]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_authorization_adjudication_execution_authorized_by_review"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "bounded_source_map_authorization_adjudication_execution_authorized"
        ]
        == "yes"
    )
    assert current_active_workstream["source_map_authorization_adjudication_executed"] == "yes"
    assert current_active_workstream["bounded_source_map_authorization_adjudication_executed"] == "yes"
    assert (
        current_active_workstream[
            "bounded_source_map_authorization_adjudication_execution_only"
        ]
        == "yes"
    )
    assert current_active_workstream["source_map_authorization_adjudication_result_review_authorized"] == "yes"
    assert current_active_workstream["source_map_authorization_adjudication_result_classification"] == (
        "source_map_authorization_requirements_satisfied_pending_result_review_no_closure_or_release_promotion"
    )
    assert current_active_workstream["adjudication_result_classification_count"] == "1"
    assert current_active_workstream["adjudication_question"] == (
        "Does the accepted witness-chain construction satisfy the source-map "
        "semantic-closure authorization requirements?"
    )
    assert current_active_workstream["adjudication_question_answered"] == "yes"
    assert current_active_workstream["adjudication_answer"] == (
        "yes_satisfies_source_map_semantic_closure_authorization_requirements_pending_result_review"
    )
    assert current_active_workstream["adjudication_answer_pending_result_review"] == "yes"
    assert (
        current_active_workstream[
            "source_map_authorization_requirements_satisfied_pending_result_review"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_semantic_closure_authorization_requirements_satisfied_pending_result_review"
        ]
        == "yes"
    )
    assert current_active_workstream["adjudication_requirement_count"] == "7"
    assert current_active_workstream["adjudicated_requirement_count"] == "7"
    assert current_active_workstream["adjudication_success_criteria_count"] == "4"
    assert current_active_workstream["adjudication_failure_criteria_count"] == "4"
    assert current_active_workstream["adjudication_execution_boundary_count"] == "5"
    assert current_active_workstream["adjudication_execution_step_count"] == "5"
    assert current_active_workstream["future_source_map_authorization_adjudication_execution_target"] == (
        V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_EXECUTION_TARGET
    )
    assert current_active_workstream["source_map_authorization_adjudication_execution_target"] == (
        V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_EXECUTION_TARGET
    )
    assert current_active_workstream["post_adjudication_result_review_target"] == (
        V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_RESULT_REVIEW_TARGET
    )
    assert current_active_workstream["source_map_authorization_adjudication_result_reviewed"] == "yes"
    assert current_active_workstream["source_map_authorization_adjudication_result_accepted"] == "yes"
    assert current_active_workstream["requirements_satisfied_status_accepted_by_review"] == "yes"
    assert (
        current_active_workstream[
            "source_map_authorization_requirements_satisfied_accepted_by_review"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_authorization_requirements_satisfied_accepted_for_closure_adjudication_packet_preparation_only"
        ]
        == "yes"
    )
    assert current_active_workstream["source_map_authorization_result_accepted_as_closure_evidence"] == "no"
    assert current_active_workstream["adjudication_answer_accepted_by_review"] == "yes"
    assert current_active_workstream["reviewed_authorization_requirement_count"] == "7"
    assert current_active_workstream["accepted_authorization_requirement_count"] == "7"
    assert current_active_workstream["source_map_closure_adjudication_packet_preparation_authorized"] == "yes"
    assert current_active_workstream["source_map_closure_adjudication_packet_preparation_only"] == "yes"
    assert current_active_workstream["source_map_closure_adjudication_packet_prepared"] == "yes"
    assert current_active_workstream["source_map_closure_adjudication_packet_classification"] == (
        "source_map_closure_adjudication_packet_prepared_no_source_map_closure_or_release_promotion"
    )
    assert current_active_workstream["packet_classification"] == (
        "qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_"
        "prepared_primary_insufficient_assumptions_for_conservation_no_closure_or_"
        "empirical_validation"
    )
    assert current_active_workstream["packet_classification_count"] == "1"
    assert current_active_workstream["source_map_closure_adjudication_question_prepared"] == "yes"
    assert current_active_workstream["source_map_closure_adjudication_question_answered"] == "yes"
    assert current_active_workstream["closure_adjudication_requirement_count"] == "7"
    assert current_active_workstream["closure_adjudication_success_criteria_count"] == "4"
    assert current_active_workstream["closure_adjudication_failure_criteria_count"] == "4"
    assert current_active_workstream["closure_adjudication_execution_boundary_count"] == "5"
    assert current_active_workstream["source_map_closure_adjudication_execution_authorized"] == "yes"
    assert (
        current_active_workstream[
            "bounded_source_map_closure_adjudication_execution_authorized"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_closure_adjudication_execution_authorized_by_review"
        ]
        == "yes"
    )
    assert current_active_workstream["source_map_closure_adjudication_executed"] == "yes"
    assert (
        current_active_workstream["bounded_source_map_closure_adjudication_executed"]
        == "yes"
    )
    assert (
        current_active_workstream[
            "bounded_source_map_closure_adjudication_execution_only"
        ]
        == "yes"
    )
    assert current_active_workstream["source_map_closure_adjudication_result_review_authorized"] == "yes"
    assert current_active_workstream["source_map_closure_adjudication_result_classification"] == (
        "source_map_closure_authorized_pending_result_review"
    )
    assert current_active_workstream["closure_adjudication_result_classification_count"] == "1"
    assert current_active_workstream["closure_adjudication_answer"] == (
        "yes_source_map_closure_authorized_pending_result_review"
    )
    assert (
        current_active_workstream["source_map_closure_authorized_pending_result_review"]
        == "yes"
    )
    assert current_active_workstream["closure_adjudication_question"] == (
        "Given that source-map authorization requirements were accepted, can "
        "source-map closure be adjudicated under the repo's release-control rules?"
    )
    assert current_active_workstream["consumed_construction_result_classification"] == (
        "witness_chain_constructed_pending_result_review"
    )
    assert current_active_workstream["witness_chain_constructed"] == "yes"
    assert current_active_workstream["source_map_witness_chain_constructed"] == "yes"
    assert current_active_workstream["witness_chain_constructed_claimed"] == "yes"
    assert current_active_workstream["source_map_witness_chain_constructed_claimed"] == "yes"
    assert current_active_workstream["construction_result_claimed"] == "yes"
    assert current_active_workstream["constructed_witness_chain_component_count"] == "7"
    assert current_active_workstream["required_witness_chain_component_count"] == "7"
    assert current_active_workstream["required_future_route_for_tranche_004"] == (
        "retained_tranche_004_source_map_witness_chain_or_governed_retained_blocker_"
        "continuation_required_before_release_assembly"
    )
    assert current_active_workstream["tranche_004_status_moved"] == "yes"
    assert current_active_workstream["tranche_004_retained_blocker_discharged"] == "yes"
    assert current_active_workstream["source_map_closure_achieved"] == "yes"
    assert current_active_workstream["source_map_closure_requirements_adjudicated"] == "yes"
    assert (
        current_active_workstream[
            "source_map_closure_authorization_requirements_decision_recorded"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_closure_authorization_decision_accepted_by_review"
        ]
        == "yes"
    )
    assert current_active_workstream["adjudication_result_accepted_by_review"] == "yes"
    assert (
        current_active_workstream["source_map_closure_adjudication_result_reviewed"]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_closure_adjudication_result_accepted_by_review"
        ]
        == "yes"
    )
    assert (
        current_active_workstream["source_map_closure_authorization_accepted_by_review"]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_closure_authorization_accepted_for_registration_packet_preparation_only"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_closure_authorization_accepted_as_final_closure"
        ]
        == "no"
    )
    assert (
        current_active_workstream["closure_adjudication_answer_accepted_by_review"]
        == "yes"
    )
    assert current_active_workstream["reviewed_closure_requirement_count"] == "7"
    assert current_active_workstream["accepted_closure_requirement_count"] == "7"
    assert current_active_workstream["registration_criteria_count"] == "4"
    assert current_active_workstream["evidence_chain_count"] == "9"
    assert current_active_workstream["forbidden_downstream_claim_count"] == "6"
    assert current_active_workstream["adjudication_result_claimed_as_closure"] == "no"
    assert (
        current_active_workstream[
            "source_map_closure_authorization_result_review_required"
        ]
        == "no"
    )
    assert (
        current_active_workstream[
            "source_map_closure_registration_packet_preparation_authorized"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_closure_registration_packet_preparation_only"
        ]
        == "yes"
    )
    assert (
        current_active_workstream["source_map_closure_registration_packet_prepared"]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_closure_registration_packet_result_review_authorized"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_closure_registration_packet_result_reviewed"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_closure_registration_packet_result_accepted"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_closure_registration_packet_accepted_for_registration_execution_only"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_closure_registration_packet_accepted_as_final_closure"
        ]
        == "no"
    )
    assert (
        current_active_workstream["source_map_closure_registration_status_proposed"]
        == "source_map_closure_registration_proposed_pending_packet_result_review"
    )
    assert (
        current_active_workstream["source_map_closure_registration_status_registered"]
        == "source_map_closure_registered_pending_result_review"
    )
    assert (
        current_active_workstream["source_map_closure_registration_authorized"]
        == "yes"
    )
    assert (
        current_active_workstream[
            "bounded_source_map_closure_registration_execution_authorized"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "source_map_closure_registration_execution_authorized_by_review"
        ]
        == "yes"
    )
    assert (
        current_active_workstream["source_map_closure_registration_execution_authorized"]
        == "yes"
    )
    assert current_active_workstream["source_map_closure_registration_execution_target"] == (
        V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_EXECUTION_TARGET
    )
    assert current_active_workstream["source_map_closure_registration_executed"] == "yes"
    assert (
        current_active_workstream["bounded_source_map_closure_registration_executed"]
        == "yes"
    )
    assert (
        current_active_workstream["bounded_source_map_closure_registration_execution_only"]
        == "yes"
    )
    assert (
        current_active_workstream["source_map_closure_registration_status"]
        == "source_map_closure_registered_result_review_accepted"
    )
    assert (
        current_active_workstream["source_map_closure_registered_pending_result_review"]
        == "no"
    )
    assert (
        current_active_workstream["source_map_closure_registration_pending_result_review"]
        == "no"
    )
    assert (
        current_active_workstream["source_map_closure_registration_result_review_required"]
        == "no"
    )
    assert (
        current_active_workstream["source_map_closure_registration_result_review_authorized"]
        == "no"
    )
    assert current_active_workstream["source_map_closure_registered"] == "yes"
    assert current_active_workstream["source_map_closure_registered_as_final"] == "yes"
    assert current_active_workstream["final_source_map_closure_registered"] == "yes"
    assert current_active_workstream["final_source_map_closure_authorized"] == "yes"
    assert (
        current_active_workstream["source_map_closure_result_claimed_as_final_closure"]
        == "no"
    )
    assert current_active_workstream["source_map_closure_claimed"] == "no"
    assert current_active_workstream["source_map_closure_authorized"] == "yes"
    assert current_active_workstream["source_map_closure_achieved"] == "yes"
    assert current_active_workstream["source_map_closure_external_truth_claimed"] == "no"
    assert (
        current_active_workstream["source_map_closure_registration_external_truth_claimed"]
        == "no"
    )
    assert (
        current_active_workstream["blocker_movement_packet_preparation_authorized"]
        == "yes"
    )
    assert (
        current_active_workstream[
            "blocker_movement_registration_packet_preparation_authorized"
        ]
        == "yes"
    )
    assert (
        current_active_workstream["blocker_movement_registration_packet_preparation_only"]
        == "yes"
    )
    assert current_active_workstream["blocker_movement_registration_packet_prepared"] == "yes"
    assert (
        current_active_workstream["post_source_map_closure_blocker_movement_packet_target"]
        == V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_AFTER_SOURCE_MAP_CLOSURE_TARGET
    )
    assert current_active_workstream[
        "blocker_movement_registration_packet_after_source_map_closure_token"
    ] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_AFTER_SOURCE_MAP_CLOSURE_PREPARED_WITH_NO_SEAM_CLOSURE_OR_RELEASE_PROMOTION"
    )
    assert (
        current_active_workstream[
            "blocker_movement_registration_packet_after_source_map_closure_classification"
        ]
        == "blocker_movement_registration_packet_prepared_after_source_map_closure_no_seam_closure_or_release_promotion"
    )
    assert (
        current_active_workstream[
            "consumed_source_map_closure_registration_result_review_classification"
        ]
        == "registered_source_map_closure_accepted_blocker_movement_packet_preparation_only"
    )
    assert (
        current_active_workstream["accepted_source_map_closure_registration"]
        == "registered_source_map_closure_accepted"
    )
    assert (
        current_active_workstream["prior_tranche_004_status"]
        == "retained_release_blocking_source_map_blocker"
    )
    assert (
        current_active_workstream["proposed_tranche_004_status"]
        == "documented_source_map_closed_nonblocking"
    )
    assert (
        current_active_workstream["proposed_tranche_004_movement"]
        == "retained_release_blocking_source_map_blocker_to_documented_source_map_closed_nonblocking"
    )
    assert (
        current_active_workstream[
            "blocker_movement_registration_packet_prepared_after_source_map_closure"
        ]
        == "yes"
    )
    assert (
        current_active_workstream["blocker_movement_registration_packet_result_review_required"]
        == "no"
    )
    assert (
        current_active_workstream[
            "blocker_movement_registration_packet_result_review_authorized"
        ]
        == "no"
    )
    assert (
        current_active_workstream[
            "blocker_movement_registration_packet_result_review_surface"
        ]
        == (
            "formal/toe_formal/ToeFormal/Release/"
            "V01RetainedTranche004BlockerMovementRegistrationPacketAfterSourceMapClosureResultReview.lean"
        )
    )
    assert (
        current_active_workstream[
            "blocker_movement_registration_packet_result_review_report"
        ]
        == (
            "formal/docs/release/"
            "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_20260523_v0.json"
        )
    )
    assert (
        current_active_workstream[
            "blocker_movement_registration_packet_result_review_token"
        ]
        == "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BLOCKER_MOVEMENT_EXECUTION_ONLY"
    )
    assert (
        current_active_workstream[
            "blocker_movement_registration_packet_result_review_classification"
        ]
        == "blocker_movement_registration_packet_accepted_after_source_map_closure_blocker_movement_execution_authorized_only"
    )
    assert (
        current_active_workstream[
            "blocker_movement_registration_packet_result_reviewed"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "blocker_movement_registration_packet_result_accepted"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "blocker_movement_registration_packet_accepted_for_execution_only"
        ]
        == "yes"
    )
    assert (
        current_active_workstream["blocker_movement_registration_execution_authorized"]
        == "yes"
    )
    assert current_active_workstream["blocker_movement_execution_authorized"] == "yes"
    assert current_active_workstream["tranche_004_status_moved_by_packet"] == "no"
    assert current_active_workstream["tranche_004_status_moved_by_review"] == "no"
    assert (
        current_active_workstream[
            "tranche_004_moved_to_documented_source_map_closed_nonblocking"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "post_blocker_movement_registration_packet_result_review_target"
        ]
        == V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_TARGET
    )
    assert (
        current_active_workstream["blocker_movement_registration_execution_target"]
        == V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_SOURCE_MAP_CLOSURE_EXECUTION_TARGET
    )
    assert current_active_workstream["blocker_movement_registration_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_SOURCE_MAP_CLOSURE_20260523_v0.json"
    )
    assert current_active_workstream["blocker_movement_registration_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004BlockerMovementRegistrationAfterSourceMapClosure.lean"
    )
    assert current_active_workstream["blocker_movement_registration_token"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTERED_AFTER_SOURCE_MAP_CLOSURE_WITH_NO_SEAM_CLOSURE_OR_RELEASE_PROMOTION"
    )
    assert (
        current_active_workstream["blocker_movement_registration_result_classification"]
        == "tranche_004_blocker_movement_registered_as_documented_source_map_closed_nonblocking_pending_result_review"
    )
    assert current_active_workstream["blocker_movement_registration_status"] == (
        "documented_source_map_closed_nonblocking"
    )
    assert current_active_workstream["blocker_movement_registration_executed"] == "yes"
    assert current_active_workstream["blocker_movement_registered"] == "yes"
    assert (
        current_active_workstream["blocker_movement_registration_result_review_target"]
        == V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_TARGET
    )
    assert current_active_workstream["blocker_movement_registration_result_review_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004BlockerMovementRegistrationAfterSourceMapClosureResultReview.lean"
    )
    assert current_active_workstream["blocker_movement_registration_result_review_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_20260523_v0.json"
    )
    assert current_active_workstream["blocker_movement_registration_result_review_token"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW_ACCEPTS_DOCUMENTED_SOURCE_MAP_CLOSED_NONBLOCKING_STATUS_AND_AUTHORIZES_DEPENDENCY_REMEDIATION_CLOSEOUT_PREPARATION_ONLY"
    )
    assert current_active_workstream["blocker_movement_registration_result_review_classification"] == (
        "documented_source_map_closed_nonblocking_status_accepted_dependency_remediation_closeout_preparation_only"
    )
    assert current_active_workstream["blocker_movement_registration_result_reviewed"] == "yes"
    assert current_active_workstream["blocker_movement_registration_result_accepted"] == "yes"
    assert current_active_workstream["documented_source_map_closed_nonblocking_status_accepted"] == "yes"
    assert current_active_workstream["documented_source_map_closed_nonblocking_status_rejected"] == "no"
    assert current_active_workstream["movement_registration_criteria_count"] == "4"
    assert current_active_workstream["evidence_chain_count"] == "9"
    assert current_active_workstream["blocker_movement_registration_step_count"] == "5"
    assert current_active_workstream["release_readiness_still_blocked"] == "yes"
    assert current_active_workstream["qft_gr_seam_closed"] == "no"
    assert current_active_workstream["qft_gr_seam_closure_authorized"] == "no"
    assert current_active_workstream["qft_gr_seam_closure_claimed"] == "no"
    assert current_active_workstream["tranche_004_status_moved_by_execution"] == "yes"
    assert current_active_workstream["tranche_004_status_moved_by_result_review"] == "yes"
    assert current_active_workstream["tranche_004_status"] == (
        "documented_source_map_closed_nonblocking"
    )
    assert current_active_workstream["tranche_004_status_pending_result_review"] == "no"
    assert current_active_workstream["tranche_004_formal_movement_accepted"] == "yes"
    assert current_active_workstream["tranche_004_retained_blocker_discharged"] == "yes"
    assert current_active_workstream["dependency_remediation_closeout_preparation_authorized"] == "yes"
    assert current_active_workstream["dependency_remediation_closeout_prepared"] == "yes"
    assert current_active_workstream["dependency_remediation_closeout_packet_prepared"] == "yes"
    assert current_active_workstream["dependency_remediation_closeout_result_review_required"] == "no"
    assert current_active_workstream["dependency_remediation_closeout_status"] == (
        "dependency_remediation_closeout_accepted_all_tranches_documented_nonblocking"
    )
    assert current_active_workstream["dependency_remediation_closeout_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01DependencyRemediationCloseoutAfterTranche004Movement.lean"
    )
    assert current_active_workstream["dependency_remediation_closeout_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_MOVEMENT_20260523_v0.json"
    )
    assert current_active_workstream["dependency_remediation_closeout_token"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_PREPARED_AFTER_TRANCHE_004_MOVEMENT_WITH_NO_RELEASE_READINESS_OR_SEAM_PROMOTION"
    )
    assert current_active_workstream["dependency_remediation_closeout_classification"] == (
        "dependency_remediation_closeout_prepared_all_tranches_documented_nonblocking_no_release_readiness_or_seam_promotion"
    )
    assert current_active_workstream["dependency_remediation_closeout_result_review_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01DependencyRemediationCloseoutAfterTranche004MovementResultReview.lean"
    )
    assert current_active_workstream["dependency_remediation_closeout_result_review_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_MOVEMENT_RESULT_REVIEW_20260523_v0.json"
    )
    assert current_active_workstream["dependency_remediation_closeout_result_review_token"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_ALL_TRANCHES_DOCUMENTED_NONBLOCKING_AND_AUTHORIZES_RELEASE_READINESS_ADJUDICATION_PREPARATION_ONLY"
    )
    assert current_active_workstream["dependency_remediation_closeout_result_review_classification"] == (
        "dependency_remediation_closeout_accepted_all_tranches_documented_nonblocking_release_readiness_adjudication_preparation_only"
    )
    assert current_active_workstream["dependency_remediation_closeout_result_reviewed"] == "yes"
    assert current_active_workstream["dependency_remediation_closeout_result_accepted"] == "yes"
    assert current_active_workstream["dependency_remediation_closeout_accepted"] == "yes"
    assert current_active_workstream["dependency_remediation_queue_closed"] == "yes"
    assert current_active_workstream["release_readiness_adjudication_preparation_authorized"] == "yes"
    assert current_active_workstream["release_readiness_adjudication_prepared"] == "yes"
    assert current_active_workstream["release_readiness_eligible_for_adjudication"] == "no"
    assert current_active_workstream["release_readiness_still_requires_separate_adjudication"] == "yes"
    assert current_active_workstream["release_readiness_adjudication_packet_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01ReleaseReadinessAdjudicationAfterDependencyRemediationCloseoutPacket.lean"
    )
    assert current_active_workstream["release_readiness_adjudication_packet_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
        "CLOSEOUT_PACKET_20260525_v0.json"
    )
    assert current_active_workstream["release_readiness_adjudication_packet_token"] == (
        "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
        "CLOSEOUT_PACKET_PREPARED_CRITICIZABILITY_ONLY_NO_RELEASE_ASSEMBLY_OR_"
        "SEAM_PROMOTION"
    )
    assert current_active_workstream["release_readiness_adjudication_packet_classification"] == (
        "criticizability_readiness_adjudication_packet_prepared_after_dependency_"
        "remediation_closeout_no_release_assembly_or_seam_promotion"
    )
    assert current_active_workstream["criticizability_readiness_adjudication_packet_prepared"] == "yes"
    assert current_active_workstream["criticizability_readiness_question"] == (
        "Is v0.1-alpha eligible for criticizability-readiness adjudication after "
        "dependency-remediation closeout?"
    )
    assert current_active_workstream["criticizability_readiness_question_prepared"] == "yes"
    assert current_active_workstream["criticizability_readiness_question_answered"] == "yes"
    assert current_active_workstream["criticizability_readiness_decision_made"] == "yes"
    assert current_active_workstream["criticizability_readiness_status"] == (
        "v01_alpha_criticizability_readiness_eligible_pending_result_review"
    )
    assert current_active_workstream["criticizability_readiness_result_review_required"] == "yes"
    assert current_active_workstream["criticizability_readiness_packet_result_reviewed"] == "yes"
    assert current_active_workstream["criticizability_readiness_packet_accepted"] == "yes"
    assert (
        current_active_workstream["criticizability_readiness_adjudication_execution_authorized"]
        == "yes"
    )
    assert current_active_workstream["criticizability_readiness_adjudication_executed"] == "yes"
    assert current_active_workstream["criticizability_readiness_decision"] == (
        "v01_alpha_criticizability_readiness_eligible_pending_result_review"
    )
    assert current_active_workstream["criticizability_readiness_firewall_defined"] == "yes"
    assert current_active_workstream["public_submission_authorized"] == "no"
    assert current_active_workstream["scientific_validation_claimed"] == "no"
    assert (
        current_active_workstream["semiclassical_einstein_equation_derivation_claimed"]
        == "no"
    )
    assert current_active_workstream["track2_qft_gr_witness_target"] == (
        "construct_or_refute_qft_gr_conserved_renormalized_stress_energy_source_witness"
    )
    assert (
        current_active_workstream[
            "track2_qft_gr_witness_target_deferred_until_result_review"
        ]
        == "yes"
    )
    assert current_active_workstream["track2_control_clearance_only"] == "yes"
    assert current_active_workstream["track2_scientific_evidence_claimed_from_track1"] == "no"
    assert current_active_workstream["criticizability_readiness_result_reviewed"] == "yes"
    assert current_active_workstream["criticizability_readiness_eligibility_accepted"] == "yes"
    assert current_active_workstream["criticizability_readiness_eligibility_rejected"] == "no"
    assert current_active_workstream["criticizability_readiness_review_decision"] == (
        "criticizability_readiness_eligibility_accepted"
    )
    assert current_active_workstream["qft_gr_witness_packet_preparation_authorized"] == "yes"
    assert current_active_workstream["qft_gr_witness_packet_prepared"] == "no"
    assert current_active_workstream["qft_gr_witness_packet_target"] == (
        "prepare_qft_gr_conserved_renormalized_stress_energy_source_witness_packet"
    )
    assert current_active_workstream["qft_gr_witness_execution_authorized"] == "yes"
    assert current_active_workstream["qft_gr_witness_executed"] == "yes"
    assert current_active_workstream["track2_selected_after_result_review"] == "yes"
    assert current_active_workstream["track2_selection_kind"] == (
        "qft_gr_witness_packet_preparation_only"
    )
    assert current_active_workstream["track2_science_lane_execution_started"] == "yes_bounded_attempt_result_reviewed"
    assert current_active_workstream["track2_started"] == (
        "covariant_conservation_proof_object_obstruction_refinement_packet_prepared_result_review_pending"
    )
    assert current_active_workstream["track2_selected_after_this_execution"] == "no"
    assert current_active_workstream["next_action_scope"] == (
        "REVIEW_QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_PACKET_"
        "RESULT_ONLY_NO_PROOF_OBJECT_OR_QFT_GR_SEAM_CLOSURE"
    )
    assert current_active_workstream["all_dependency_tranches_nonblocking"] == "yes"
    assert current_active_workstream["closeout_criteria_count"] == "4"
    assert current_active_workstream["documented_dependency_nonblocking_tranche_count"] == "6"
    assert current_active_workstream["selected_next_target"] == LIVE_TARGET
    assert current_active_workstream["witness_attempt_executed"] == "yes"
    assert current_active_workstream["result_classification"] == (
        "qft_gr_covariant_conservation_proof_object_obstruction_identified_requires_refinement"
    )
    assert current_active_workstream["result_classification_count"] == "1"
    assert current_active_workstream["constructed_witness_result"] == "no"
    assert current_active_workstream["obstruction_identified_result"] == "yes"
    assert current_active_workstream["inconclusive_result"] == "no"
    assert current_active_workstream["attempt_result_reviewed"] == "yes"
    assert current_active_workstream["covariant_conservation_obstruction_result_accepted"] == "yes"
    assert current_active_workstream["refinement_packet_preparation_authorized"] == "yes"
    assert current_active_workstream["refinement_packet_prepared"] == "yes"
    assert current_active_workstream["obstruction_result_accepted"] == "yes"
    assert current_active_workstream["refinement_packet_preparation_authorized"] == "yes"
    assert current_active_workstream["obstruction_refinement_packet_prepared"] == "yes"
    assert current_active_workstream["obstruction_refinement_packet_result_reviewed"] == "yes"
    assert current_active_workstream["conservation_primary_obstruction_accepted"] == "yes"
    assert (
        current_active_workstream["primary_missing_condition"]
        == "post_operator_domain_statement_missing_conservation_proof_object"
    )
    assert current_active_workstream["primary_obstruction_solved"] == "no"
    assert current_active_workstream["conservation_witness_packet_preparation_authorized"] == "yes"
    assert current_active_workstream["conservation_witness_packet_prepared"] == "yes"
    assert current_active_workstream["conservation_witness_packet_result_reviewed"] == "yes"
    assert current_active_workstream["bounded_conservation_witness_attempt_authorized"] == "yes"
    assert current_active_workstream["conservation_witness_attempt_executed"] == "yes"
    assert current_active_workstream["conservation_obstruction_result_accepted"] == "yes"
    assert current_active_workstream["prepares_refinement_only"] == "yes"
    assert current_active_workstream["identifies_covariant_conservation_obstruction_more_narrowly"] == "yes"
    assert current_active_workstream["future_operator_domain_packet_target"] == (
        "prepare_qft_gr_covariant_derivative_operator_domain_packet"
    )
    assert current_active_workstream["operator_domain_structure_prepared"] == "yes"
    assert current_active_workstream["operator_domain_requirement_count"] == "6"
    assert current_active_workstream["covariant_conservation_statement_prepared"] == "yes"
    assert current_active_workstream["covariant_conservation_statement_formulated"] == "yes"
    assert current_active_workstream["covariant_conservation_statement_attempted"] == "yes"
    assert current_active_workstream["covariant_conservation_statement_proved"] == "no"
    assert current_active_workstream["qft_gr_covariant_derivative_operator_domain_packet_classification"] == (
        "qft_gr_covariant_derivative_operator_domain_packet_prepared_"
        "no_conservation_witness_or_seam_closure"
    )
    assert current_active_workstream["operator_domain_preparation_only_confirmed"] == "yes"
    assert current_active_workstream["qft_gr_covariant_derivative_operator_domain_packet_result_review_classification"] == (
        "qft_gr_covariant_derivative_operator_domain_packet_result_review_accepts_"
        "operator_domain_preparation_and_authorizes_next_bounded_conservation_statement_packet_only"
    )
    assert current_active_workstream["qft_gr_covariant_conservation_statement_with_operator_domain_packet_classification"] == (
        "qft_gr_covariant_conservation_statement_with_operator_domain_packet_prepared_"
        "no_conservation_witness_or_seam_closure"
    )
    assert current_active_workstream["qft_gr_covariant_conservation_statement_with_operator_domain_packet_result_review_classification"] == (
        "qft_gr_covariant_conservation_statement_with_operator_domain_packet_result_review_"
        "accepts_statement_formulation_and_authorizes_bounded_conservation_witness_attempt_only"
    )
    assert current_active_workstream["statement_formulation_accepted"] == "yes"
    assert current_active_workstream["statement_formulated_under_accepted_operator_domain"] == "yes"
    assert current_active_workstream["qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt_classification"] == (
        "qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_identified_requires_refinement"
    )
    assert current_active_workstream["qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt_result_review_classification"] == (
        "qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt_result_review_"
        "accepts_obstruction_and_authorizes_refinement_packet_preparation_only"
    )
    assert current_active_workstream["refined_obstruction_class"] == (
        "post_operator_domain_statement_missing_conservation_proof_object"
    )
    assert current_active_workstream["covariant_conservation_statement_with_operator_domain_witness_attempt_executed"] == "yes"
    assert current_active_workstream["covariant_conservation_statement_with_operator_domain_witness_constructed"] == "no"

    assert current_active_workstream["qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_classification"] == (
        "qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_prepared_"
        "primary_missing_conservation_proof_object_no_closure_or_empirical_validation"
    )
    assert current_active_workstream["selected_obstruction"] == (
        "post_operator_domain_statement_missing_conservation_proof_object"
    )
    assert current_active_workstream["available_structure"] == (
        "covariant_conservation_statement_with_operator_domain"
    )
    assert current_active_workstream["missing_proof_object"] == (
        "conservation_proof_object_for_candidate_source_under_prepared_operator_domain"
    )
    assert current_active_workstream["required_theorem_shape"] == (
        "candidate_stress_energy_source_in_prepared_operator_domain -> "
        "covariant_divergence candidate_stress_energy_source = 0"
    )
    assert current_active_workstream["next_bounded_action"] == LIVE_TARGET

    assert current_active_workstream["qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review_classification"] == (
        "qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_result_review_"
        "accepts_missing_conservation_proof_object_and_authorizes_proof_object_packet_preparation_only"
    )
    assert current_active_workstream["missing_conservation_proof_object_accepted"] == "yes"
    assert current_active_workstream["proof_object_packet_preparation_authorized"] == "yes"
    assert current_active_workstream["conservation_proof_object_constructed"] == "no"

    assert current_active_workstream["qft_gr_covariant_conservation_proof_object_packet_classification"] == (
        "qft_gr_covariant_conservation_proof_object_packet_prepared_no_"
        "conservation_witness_or_seam_closure"
    )
    assert current_active_workstream["target_proof_object"] == (
        "conservation_proof_object_for_candidate_source_under_prepared_operator_domain"
    )
    assert current_active_workstream["covariant_conservation_statement_to_be_proved"] == (
        "candidate_stress_energy_source_in_prepared_operator_domain -> "
        "covariant_divergence candidate_stress_energy_source = 0"
    )
    assert current_active_workstream["prepares_proof_object_packet_only"] == "yes"
    assert current_active_workstream["proof_object_packet_preparation_accepted"] == "yes"
    assert current_active_workstream["bounded_proof_object_attempt_authorized"] == "yes"
    assert current_active_workstream["proof_object_packet_prepared_only"] == "yes"
    assert current_active_workstream["qft_gr_covariant_conservation_proof_object_packet_result_review_classification"] == (
        "qft_gr_covariant_conservation_proof_object_packet_result_review_accepts_"
        "proof_object_preparation_and_authorizes_bounded_proof_object_attempt_only"
    )
    assert current_active_workstream["proof_object_attempt_executed"] == "yes"
    assert current_active_workstream["qft_gr_covariant_conservation_proof_object_attempt_classification"] == (
        "qft_gr_covariant_conservation_proof_object_obstruction_identified_requires_refinement"
    )
    assert current_active_workstream["constructed_proof_object_result"] == "no"
    assert current_active_workstream["obstruction_identified_result"] == "yes"
    assert current_active_workstream["inconclusive_result"] == "no"
    assert current_active_workstream["conservation_witness_upgraded_by_execution"] == "no"
    assert current_active_workstream["proof_object_attempt_result_reviewed"] == "yes"
    assert current_active_workstream["proof_object_obstruction_accepted"] == "yes"
    assert current_active_workstream["proof_object_obstruction_class"] == (
        "qft_gr_covariant_conservation_proof_object_obstruction_identified_requires_refinement"
    )
    assert current_active_workstream["qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_classification"] == (
        "qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_"
        "prepared_primary_insufficient_assumptions_for_conservation_no_closure_or_"
        "empirical_validation"
    )
    assert current_active_workstream["primary_blocker"] == (
        "insufficient_assumptions_for_conservation"
    )
    assert current_active_workstream["selected_primary_blocker"] == (
        "insufficient_assumptions_for_conservation"
    )
    assert current_active_workstream["blocker_menu_count"] == "7"
    assert current_active_workstream["identifies_proof_object_obstruction_more_narrowly"] == "yes"
    assert current_active_workstream["prepares_refinement_only"] == "yes"
    assert current_active_workstream["statement_component_count"] == "6"
    assert current_active_workstream["primary_blocker_addressed_at_preparation_level"] == "yes"
    assert current_active_workstream["qft_gr_covariant_conservation_statement_obstruction_refinement_packet_classification"] == (
        "qft_gr_covariant_conservation_statement_obstruction_refinement_packet_prepared_"
        "primary_missing_covariant_derivative_operator_domain_no_closure_or_empirical_validation"
    )
    assert current_active_workstream["covariant_conservation_statement_witness_packet_prepared"] == "yes"
    assert current_active_workstream["covariant_conservation_statement_witness_attempt_executed"] == "yes"
    assert current_active_workstream["covariant_conservation_statement_witness_constructed"] == "no"
    assert current_active_workstream[
        "qft_gr_covariant_conservation_statement_witness_attempt_classification"
    ] == (
        "qft_gr_covariant_conservation_statement_obstruction_identified_requires_refinement"
    )
    assert current_active_workstream["prepares_packet_only"] == "yes"
    assert current_active_workstream["packet_preparation_only_confirmed"] == "yes"
    assert current_active_workstream["bounded_witness_attempt_authorized"] == "yes"
    assert current_active_workstream["primary_blocker_preserved"] == "yes"
    assert current_active_workstream["primary_obstruction_id"] == (
        "qft_gr_covariant_conservation_statement_with_operator_domain_missing_conservation_proof_object_v0"
    )
    assert current_active_workstream["obstruction_class"] == (
        "qft_gr_covariant_conservation_statement_obstruction_identified_requires_refinement"
    )
    assert current_active_workstream["conservation_witness_constructed"] == "no"
    assert current_active_workstream["stress_energy_source_admissibility_claimed"] == "no"
    assert current_active_workstream["Bianchi_compatibility_claimed"] == "no"
    assert current_active_workstream["release_packet_assembled"] == "no"
    assert current_active_workstream["public_release_completion_authorized"] == "no"
    assert current_active_workstream["master_action_promotion_authorized"] == "no"
    assert current_active_workstream["pillar_completion_inferred"] == "no"
    assert current_active_workstream["seam_closure_claim"] == "no"
    assert current_active_workstream["phase2_readiness_claim"] == "no"
    assert current_active_workstream["empirical_adequacy_claim"] == "no"
    assert current_active_workstream["canonical_toe_claim"] == "no"
    assert current_active_workstream["qft_gr_source_map_closure_authorized"] == "no"
    assert current_active_workstream["unrelated_gate_enrollment_authorized"] == "no"

    previous_full_pillar_workstream = _workstream(
        payload, "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap"
    )
    assert previous_full_pillar_workstream["status"] == "paused"
    assert previous_full_pillar_workstream["authorized_next_strict_target"] == (
        QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_TARGET
    )
    assert (
        previous_full_pillar_workstream["selected_lane"]
        == "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP"
    )
    assert previous_full_pillar_workstream["selection_executes_lane"] == "no"

    previous_assumption_map_workstream = _workstream(
        payload, "qm_stat_entropy_semantics_supporting_assumption_map"
    )
    assert previous_assumption_map_workstream["status"] == "paused"
    assert previous_assumption_map_workstream["authorized_next_strict_target"] == (
        QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_RESULT_REVIEW_TARGET
    )
    assert previous_assumption_map_workstream["consumed_target"] == (
        QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_TARGET
    )
    assert previous_assumption_map_workstream["result_token"] == (
        QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_RESULT_TOKEN
    )
    assert previous_assumption_map_workstream["assumption_class_count"] == 8
    assert previous_assumption_map_workstream["map_attempts_theorem_discharge"] == "no"

    active_targets = {
        state["live_next_target"],
        current_active_workstream["authorized_next_strict_target"],
    }
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

    post_enforcement_workstream = _workstream(
        payload, "post_status_surface_enforcement_bounded_attack_selection"
    )
    assert post_enforcement_workstream["status"] == "paused"
    assert (
        post_enforcement_workstream["result_token"]
        == POST_STATUS_SURFACE_ENFORCEMENT_SELECTOR_RESULT_TOKEN
    )
    assert (
        post_enforcement_workstream["selected_next_target"]
        == FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_TARGET
    )
    assert post_enforcement_workstream["selector_executes_selected_target"] == "no"


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
    assert qft_gr["authorized_next_strict_target"] == (
        FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_TARGET
    )
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
    assert master_action["authorized_next_strict_target"] == (
        FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_TARGET
    )
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


