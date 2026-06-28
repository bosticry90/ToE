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
MR_ROW_SELECTION_TARGET = (
    "select_next_qft_gr_mathematical_regularity_row_from_repo_authoritative_inventory"
)
MR_ROW_SELECTION_CONSUMED_TARGET = (
    "review_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result"
)
MR_ROW_SELECTION_EVIDENCE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_LimitInterchangeRegularizationBoundaryAssumptionReductionAttemptResultReview.lean"
)
ACTIVE_LANE = (
    "review_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result"
)
ATTEMPT_TARGET = (
    "execute_qft_gr_candidate_source_domain_membership_assumption_reduction_attempt"
)
CANDIDATE_SOURCE_ATTEMPT_REVIEW_TARGET = (
    "review_qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_result"
)
STATE_EXPECTATION_PACKET_TARGET = (
    "prepare_qft_gr_state_expectation_domain_link_assumption_reduction_packet"
)
STATE_EXPECTATION_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_expectation_domain_link_assumption_reduction_packet_result"
)
STATE_EXPECTATION_ATTEMPT_TARGET = (
    "execute_qft_gr_state_expectation_domain_link_assumption_reduction_attempt"
)
STATE_EXPECTATION_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_expectation_domain_link_assumption_reduction_attempt_result"
)
RENORMALIZED_EXPECTATION_DOMAIN_LINK_PACKET_TARGET = (
    "prepare_qft_gr_renormalized_expectation_domain_link_assumption_reduction_packet"
)
RENORMALIZED_EXPECTATION_DOMAIN_LINK_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalized_expectation_domain_link_assumption_reduction_packet_result"
)
RENORMALIZED_EXPECTATION_DOMAIN_LINK_ATTEMPT_TARGET = (
    "execute_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt"
)
RENORMALIZED_EXPECTATION_DOMAIN_LINK_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_result"
)
CONSERVATION_FORM_SCOPE_PACKET_TARGET = (
    "prepare_qft_gr_conservation_form_scope_assumption_reduction_packet"
)
CONSERVATION_FORM_SCOPE_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_conservation_form_scope_assumption_reduction_packet_result"
)
CONSERVATION_FORM_SCOPE_ATTEMPT_TARGET = (
    "execute_qft_gr_conservation_form_scope_assumption_reduction_attempt"
)
CONSERVATION_FORM_SCOPE_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_conservation_form_scope_assumption_reduction_attempt_result"
)
METRIC_CONNECTION_SCOPE_PACKET_TARGET = (
    "prepare_qft_gr_metric_connection_scope_assumption_reduction_packet"
)
METRIC_CONNECTION_SCOPE_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_metric_connection_scope_assumption_reduction_packet_result"
)
METRIC_CONNECTION_SCOPE_ATTEMPT_TARGET = (
    "execute_qft_gr_metric_connection_scope_assumption_reduction_attempt"
)
METRIC_CONNECTION_SCOPE_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_metric_connection_scope_assumption_reduction_attempt_result"
)
OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TARGET = (
    "prepare_qft_gr_operator_domain_assumption_reduction_closeout_packet"
)
OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_operator_domain_assumption_reduction_closeout_packet_result"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_TARGET = (
    "prepare_qft_gr_renormalization_assumption_reduction_packet"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalization_assumption_reduction_packet_result"
)
RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_PACKET_TARGET = (
    "prepare_qft_gr_renormalized_stress_energy_object_assumption_reduction_packet"
)
RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalized_stress_energy_object_assumption_reduction_packet_result"
)
RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_TARGET = (
    "execute_qft_gr_renormalized_stress_energy_object_assumption_reduction_attempt"
)
RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalized_stress_energy_object_assumption_reduction_attempt_result"
)
RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_PACKET_TARGET = (
    "prepare_qft_gr_renormalization_scope_assumption_reduction_packet"
)
RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalization_scope_assumption_reduction_packet_result"
)
RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_TARGET = (
    "execute_qft_gr_renormalization_scope_assumption_reduction_attempt"
)
RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalization_scope_assumption_reduction_attempt_result"
)
RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TARGET = (
    "prepare_qft_gr_renormalized_expectation_domain_assumption_reduction_packet"
)
RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalized_expectation_domain_assumption_reduction_packet_result"
)
RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_TARGET = (
    "execute_qft_gr_renormalized_expectation_domain_assumption_reduction_attempt"
)
RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_result"
)
RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_PACKET_TARGET = (
    "prepare_qft_gr_renormalized_expectation_finiteness_assumption_reduction_packet"
)
RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalized_expectation_finiteness_assumption_reduction_packet_result"
)
RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_TARGET = (
    "execute_qft_gr_renormalized_expectation_finiteness_assumption_reduction_attempt"
)
RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalized_expectation_finiteness_assumption_reduction_attempt_result"
)
RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_TARGET = (
    "prepare_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_packet"
)
RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_packet_result"
)
RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_TARGET = (
    "execute_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt"
)
RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_result"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TARGET = (
    "prepare_qft_gr_renormalization_assumption_reduction_closeout_packet"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalization_assumption_reduction_closeout_packet_result"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TARGET = (
    "prepare_qft_gr_state_domain_assumption_reduction_packet"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_domain_assumption_reduction_packet_result"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_TARGET = (
    "prepare_qft_gr_state_domain_object_assumption_reduction_packet"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_domain_object_assumption_reduction_packet_result"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_TARGET = (
    "execute_qft_gr_state_domain_object_assumption_reduction_attempt"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_domain_object_assumption_reduction_attempt_result"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_TARGET = (
    "prepare_qft_gr_state_admissibility_boundary_assumption_reduction_packet"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_admissibility_boundary_assumption_reduction_packet_result"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_TARGET = (
    "prepare_qft_gr_state_expectation_compatibility_assumption_reduction_packet"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_expectation_compatibility_assumption_reduction_packet_result"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_TARGET = (
    "execute_qft_gr_state_expectation_compatibility_assumption_reduction_attempt"
)
CONSERVATION_TEST_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_conservation_test_packet_result"
)
A_TRANSPORT_CLOSEOUT_TARGET = (
    "prepare_toe_native_A_transport_consistency_ck_admissibility_rule_closeout"
)
A_CK_CLOSEOUT_TARGET = (
    "prepare_toe_native_A_ck_source_bridge_transport_rule_family_closeout"
)
A_CK_CLOSEOUT_SELECTED_TARGET = (
    "select_next_master_action_interaction_after_A_ck_triad"
)
PREVIOUS_LIVE_TARGET = (
    "prepare_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet"
)
A_CK_SYNTHESIS_REVIEW_TARGET = (
    "review_toe_native_A_ck_source_bridge_transport_rule_family_synthesis_packet_result"
)
A_CK_SYNTHESIS_PACKET_TARGET = (
    "prepare_toe_native_A_ck_source_bridge_transport_rule_family_synthesis_packet"
)
A_TRANSPORT_FUNCTIONAL_EMBEDDING_REVIEW_TARGET = (
    "review_toe_native_A_transport_consistency_ck_functional_embedding_packet_result"
)
A_TRANSPORT_FUNCTIONAL_EMBEDDING_PACKET_TARGET = (
    "prepare_toe_native_A_transport_consistency_ck_functional_embedding_packet"
)
A_TRANSPORT_CANDIDATE_PACKET_TARGET = (
    "prepare_toe_native_A_transport_consistency_ck_constraint_candidate_packet"
)
A_TRANSPORT_CANDIDATE_REVIEW_TARGET = (
    "review_toe_native_A_transport_consistency_ck_constraint_candidate_packet_result"
)
A_SOURCE_BRIDGE_SELECTOR_TARGET = (
    "select_next_toe_native_A_ck_constraint_family_after_source_and_bridge_admissibility"
)
A_BRIDGE_CLOSEOUT_TARGET = (
    "prepare_toe_native_A_bridge_admissibility_ck_admissibility_rule_closeout"
)
A_BRIDGE_FUNCTIONAL_EMBEDDING_REVIEW_TARGET = (
    "review_toe_native_A_bridge_admissibility_ck_functional_embedding_packet_result"
)
A_BRIDGE_FUNCTIONAL_EMBEDDING_PACKET_TARGET = (
    "prepare_toe_native_A_bridge_admissibility_ck_functional_embedding_packet"
)
A_BRIDGE_CANDIDATE_REVIEW_TARGET = (
    "review_toe_native_A_bridge_admissibility_ck_constraint_candidate_packet_result"
)
A_BRIDGE_CANDIDATE_PACKET_TARGET = (
    "prepare_toe_native_A_bridge_admissibility_ck_constraint_candidate_packet"
)
A_CK_SELECTOR_TARGET = (
    "select_next_toe_native_A_ck_constraint_family_after_source_admissibility"
)
A_SOURCE_CK_CLOSEOUT_TARGET = (
    "prepare_toe_native_A_source_admissibility_ck_admissibility_rule_closeout"
)
A_SOURCE_CK_FUNCTIONAL_EMBEDDING_REVIEW_TARGET = (
    "review_toe_native_A_source_admissibility_ck_functional_embedding_packet_result"
)
A_SOURCE_CK_FUNCTIONAL_EMBEDDING_PACKET_TARGET = (
    "prepare_toe_native_A_source_admissibility_ck_functional_embedding_packet"
)
A_SOURCE_CK_CANDIDATE_REVIEW_TARGET = (
    "review_toe_native_A_source_admissibility_ck_constraint_candidate_packet_result"
)
A_SOURCE_CK_CANDIDATE_PACKET_TARGET = (
    "prepare_toe_native_A_source_admissibility_ck_constraint_candidate_packet"
)
A_AFTER_VACUUM_SOURCE_SELECTOR_TARGET = (
    "select_next_toe_native_A_route_after_vacuum_source_admissibility"
)
A_SOURCE_RETRY_RESULT_REVIEW_TARGET = (
    "review_toe_native_A_source_admissibility_review_retry_after_vacuum_identity_result"
)
A_SOURCE_RETRY_TARGET = (
    "prepare_toe_native_A_source_admissibility_review_retry_after_vacuum_identity"
)
A_SOURCE_IDENTITY_RESULT_REVIEW_TARGET = (
    "review_toe_native_A_vacuum_source_admissibility_identity_packet_result"
)
A_SOURCE_IDENTITY_PACKET_TARGET = (
    "prepare_toe_native_A_vacuum_source_admissibility_identity_packet"
)
A_SOURCE_RESULT_REVIEW_TARGET = (
    "review_toe_native_A_source_admissibility_review_for_vacuum_stress_energy_result"
)
A_SOURCE_REVIEW_PREP_TARGET = (
    "prepare_toe_native_A_source_admissibility_review_for_vacuum_stress_energy"
)
A_AFTER_STRESS_SELECTOR_TARGET = "select_next_toe_native_A_route_after_stress_energy_route"
A_STRESS_ENERGY_REVIEW_TARGET = (
    "review_toe_native_A_stress_energy_route_under_selected_u1_policy_result"
)
A_STRESS_ENERGY_PACKET_TARGET = (
    "prepare_toe_native_A_stress_energy_route_under_selected_u1_policy"
)
A_ROUTE_SELECTOR_TARGET = "select_next_toe_native_A_route_after_vacuum_u1_variation"
A_VACUUM_RETRY_REVIEW_TARGET = (
    "review_toe_native_A_vacuum_variation_retry_under_selected_u1_policy_result"
)
A_VACUUM_RETRY_PACKET_TARGET = (
    "prepare_toe_native_A_vacuum_variation_retry_under_selected_u1_policy"
)
A_GAUGE_POLICY_TARGET = "prepare_toe_native_A_gauge_group_domain_and_current_policy_packet"
A_SURFACE_ROUTE_REVIEW_TARGET = "review_toe_native_A_surface_variation_and_source_route_result"
A_SURFACE_ROUTE_PACKET_TARGET = "prepare_toe_native_A_surface_variation_and_source_route_packet"
MASTER_ACTION_SURFACE_SELECTOR_TARGET = (
    "select_next_master_action_surface_after_phi_ck_triad"
)
PHI_CK_SOURCE_BRIDGE_TRANSPORT_CLOSEOUT_TARGET = (
    "prepare_phi_ck_source_bridge_transport_rule_family_closeout"
)
PHI_CK_SOURCE_BRIDGE_TRANSPORT_REVIEW_TARGET = (
    "review_phi_ck_source_bridge_transport_rule_family_synthesis_packet_result"
)
PHI_CK_SOURCE_BRIDGE_TRANSPORT_SYNTHESIS_PACKET_TARGET = (
    "prepare_phi_ck_source_bridge_transport_rule_family_synthesis_packet"
)
PHI_TRANSPORT_CLOSEOUT_TARGET = (
    "prepare_phi_transport_consistency_ck_admissibility_rule_closeout"
)
PHI_TRANSPORT_FUNCTIONAL_EMBEDDING_REVIEW_TARGET = (
    "review_phi_transport_consistency_ck_functional_embedding_packet_result"
)
PHI_TRANSPORT_FUNCTIONAL_EMBEDDING_PACKET_TARGET = (
    "prepare_phi_transport_consistency_ck_functional_embedding_packet"
)
PHI_TRANSPORT_CANDIDATE_REVIEW_TARGET = (
    "review_phi_transport_consistency_ck_constraint_candidate_packet_result"
)
PHI_TRANSPORT_CANDIDATE_PACKET_TARGET = (
    "prepare_phi_transport_consistency_ck_constraint_candidate_packet"
)
PHI_TRANSPORT_SELECTOR_TARGET = (
    "select_next_ck_constraint_family_after_phi_source_and_bridge_admissibility"
)
PHI_CK_SYNTHESIS_CLOSEOUT_TARGET = (
    "prepare_phi_ck_admissibility_rule_family_synthesis_closeout"
)
PHI_CK_SYNTHESIS_RESULT_REVIEW_TARGET = (
    "review_phi_ck_admissibility_rule_family_synthesis_packet_result"
)
PHI_CK_SYNTHESIS_PACKET_TARGET = (
    "prepare_phi_ck_admissibility_rule_family_synthesis_packet"
)
PHI_BRIDGE_CLOSEOUT_TARGET = (
    "prepare_phi_bridge_admissibility_ck_admissibility_rule_closeout"
)
BRIDGE_FUNCTIONAL_EMBEDDING_REVIEW_TARGET = (
    "review_phi_bridge_admissibility_ck_functional_embedding_packet_result"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_PACKET_TARGET = (
    "prepare_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_refinement"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_refinement_result"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_ATTEMPT_TARGET = (
    "execute_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_refinement"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_refinement_result"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_result"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_PACKET_TARGET = (
    "prepare_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_PACKET_TARGET = (
    "prepare_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_result"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_ATTEMPT_TARGET = (
    "execute_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_result"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RETEST_PACKET_TARGET = (
    "prepare_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RETEST_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_result"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RETEST_ATTEMPT_TARGET = (
    "execute_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RETEST_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_result"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_result"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_PACKET_TARGET = (
    "prepare_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_ATTEMPT_TARGET = (
    "execute_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement"
)
POST_RETEST_REFINEMENT_CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_result"
)
POST_RETEST_REFINEMENT_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest_result"
)
REFINEMENT_ATTEMPT_AFTER_RETEST_TARGET = (
    "execute_qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest"
)
REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_refinement_packet_after_conservation_retest_result"
)
REFINEMENT_AFTER_RETEST_PACKET_TARGET = (
    "prepare_qft_gr_minimal_working_model_refinement_packet_after_conservation_retest"
)
CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_conservation_retest_attempt_result"
)
CONSERVATION_RETEST_ATTEMPT_TARGET = (
    "execute_qft_gr_minimal_working_model_conservation_retest_attempt"
)
CONSUMED_TARGET = (
    "execute_qft_gr_minimal_working_model_conservation_test_attempt"
)
PREVIOUS_TARGET = (
    "review_qft_gr_minimal_working_model_conservation_retest_packet_result"
)
CONSERVATION_RETEST_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_conservation_retest_packet_result"
)
CONSERVATION_RETEST_PACKET_TARGET = (
    "prepare_qft_gr_minimal_working_model_conservation_retest_packet"
)
REFINEMENT_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_refinement_attempt_result"
)
CONSERVATION_TEST_PACKET_TARGET = (
    "prepare_qft_gr_minimal_working_model_conservation_test_packet"
)
LIVE_TARGET = (
    "review_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TARGET = (
    "prepare_qft_gr_state_domain_assumption_reduction_closeout_packet"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_domain_assumption_reduction_closeout_packet_result"
)
PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_candidate_source_domain_membership_assumption_reduction_packet_result"
)
LIVE_TARGET_EVIDENCE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiAGaugeSectorExchangeTheoremLinkageObligationPacket.lean"
)
DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_LimitInterchangeRegularizationBoundaryAssumptionReductionAttemptResultReview.lean"
)
DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_REPORT = (
    "formal/docs/release/"
    "QFT_GR_LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_ASSUMPTION_REDUCTION_"
    "ATTEMPT_RESULT_REVIEW_20260609_v0.json"
)
DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_TOKEN = (
    "QFT_GR_LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_ASSUMPTION_REDUCTION_"
    "ATTEMPT_RESULT_REVIEW_ACCEPTS_REDUCED_MR_ASSUMP_004_AND_AUTHORIZES_"
    "NEXT_MATHEMATICAL_REGULARITY_ROW_SELECTION_ONLY"
)
DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_TOOL = (
    "formal/python/tools/"
    "qft_gr_limit_interchange_regularization_boundary_assumption_reduction_"
    "attempt_result_review_report.py"
)
DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_CLASSIFICATION = (
    "qft_gr_limit_interchange_regularization_boundary_assumption_reduction_"
    "attempt_result_review_accepts_reduced_mr_assump_004_and_authorizes_next_"
    "mathematical_regularity_row_selection_only"
)
DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_REVIEW_CLASSIFICATION = (
    "qft_gr_limit_interchange_regularization_boundary_assumption_reduction_"
    "attempt_result_review_accepts_reduced_mr_assump_004_and_authorizes_next_"
    "mathematical_regularity_row_selection_only"
)
DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_REVIEW_ID = (
    "QFT_GR_LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_ASSUMPTION_REDUCTION_"
    "ATTEMPT_RESULT_REVIEW_v0"
)
DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_REVIEW_SCOPE = (
    "SELECT_NEXT_QFT_GR_MATHEMATICAL_REGULARITY_ROW_FROM_REPO_AUTHORITATIVE_"
    "INVENTORY_ONLY_NO_CONSERVATION_PROOF_OBJECT_OR_QFT_GR_SEAM_CLOSURE"
)
RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_RenormalizationOperatorDomainCompatibilityAssumptionReductionAttempt.lean"
)
RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_REPORT = (
    "formal/docs/release/"
    "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
    "REDUCTION_ATTEMPT_20260606_v0.json"
)
RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_TOOL = (
    "formal/python/tools/"
    "qft_gr_renormalization_operator_domain_compatibility_assumption_"
    "reduction_attempt_report.py"
)
RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_TOKEN = (
    "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
    "REDUCTION_ATTEMPT_EXECUTED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_RenormalizationOperatorDomainCompatibilityAssumptionReductionAttemptResultReview.lean"
)
RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
    "REDUCTION_ATTEMPT_RESULT_REVIEW_20260606_v0.json"
)
RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_renormalization_operator_domain_compatibility_assumption_"
    "reduction_attempt_result_review_report.py"
)
RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOKEN = (
    "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
    "REDUCTION_ATTEMPT_RESULT_REVIEW_ACCEPTS_REDUCED_OPERATOR_DOMAIN_"
    "COMPATIBILITY_AND_AUTHORIZES_RENORMALIZATION_ASSUMPTION_REDUCTION_"
    "CLOSEOUT_PREPARATION_ONLY"
)
RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_"
    "attempt_result_review_accepts_reduced_operator_domain_compatibility_and_"
    "authorizes_renormalization_assumption_reduction_closeout_preparation_only"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_RenormalizationAssumptionReductionCloseoutPacket.lean"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_REPORT = (
    "formal/docs/release/"
    "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_20260606_v0.json"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TOOL = (
    "formal/python/tools/"
    "qft_gr_renormalization_assumption_reduction_closeout_packet_report.py"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TOKEN = (
    "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_PREPARED_"
    "WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_CLASSIFICATION = (
    "qft_gr_renormalization_assumption_reduction_closeout_packet_prepared_"
    "with_no_conservation_witness_or_seam_closure"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_RenormalizationAssumptionReductionCloseoutPacketResultReview.lean"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_"
    "20260606_v0.json"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_renormalization_assumption_reduction_closeout_packet_result_review_report.py"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TOKEN = (
    "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_RESULT_REVIEW_"
    "ACCEPTS_RENORMALIZATION_ROWS_AND_AUTHORIZES_NEXT_ASSUMPTION_FAMILY_"
    "SELECTION_ONLY"
)
RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_renormalization_assumption_reduction_closeout_result_review_"
    "accepts_renormalization_rows_and_authorizes_next_assumption_family_"
    "selection_only"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateDomainAssumptionReductionPacket.lean"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_20260607_v0.json"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_domain_assumption_reduction_packet_report.py"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TOKEN = (
    "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_PREPARED_WITH_NO_"
    "CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_CLASSIFICATION = (
    "qft_gr_state_domain_assumption_reduction_packet_prepared_with_no_"
    "conservation_witness_or_seam_closure"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateDomainAssumptionReductionPacketResultReview.lean"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_"
    "20260607_v0.json"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_domain_assumption_reduction_packet_result_review_report.py"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOKEN = (
    "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "PACKET_AND_AUTHORIZES_BOUNDED_STATE_DOMAIN_ROW_SELECTION_ONLY"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_state_domain_assumption_reduction_packet_result_review_accepts_"
    "packet_and_authorizes_bounded_state_domain_row_selection_only"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateDomainObjectAssumptionReductionPacket.lean"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_20260607_v0.json"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_domain_object_assumption_reduction_packet_report.py"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_TOKEN = (
    "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_PREPARED_WITH_NO_"
    "CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_CLASSIFICATION = (
    "qft_gr_state_domain_object_assumption_reduction_packet_prepared_with_no_"
    "conservation_witness_or_seam_closure"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_PENDING_CLASSIFICATION = (
    "qft_gr_state_domain_object_assumption_reduction_packet_result_review_pending"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateDomainObjectAssumptionReductionPacketResultReview.lean"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_"
    "20260607_v0.json"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_domain_object_assumption_reduction_packet_result_review_report.py"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOKEN = (
    "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_REDUCTION_ATTEMPT_ONLY"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_state_domain_object_assumption_reduction_packet_result_review_"
    "accepts_packet_and_authorizes_bounded_reduction_attempt_only"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateDomainObjectAssumptionReductionAttempt.lean"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_20260607_v0.json"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_domain_object_assumption_reduction_attempt_report.py"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_TOKEN = (
    "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_EXECUTED_WITH_NO_"
    "CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_CLASSIFICATION = (
    "qft_gr_state_domain_object_assumption_reduced_pending_result_review"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT = (
    "SD-ASSUMP-001-state_domain_object_contract_v0"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT_STATUS = (
    "bounded_repo_local_state_domain_object_contract_pending_result_review_not_"
    "state_admissibility_source_admissibility_or_conservation_discharge"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateDomainObjectAssumptionReductionAttemptResultReview.lean"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_"
    "20260607_v0.json"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_domain_object_assumption_reduction_attempt_result_review_report.py"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOKEN = (
    "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_"
    "ACCEPTS_REDUCED_STATE_DOMAIN_OBJECT_AND_AUTHORIZES_NEXT_STATE_DOMAIN_ROW_"
    "SELECTION_ONLY"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_state_domain_object_assumption_reduction_attempt_result_review_"
    "accepts_reduced_state_domain_object_and_authorizes_next_state_domain_row_"
    "selection_only"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_ACCEPTED_ROW = (
    "SD-ASSUMP-001-state_domain_object"
)
STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_NEXT_ROW = (
    "SD-ASSUMP-002-state_admissibility_boundary"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateAdmissibilityBoundaryAssumptionReductionPacket.lean"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_"
    "20260607_v0.json"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_admissibility_boundary_assumption_reduction_packet_report.py"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_TOKEN = (
    "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_PREPARED_"
    "WITH_NO_SOURCE_ADMISSIBILITY_OR_SEAM_CLOSURE"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_CLASSIFICATION = (
    "qft_gr_state_admissibility_boundary_assumption_reduction_packet_prepared_"
    "with_no_source_admissibility_or_seam_closure"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_PENDING_CLASSIFICATION = (
    "qft_gr_state_admissibility_boundary_assumption_reduction_packet_result_review_pending"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateAdmissibilityBoundaryAssumptionReductionPacketResultReview.lean"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_"
    "RESULT_REVIEW_20260607_v0.json"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_admissibility_boundary_assumption_reduction_packet_"
    "result_review_report.py"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOKEN = (
    "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_"
    "RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_REDUCTION_"
    "ATTEMPT_ONLY"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_state_admissibility_boundary_assumption_reduction_packet_"
    "result_review_accepts_packet_and_authorizes_bounded_reduction_attempt_only"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_TARGET = (
    "execute_qft_gr_state_admissibility_boundary_assumption_reduction_attempt"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_admissibility_boundary_assumption_reduction_attempt_result"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateAdmissibilityBoundaryAssumptionReductionAttempt.lean"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_"
    "20260607_v0.json"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_admissibility_boundary_assumption_reduction_attempt_report.py"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_TOKEN = (
    "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_"
    "EXECUTED_WITH_NO_SOURCE_ADMISSIBILITY_OR_SEAM_CLOSURE"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_CLASSIFICATION = (
    "qft_gr_state_admissibility_boundary_assumption_reduced_pending_result_review"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT = (
    "SD-ASSUMP-002-state_admissibility_boundary_contract_v0"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT_STATUS = (
    "bounded_repo_local_state_admissibility_boundary_contract_pending_result_"
    "review_not_state_admissibility_source_admissibility_or_conservation_"
    "discharge"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_PENDING_CLASSIFICATION = (
    "qft_gr_state_admissibility_boundary_assumption_reduction_attempt_result_review_pending"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateAdmissibilityBoundaryAssumptionReductionAttemptResultReview.lean"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_"
    "RESULT_REVIEW_20260607_v0.json"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_admissibility_boundary_assumption_reduction_attempt_"
    "result_review_report.py"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOKEN = (
    "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_"
    "RESULT_REVIEW_ACCEPTS_REDUCED_STATE_ADMISSIBILITY_BOUNDARY_AND_"
    "AUTHORIZES_NEXT_STATE_DOMAIN_ROW_SELECTION_ONLY"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_state_admissibility_boundary_assumption_reduction_attempt_"
    "result_review_accepts_reduced_state_admissibility_boundary_and_"
    "authorizes_next_state_domain_row_selection_only"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_ACCEPTED_ROW = (
    "SD-ASSUMP-002-state_admissibility_boundary"
)
STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_NEXT_ROW = (
    "SD-ASSUMP-003-state_expectation_compatibility"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateExpectationCompatibilityAssumptionReductionPacket.lean"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_"
    "20260607_v0.json"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_expectation_compatibility_assumption_reduction_packet_report.py"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_TOKEN = (
    "QFT_GR_STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_"
    "PREPARED_WITH_NO_SOURCE_ADMISSIBILITY_OR_SEAM_CLOSURE"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_CLASSIFICATION = (
    "qft_gr_state_expectation_compatibility_assumption_reduction_packet_"
    "prepared_with_no_source_admissibility_or_seam_closure"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_SELECTED_ROW = (
    "SD-ASSUMP-003-state_expectation_compatibility"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateExpectationCompatibilityAssumptionReductionPacketResultReview.lean"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_"
    "RESULT_REVIEW_20260607_v0.json"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_expectation_compatibility_assumption_reduction_packet_"
    "result_review_report.py"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOKEN = (
    "QFT_GR_STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_"
    "RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_REDUCTION_ATTEMPT_ONLY"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_state_expectation_compatibility_assumption_reduction_packet_"
    "result_review_accepts_packet_and_authorizes_bounded_reduction_attempt_only"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateExpectationCompatibilityAssumptionReductionAttempt.lean"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_"
    "20260607_v0.json"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_expectation_compatibility_assumption_reduction_attempt_report.py"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_TOKEN = (
    "QFT_GR_STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_"
    "EXECUTED_WITH_NO_SOURCE_ADMISSIBILITY_OR_SEAM_CLOSURE"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_CLASSIFICATION = (
    "qft_gr_state_expectation_compatibility_assumption_reduced_pending_result_review"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT = (
    "SD-ASSUMP-003-state_expectation_compatibility_contract_v0"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT_STATUS = (
    "bounded_repo_local_state_expectation_compatibility_contract_pending_result_"
    "review_not_state_admissibility_source_admissibility_or_conservation_discharge"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateExpectationCompatibilityAssumptionReductionAttemptResultReview.lean"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_"
    "RESULT_REVIEW_20260607_v0.json"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_expectation_compatibility_assumption_reduction_attempt_"
    "result_review_report.py"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_expectation_compatibility_assumption_reduction_attempt_result"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOKEN = (
    "QFT_GR_STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_"
    "RESULT_REVIEW_ACCEPTS_REDUCED_STATE_EXPECTATION_COMPATIBILITY_AND_"
    "AUTHORIZES_STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PREPARATION_ONLY"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_state_expectation_compatibility_assumption_reduction_attempt_"
    "result_review_accepts_reduced_state_expectation_compatibility_and_"
    "authorizes_state_domain_assumption_reduction_closeout_preparation_only"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateDomainAssumptionReductionCloseoutPacket.lean"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_20260608_v0.json"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_domain_assumption_reduction_closeout_packet_report.py"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_ACCEPTED_ROW = (
    "SD-ASSUMP-003-state_expectation_compatibility"
)
STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_NO_NEXT_ROW = (
    "none_state_domain_inventory_exhausted_after_SD-ASSUMP-003-state_expectation_compatibility"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TARGET_KIND = (
    "qft_gr_state_domain_assumption_reduction_closeout_packet_preparation"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_KIND = (
    "qft_gr_state_domain_assumption_reduction_closeout_packet_result_review"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TOKEN = (
    "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_PREPARED_"
    "WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_CLASSIFICATION = (
    "qft_gr_state_domain_assumption_reduction_closeout_packet_prepared_"
    "with_no_conservation_witness_or_seam_closure"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateDomainAssumptionReductionCloseoutPacketResultReview.lean"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_"
    "20260608_v0.json"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_domain_assumption_reduction_closeout_packet_result_review_report.py"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TOKEN = (
    "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_"
    "ACCEPTS_STATE_DOMAIN_FAMILY_CLOSEOUT_AND_AUTHORIZES_NEXT_ASSUMPTION_"
    "FAMILY_SELECTION_ONLY"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_state_domain_assumption_reduction_closeout_packet_result_review_"
    "accepts_state_domain_family_closeout_and_authorizes_next_assumption_"
    "family_selection_only"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_TARGET_KIND = (
    "qft_gr_mathematical_regularity_assumption_reduction_packet_preparation"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET_KIND = (
    "qft_gr_mathematical_regularity_assumption_reduction_packet_result_review"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_ID = (
    "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_v0"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_PENDING_REVIEW_DECISION = (
    "mathematical_regularity_assumption_reduction_packet_prepared_pending_result_review"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_MathematicalRegularityAssumptionReductionPacket.lean"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_REPORT = (
    "formal/docs/release/"
    "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_"
    "20260608_v0.json"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_TOOL = (
    "formal/python/tools/"
    "qft_gr_mathematical_regularity_assumption_reduction_packet_report.py"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_TOKEN = (
    "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_PREPARED_"
    "WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_CLASSIFICATION = (
    "qft_gr_mathematical_regularity_assumption_reduction_packet_prepared_"
    "with_no_conservation_witness_or_seam_closure"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_MathematicalRegularityAssumptionReductionPacketResultReview.lean"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_"
    "RESULT_REVIEW_20260608_v0.json"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_mathematical_regularity_assumption_reduction_packet_"
    "result_review_report.py"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOKEN = (
    "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_"
    "RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_MR_ASSUMP_001_"
    "ATTEMPT_ONLY"
)
MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_mathematical_regularity_assumption_reduction_packet_result_review_"
    "accepts_packet_and_authorizes_bounded_mr_assump_001_attempt_only"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_TARGET_KIND = (
    "qft_gr_derivative_exchange_regular_boundary_assumption_reduction_attempt_execution"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET_KIND = (
    "qft_gr_derivative_exchange_regular_boundary_assumption_reduction_attempt_result_review"
)
WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_TARGET_KIND = (
    "qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet_preparation"
)
WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet_result"
)
WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET_KIND = (
    "qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet_result_review"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_DerivativeExchangeRegularBoundaryAssumptionReductionAttempt.lean"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_REPORT = (
    "formal/docs/release/"
    "QFT_GR_DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_"
    "20260608_v0.json"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_TOOL = (
    "formal/python/tools/"
    "qft_gr_derivative_exchange_regular_boundary_assumption_reduction_attempt_report.py"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_TOKEN = (
    "QFT_GR_DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_"
    "EXECUTED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_CLASSIFICATION = (
    "qft_gr_derivative_exchange_regular_boundary_assumption_reduced_pending_result_review"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT = (
    "MR-ASSUMP-001-derivative_exchange_regular_boundary_contract_v0"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT_STATUS = (
    "bounded_repo_local_derivative_exchange_regular_boundary_contract_pending_"
    "result_review_not_global_derivative_exchange_regularity_discharge"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_ID = (
    "QFT_GR_DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_"
    "RESULT_REVIEW_v0"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_PENDING_CLASSIFICATION = (
    "qft_gr_derivative_exchange_regular_boundary_assumption_reduction_attempt_result_review_pending"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_DerivativeExchangeRegularBoundaryAssumptionReductionAttemptResultReview.lean"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_"
    "RESULT_REVIEW_20260608_v0.json"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_derivative_exchange_regular_boundary_assumption_reduction_attempt_"
    "result_review_report.py"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOKEN = (
    "QFT_GR_DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_"
    "RESULT_REVIEW_ACCEPTS_REDUCED_MR_ASSUMP_001_AND_AUTHORIZES_NEXT_"
    "MATHEMATICAL_REGULARITY_ROW_SELECTION_ONLY"
)
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_derivative_exchange_regular_boundary_assumption_reduction_attempt_"
    "result_review_accepts_reduced_mr_assump_001_and_authorizes_next_"
    "mathematical_regularity_row_selection_only"
)
WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_WeakStrongConservationComparisonScopeAssumptionReductionPacket.lean"
)
WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_REPORT = (
    "formal/docs/release/"
    "QFT_GR_WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_"
    "PACKET_20260608_v0.json"
)
WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_TOOL = (
    "formal/python/tools/"
    "qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_"
    "packet_report.py"
)
WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_TOKEN = (
    "QFT_GR_WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_"
    "PACKET_PREPARED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_CLASSIFICATION = (
    "qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_"
    "packet_prepared_with_no_conservation_witness_or_seam_closure"
)
WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_SELECTED_ROW = (
    "MR-ASSUMP-002-weak_strong_conservation_comparison_scope"
)
WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_PENDING_CLASSIFICATION = (
    "qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet_result_review_accepts_packet_and_authorizes_bounded_mr_assump_002_attempt_only"
)
RN002_ATTEMPT_RESULT_REVIEW_EVIDENCE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_RenormalizationScopeAssumptionReductionAttemptResultReview.lean"
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
    assert state["previous_live_next_target"] == PREVIOUS_LIVE_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == str(
        LIVE_TARGET_EVIDENCE_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert payload["PREVIOUS_LIVE_NEXT_TARGET_v0"] == PREVIOUS_LIVE_TARGET
    assert payload["CURRENT_LIVE_NEXT_TARGET_v0"] == LIVE_TARGET
    assert payload["CURRENT_LIVE_TARGET_EVIDENCE_v0"] == str(
        LIVE_TARGET_EVIDENCE_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert payload["CURRENT_LIVE_TARGET_REPORT_v0"] == (
        "formal/docs/release/"
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_"
        "20260628_v0.json"
    )
    assert payload["CURRENT_LIVE_TARGET_OUTCOME_v0"] == (
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_"
        "GAUGE_EXCHANGE_ROUTE_SCOPED_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
    )
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

    a_surface_route_packet_result = (
        "TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_PREPARED_RAW_"
        "GAUGE_VARIATION_RECORDED_SOURCE_ROUTE_BLOCKED_PENDING_GAUGE_GROUP_"
        "CURRENT_DOMAIN_AND_CK_CONTENT"
    )
    a_surface_route_review_result = (
        "TOE_NATIVE_A_SURFACE_VARIATION_ROUTE_RESULT_REVIEW_ACCEPTS_RAW_"
        "GAUGE_ROUTE_AND_BLOCKS_NATIVE_DERIVATION_PENDING_GAUGE_GROUP_"
        "CURRENT_DOMAIN_AND_CK_CONTENT"
    )
    a_gauge_policy_packet_result = (
        "TOE_NATIVE_A_GAUGE_GROUP_DOMAIN_AND_CURRENT_POLICY_PACKET_PREPARED_"
        "U1_ROUTE_SELECTED_CURRENT_DERIVATION_STILL_BLOCKED"
    )
    a_vacuum_variation_retry_packet_result = (
        "TOE_NATIVE_A_VACUUM_VARIATION_RETRY_UNDER_SELECTED_U1_POLICY_PACKET_PREPARED_"
        "VACUUM_GAUGE_VARIATION_ROUTE_CONSTRUCTED_NO_CURRENT_DERIVATION_OR_EM_CLOSURE"
    )
    a_vacuum_variation_retry_review_result = (
        "TOE_NATIVE_A_VACUUM_VARIATION_RETRY_RESULT_REVIEW_ACCEPTS_VACUUM_U1_"
        "GAUGE_ROUTE_NO_CURRENT_DERIVATION_OR_EM_CLOSURE"
    )
    a_route_selection_result = (
        "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_U1_VARIATION_SELECTS_STRESS_"
        "ENERGY_ROUTE_NO_CURRENT_DERIVATION_OR_EM_CLOSURE"
    )
    a_stress_energy_packet_result = (
        "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_PACKET_PREPARED_"
        "GAUGE_STRESS_ENERGY_ROUTE_RECORDED_NO_SOURCE_ADMISSIBILITY_OR_EM_CLOSURE"
    )
    a_stress_energy_review_result = (
        "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_RESULT_REVIEW_ACCEPTS_GAUGE_STRESS_"
        "ENERGY_ROUTE_NO_SOURCE_ADMISSIBILITY_OR_EM_CLOSURE"
    )
    a_after_stress_selection_result = (
        "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_STRESS_ENERGY_ROUTE_SELECTS_VACUUM_"
        "SOURCE_ADMISSIBILITY_REVIEW_NO_CURRENT_DERIVATION_OR_EM_CLOSURE"
    )

    a_source_review_prep_result = (
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_FOR_VACUUM_STRESS_ENERGY_"
        "PREPARED_VACUUM_GAUGE_SOURCE_ADMISSIBILITY_REVIEW_ON_SHELL_NO_CURRENT_"
        "OR_EM_CLOSURE"
    )
    a_source_result_review_result = (
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RESULT_REVIEW_ACCEPTS_PREPARED_"
        "ON_SHELL_VACUUM_GAUGE_SOURCE_TEST_NO_SOURCE_ADMISSIBILITY_OR_EM_CLOSURE"
    )
    a_source_identity_result = (
        "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_PACKET_PREPARED_"
        "ON_SHELL_DIVERGENCE_IDENTITY_CONSTRUCTED_NO_CURRENT_OR_EM_CLOSURE"
    )
    a_source_identity_result_review_result = (
        "TOE_NATIVE_A_VACUUM_SOURCE_ADMISSIBILITY_IDENTITY_RESULT_REVIEW_ACCEPTS_"
        "ON_SHELL_DIVERGENCE_IDENTITY_NO_CURRENT_OR_EM_CLOSURE"
    )
    a_source_retry_result = (
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_ACCEPTS_LOCAL_ON_SHELL_"
        "VACUUM_GAUGE_SOURCE_ROUTE_NO_CURRENT_OR_EM_CLOSURE"
    )
    a_source_retry_result_review_result = (
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_REVIEW_RETRY_RESULT_REVIEW_ACCEPTS_"
        "LOCAL_ON_SHELL_VACUUM_GAUGE_SOURCE_ROUTE_NO_CURRENT_OR_EM_CLOSURE"
    )
    a_after_vacuum_source_selection_result = (
        "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_SOURCE_ADMISSIBILITY_SELECTS_"
        "SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_NO_CURRENT_OR_EM_CLOSURE"
    )
    a_source_ck_candidate_packet_result = (
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_PREPARED_"
        "A_SOURCE_ADMISSIBILITY_RULE_RECORDED_AS_VACUUM_CONSERVATION_RESIDUAL_"
        "NO_ACTION_VARIATION_OR_PROMOTION"
    )
    a_source_ck_candidate_review_result = (
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_RESULT_REVIEW_"
        "ACCEPTS_VACUUM_GAUGE_CONSERVATION_RESIDUAL_CANDIDATE_"
        "NO_FUNCTIONALIZATION_OR_PROMOTION"
    )
    a_source_ck_functional_embedding_result = (
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
        "PREPARED_OPTIONS_RECORDED_ADMISSIBILITY_ONLY_ROUTE_SELECTED_"
        "NO_ACTION_VARIATION"
    )
    a_source_ck_functional_embedding_review_result = (
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_RESULT_REVIEW_"
        "ACCEPTS_ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_OR_PROMOTION"
    )

    a_source_ck_closeout_result = (
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSED_AS_"
        "VACUUM_GAUGE_SOURCE_RULE_NO_ACTION_VARIATION_OR_PROMOTION"
    )

    a_ck_selector_result = (
        "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY_"
        "SELECTS_BRIDGE_ADMISSIBILITY_NO_CURRENT_OR_EM_CLOSURE"
    )

    a_bridge_candidate_packet_result = (
        "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_PREPARED_"
        "A_BRIDGE_ROUTE_CONSISTENCY_RULE_RECORDED_NO_CURRENT_OR_EM_CLOSURE"
    )
    a_bridge_candidate_review_result = (
        "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_RESULT_REVIEW_"
        "ACCEPTS_VACUUM_U1_ROUTE_CONSISTENCY_CANDIDATE_"
        "NO_FUNCTIONALIZATION_OR_PROMOTION"
    )
    a_bridge_functional_embedding_result = (
        "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
        "PREPARED_OPTIONS_RECORDED_ADMISSIBILITY_ONLY_ROUTE_SELECTED_"
        "NO_ACTION_VARIATION"
    )
    a_bridge_functional_embedding_review_result = (
        "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_"
        "RESULT_REVIEW_ACCEPTS_ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_"
        "OR_PROMOTION"
    )
    a_bridge_closeout_result = (
        "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSED_AS_"
        "VACUUM_U1_ROUTE_CONSISTENCY_RULE_NO_ACTION_VARIATION_OR_PROMOTION"
    )

    a_source_bridge_selector_result = (
        "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_AND_BRIDGE_"
        "ADMISSIBILITY_SELECTS_TRANSPORT_CONSISTENCY_NO_CURRENT_OR_EM_CLOSURE"
    )

    a_transport_candidate_packet_result = (
        "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_"
        "PREPARED_A_TRANSPORT_STABILITY_RULE_RECORDED_NO_CURRENT_OR_EM_CLOSURE"
    )
    a_transport_candidate_review_result = (
        "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_RESULT_REVIEW_"
        "ACCEPTS_VACUUM_U1_DERIVATION_CHAIN_STABILITY_CANDIDATE_"
        "NO_FUNCTIONALIZATION_OR_PROMOTION"
    )
    a_transport_functional_embedding_packet_result = (
        "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
        "PREPARED_OPTIONS_RECORDED_ADMISSIBILITY_ONLY_ROUTE_SELECTED_"
        "NO_ACTION_VARIATION"
    )
    a_transport_functional_embedding_short_result = (
        "OPTIONS_RECORDED_ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
    )
    a_transport_functional_embedding_review_result = (
        "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_"
        "RESULT_REVIEW_ACCEPTS_ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_"
        "OR_PROMOTION"
    )
    a_transport_closeout_result = (
        "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_ADMISSIBILITY_RULE_CLOSED_AS_"
        "VACUUM_U1_DERIVATION_CHAIN_STABILITY_RULE_NO_ACTION_VARIATION_OR_PROMOTION"
    )
    a_ck_synthesis_result = (
        "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_PACKET_"
        "PREPARED_THREE_ADMISSIBILITY_RULES_SYNTHESIZED_NO_CURRENT_OR_EM_CLOSURE"
    )
    a_ck_synthesis_review_result = (
        "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_"
        "ACCEPTS_THREE_RULE_VACUUM_U1_ADMISSIBILITY_FAMILY_NO_CURRENT_OR_EM_CLOSURE"
    )

    a_ck_closeout_result = (
        "TOE_NATIVE_A_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_CLOSED_AS_THREE_RULE_"
        "VACUUM_U1_ADMISSIBILITY_FAMILY_NO_CURRENT_OR_EM_CLOSURE"
    )

    psi_a_policy_result = (
        "TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_ROUTE_POLICY_PACKET_PREPARED_"
        "INTERACTION_POLICY_SELECTED_CURRENT_AND_EXCHANGE_DERIVATION_STILL_BLOCKED"
    )
    psi_a_obligation_result = (
        "TOE_NATIVE_PSI_A_U1_CURRENT_AND_EXCHANGE_DERIVATION_OBLIGATION_PACKET_"
        "PREPARED_CURRENT_DERIVATION_AND_EXCHANGE_PROOF_OBLIGATIONS_INDEXED_"
        "NO_DERIVATION_OR_EM_QFT_CLOSURE"
    )
    psi_a_action_block_result = (
        "TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_PACKET_PREPARED_"
        "ACTION_BLOCK_DEFINED_CURRENT_AND_EXCHANGE_DERIVATION_STILL_BLOCKED"
    )
    psi_a_action_block_review_result = (
        "TOE_NATIVE_PSI_A_U1_INTERACTION_ACTION_BLOCK_DEFINITION_RESULT_REVIEW_"
        "ACCEPTS_ACTION_BLOCK_DEFINITION_NO_CURRENT_OR_EXCHANGE_DERIVATION"
    )
    psi_a_current_derivation_result = (
        "TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_PACKET_PREPARED_"
        "A_VARIATION_CURRENT_CANDIDATE_RECORDED_NO_SOURCED_MAXWELL_CLOSURE_"
        "OR_EXCHANGE_PROOF"
    )
    psi_a_current_derivation_review_result = (
        "TOE_NATIVE_PSI_A_U1_CURRENT_DERIVATION_FROM_A_VARIATION_RESULT_REVIEW_"
        "ACCEPTS_A_VARIATION_CURRENT_CANDIDATE_NO_CURRENT_CONSERVATION_OR_"
        "EXCHANGE_PROOF"
    )

    psi_a_current_conservation_obligation_result = (
        "TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_OBLIGATION_PACKET_PREPARED_"
        "CURRENT_CONSERVATION_REQUIREMENTS_INDEXED_NO_CONSERVATION_PROOF_"
        "OR_EM_QFT_CLOSURE"
    )
    psi_a_psi_variation_dirac_route_result = (
        "TOE_NATIVE_PSI_A_U1_PSI_VARIATION_DIRAC_ROUTE_PACKET_PREPARED_"
        "PSI_EQUATION_ROUTE_RECORDED_ADJOINT_AND_CONSERVATION_STILL_BLOCKED"
    )
    psi_a_adjoint_dirac_route_result = (
        "TOE_NATIVE_PSI_A_U1_ADJOINT_DIRAC_ROUTE_PACKET_PREPARED_"
        "ADJOINT_EQUATION_ROUTE_RECORDED_CURRENT_CONSERVATION_STILL_BLOCKED"
    )
    psi_a_current_conservation_pair_result = (
        "TOE_NATIVE_PSI_A_U1_CURRENT_CONSERVATION_FROM_DIRAC_PAIR_PACKET_PREPARED_"
        "CURRENT_CONSERVATION_ROUTE_CONSTRUCTED_NO_SOURCED_MAXWELL_CLOSURE_"
        "OR_EXCHANGE_PROOF"
    )
    psi_a_sourced_maxwell_route_result = (
        "TOE_NATIVE_PSI_A_U1_SOURCED_MAXWELL_ROUTE_PACKET_PREPARED_"
        "SOURCED_GAUGE_ROUTE_RECORDED_NO_MAXWELL_CLOSURE_OR_EXCHANGE_PROOF"
    )
    psi_a_stress_energy_exchange_obligation_result = (
        "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_AND_EXCHANGE_OBLIGATION_PACKET_"
        "PREPARED_STRESS_ENERGY_AND_EXCHANGE_REQUIREMENTS_INDEXED_"
        "NO_EXCHANGE_PROOF_OR_EM_QFT_CLOSURE"
    )
    psi_a_stress_energy_definition_policy_result = (
        "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_PACKET_PREPARED_"
        "STRESS_ENERGY_POLICY_INDEXED_NO_EXCHANGE_PROOF_OR_EM_QFT_CLOSURE"
    )
    psi_a_stress_energy_definition_policy_review_result = (
        "TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_"
        "ACCEPTS_STRESS_ENERGY_POLICY_NO_EXCHANGE_PROOF_OR_EM_QFT_CLOSURE"
    )
    psi_a_gauge_sector_exchange_route_packet_result = (
        "TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_PACKET_PREPARED_"
        "GAUGE_SECTOR_EXCHANGE_ROUTE_CONSTRUCTED_NO_MATTER_EXCHANGE_OR_"
        "TOTAL_CONSERVATION_PROOF"
    )
    psi_a_gauge_sector_exchange_route_review_result = (
        "TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_"
        "ACCEPTS_GAUGE_SECTOR_EXCHANGE_ROUTE_NO_MATTER_EXCHANGE_OR_"
        "TOTAL_CONSERVATION_PROOF"
    )
    psi_a_matter_sector_exchange_route_packet_result = (
        "TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_PACKET_PREPARED_"
        "MATTER_SECTOR_EXCHANGE_ROUTE_CONSTRUCTED_NO_TOTAL_CONSERVATION_OR_"
        "CEXCHANGE_CLOSURE"
    )
    psi_a_matter_sector_exchange_route_review_result = (
        "TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_"
        "ACCEPTS_MATTER_SECTOR_EXCHANGE_ROUTE_NO_TOTAL_CONSERVATION_OR_"
        "CEXCHANGE_CLOSURE"
    )
    psi_a_total_stress_energy_conservation_route_packet_result = (
        "TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_PACKET_PREPARED_"
        "TOTAL_CONSERVATION_ROUTE_CONSTRUCTED_NO_CEXCHANGE_CLOSEOUT_OR_EM_QFT_CLOSURE"
    )
    psi_a_total_stress_energy_conservation_route_review_result = (
        "TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_RESULT_REVIEW_"
        "ACCEPTS_TOTAL_CONSERVATION_ROUTE_NO_CEXCHANGE_CLOSEOUT_OR_EM_QFT_CLOSURE"
    )
    psi_a_cexchange_constraint_candidate_packet_result = (
        "TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_PACKET_PREPARED_"
        "TOTAL_EXCHANGE_CONSERVATION_RESIDUAL_CANDIDATE_RECORDED_NO_"
        "FUNCTIONALIZATION_OR_EM_QFT_CLOSURE"
    )
    psi_a_cexchange_constraint_candidate_result_review_result = (
        "TOE_NATIVE_PSI_A_U1_CEXCHANGE_CONSTRAINT_CANDIDATE_RESULT_REVIEW_"
        "ACCEPTS_TOTAL_EXCHANGE_CONSERVATION_RESIDUAL_CANDIDATE_NO_"
        "FUNCTIONALIZATION_OR_EM_QFT_CLOSURE"
    )
    psi_a_cexchange_functional_embedding_packet_result = (
        "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_PREPARED_"
        "OPTIONS_RECORDED_ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
    )
    psi_a_cexchange_functional_embedding_result_review_result = (
        "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_RESULT_REVIEW_"
        "ACCEPTS_ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_OR_EM_QFT_CLOSURE"
    )
    psi_a_cexchange_admissibility_rule_closeout_result = (
        "TOE_NATIVE_PSI_A_U1_CEXCHANGE_ADMISSIBILITY_RULE_CLOSED_AS_"
        "INTERACTION_EXCHANGE_BALANCE_RULE_NO_ACTION_VARIATION_OR_EM_QFT_CLOSURE"
    )
    psi_a_interaction_exchange_rule_family_synthesis_packet_result = (
        "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_PACKET_"
        "PREPARED_CURRENT_SOURCE_EXCHANGE_AND_TOTAL_CONSERVATION_ROUTES_SYNTHESIZED_"
        "NO_EM_QFT_OR_CK_ACTION_CLOSURE"
    )
    psi_a_interaction_exchange_rule_family_synthesis_result_review_result = (
        "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_"
        "ACCEPTS_CURRENT_SOURCE_EXCHANGE_AND_TOTAL_CONSERVATION_SYNTHESIS_"
        "NO_EM_QFT_OR_CK_ACTION_CLOSURE"
    )
    psi_a_interaction_exchange_rule_family_closeout_result = (
        "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSED_AS_BOUNDED_"
        "CURRENT_SOURCE_AND_EXCHANGE_ADMISSIBILITY_FAMILY_"
        "NO_EM_QFT_OR_CK_ACTION_CLOSURE"
    )
    psi_a_interaction_exchange_rule_family_closeout_result_review_result = (
        "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_RESULT_REVIEW_"
        "ACCEPTS_BOUNDED_CURRENT_SOURCE_AND_EXCHANGE_ADMISSIBILITY_FAMILY_"
        "NO_EM_QFT_OR_CK_ACTION_CLOSURE"
    )

    cexchange_theorem_linkage_attempt_result_review_result = (
        "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_RESULT_REVIEW_"
        "ACCEPTS_DEFINITIONAL_LINKAGE_ROUTE_PREPARATION_NO_THEOREM_DISCHARGE_OR_"
        "CK_RULE_PROMOTION"
    )
    cexchange_theorem_linkage_attempt_execution_result = (
        "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_EXECUTED_"
        "DEFINITIONAL_LINKAGE_CONSTRUCTED_NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_PROMOTION"
    )
    cexchange_theorem_linkage_attempt_execution_result_review_result = (
        "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_RESULT_REVIEW_"
        "ACCEPTS_DEFINITIONAL_LINKAGE_CONSTRUCTED_NO_CK_RULE_PROMOTION_OR_MASTER_"
        "ACTION_PROMOTION"
    )
    cexchange_theorem_linkage_obligation_closeout_outcome = (
        "CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_DEFINITIONALLY_LINKED_TO_"
        "TOTAL_CONSERVATION_NO_CK_RULE_PROMOTION_OR_SEAM_CLOSURE"
    )
    ck_family_selection_after_cexchange_outcome = (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_CEXCHANGE_CLOSEOUT_"
        "SELECTS_PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_GAP_NO_PROOF_EXECUTION_OR_"
        "MASTER_ACTION_PROMOTION"
    )
    ck_family_selection_after_cexchange_strict_outcome = (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_CEXCHANGE_CLOSEOUT_"
        "SELECTS_SECOND_PRIORITY_TOTAL_CONSERVATION_OBLIGATION_NO_GAP_DISCHARGE_OR_"
        "CK_RULE_PROMOTION"
    )
    ck_family_selection_after_cexchange_review_outcome = (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_CEXCHANGE_CLOSEOUT_"
        "RESULT_REVIEW_ACCEPTS_PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_GAP_SELECTION_"
        "NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
    )
    ck_family_selection_after_cexchange_strict_review_outcome = (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_CEXCHANGE_CLOSEOUT_"
        "RESULT_REVIEW_ACCEPTS_SECOND_PRIORITY_TOTAL_CONSERVATION_SELECTION_ONLY_NO_GAP_"
        "DISCHARGE_OR_CK_RULE_PROMOTION"
    )
    psi_A_total_conservation_packet_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_"
        "EXCHANGE_CANCELLATION_THEOREM_TARGET_SCOPED_NO_PROOF_EXECUTION_OR_"
        "CK_RULE_PROMOTION"
    )
    psi_A_total_conservation_strict_packet_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_GAUGE_"
        "MATTER_EXCHANGE_CANCELLATION_TARGET_NO_THEOREM_DISCHARGE_OR_MASTER_ACTION_PROMOTION"
    )
    psi_A_total_conservation_packet_review_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_"
        "ACCEPTS_EXCHANGE_CANCELLATION_THEOREM_TARGET_SCOPE_NO_PROOF_EXECUTION_OR_"
        "CK_RULE_PROMOTION"
    )
    psi_A_total_conservation_strict_packet_review_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_"
        "ACCEPTS_GAUGE_MATTER_EXCHANGE_CANCELLATION_TARGET_NO_THEOREM_DISCHARGE_OR_"
        "MASTER_ACTION_PROMOTION"
    )
    psi_A_total_conservation_attempt_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
        "RESULT_REVIEW_ACCEPTS_EXCHANGE_CANCELLATION_ROUTE_PREPARATION_NO_THEOREM_"
        "DISCHARGE_OR_CK_RULE_PROMOTION"
    )
    psi_A_total_conservation_execution_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
        "EXECUTED_EXCHANGE_CANCELLATION_CONSTRUCTED_NO_CK_RULE_PROMOTION_OR_"
        "MASTER_ACTION_PROMOTION"
    )
    psi_A_total_conservation_strict_execution_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
        "EXECUTED_TOTAL_CONSERVATION_DERIVED_FROM_GAUGE_MATTER_EXCHANGE_"
        "CANCELLATION_NO_SEAM_CLOSURE"
    )
    psi_A_total_conservation_execution_result_review_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
        "RESULT_REVIEW_ACCEPTS_EXCHANGE_CANCELLATION_CONSTRUCTED_NO_CK_RULE_"
        "PROMOTION_OR_MASTER_ACTION_PROMOTION"
    )
    psi_A_total_conservation_execution_result_review_strict_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
        "RESULT_REVIEW_ACCEPTS_TOTAL_CONSERVATION_DERIVED_FROM_GAUGE_MATTER_"
        "EXCHANGE_CANCELLATION_NO_SEAM_CLOSURE"
    )
    psi_A_total_conservation_closeout_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_EXCHANGE_"
        "CANCELLATION_LINKED_TO_GAUGE_MATTER_EXCHANGE_ROUTES_NO_CK_RULE_PROMOTION_"
        "OR_SEAM_CLOSURE"
    )
    psi_A_total_conservation_strict_closeout_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_LOCAL_TOTAL_"
        "CONSERVATION_LINKAGE_NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
    )
    psi_A_total_conservation_closeout_result_review_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_"
        "ACCEPTS_EXCHANGE_CANCELLATION_LINKAGE_NO_CK_RULE_PROMOTION_OR_SEAM_CLOSURE"
    )
    psi_A_total_conservation_closeout_result_review_strict_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_"
        "ACCEPTS_LOCAL_TOTAL_CONSERVATION_LINKAGE_NO_ACTION_VARIATION_OR_MASTER_ACTION_"
        "PROMOTION"
    )
    psi_A_total_conservation_strict_attempt_outcome = (
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
        "PREPARED_GAUGE_MATTER_EXCHANGE_CANCELLATION_ROUTE_NO_ACTION_VARIATION_OR_"
        "MASTER_ACTION_PROMOTION"
    )
    post_psi_A_total_conservation_selector_outcome = (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_TOTAL_"
        "CONSERVATION_CLOSEOUT_SELECTS_PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_"
        "GAP_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
    )
    post_psi_A_total_conservation_selector_strict_outcome = (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_TOTAL_"
        "CONSERVATION_CLOSEOUT_SELECTS_MATTER_EXCHANGE_LINKAGE_OBLIGATION_NO_GAP_"
        "DISCHARGE_OR_CK_RULE_PROMOTION"
    )
    post_psi_A_total_conservation_selector_result_review_outcome = (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_TOTAL_"
        "CONSERVATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_PSI_A_MATTER_SECTOR_EXCHANGE_"
        "THEOREM_LINKAGE_GAP_SELECTION_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
    )
    post_psi_A_total_conservation_selector_result_review_strict_outcome = (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_TOTAL_"
        "CONSERVATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_MATTER_EXCHANGE_LINKAGE_"
        "SELECTION_ONLY_NO_GAP_DISCHARGE_OR_CK_RULE_PROMOTION"
    )
    psi_A_matter_sector_packet_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_"
        "MATTER_EXCHANGE_ROUTE_SCOPED_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
    )
    psi_A_matter_sector_packet_strict_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_"
        "DIRAC_MATTER_EXCHANGE_TARGET_NO_THEOREM_DISCHARGE_OR_MASTER_ACTION_PROMOTION"
    )
    psi_A_matter_sector_packet_result_review_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_"
        "ACCEPTS_MATTER_EXCHANGE_ROUTE_SCOPE_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
    )
    psi_A_matter_sector_packet_result_review_strict_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_"
        "ACCEPTS_DIRAC_MATTER_EXCHANGE_TARGET_NO_THEOREM_DISCHARGE_OR_MASTER_ACTION_"
        "PROMOTION"
    )
    psi_A_matter_sector_attempt_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
        "PREPARED_MATTER_EXCHANGE_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_OR_"
        "CK_RULE_PROMOTION"
    )
    psi_A_matter_sector_attempt_strict_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
        "PREPARED_DIRAC_PAIR_TO_MATTER_EXCHANGE_TARGET_NO_ACTION_VARIATION_OR_MASTER_"
        "ACTION_PROMOTION"
    )
    psi_A_matter_sector_attempt_result_review_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
        "RESULT_REVIEW_ACCEPTS_MATTER_EXCHANGE_ROUTE_PREPARATION_NO_THEOREM_"
        "DISCHARGE_OR_CK_RULE_PROMOTION"
    )
    psi_A_matter_sector_attempt_result_review_strict_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
        "RESULT_REVIEW_ACCEPTS_PREPARED_DIRAC_PAIR_TO_MATTER_EXCHANGE_LINKAGE_"
        "ROUTE_NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
    )
    psi_A_matter_sector_attempt_execution_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
        "EXECUTED_MATTER_EXCHANGE_ROUTE_CONSTRUCTED_NO_CK_RULE_PROMOTION_OR_MASTER_"
        "ACTION_PROMOTION"
    )
    psi_A_matter_sector_attempt_execution_strict_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
        "EXECUTED_MATTER_EXCHANGE_DERIVED_FROM_DIRAC_PAIR_NO_SEAM_CLOSURE"
    )
    psi_A_matter_sector_attempt_execution_result_review_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
        "RESULT_REVIEW_ACCEPTS_MATTER_EXCHANGE_ROUTE_CONSTRUCTED_NO_CK_RULE_"
        "PROMOTION_OR_MASTER_ACTION_PROMOTION"
    )
    psi_A_matter_sector_attempt_execution_result_review_strict_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
        "RESULT_REVIEW_ACCEPTS_MATTER_EXCHANGE_DERIVED_FROM_DIRAC_PAIR_NO_SEAM_CLOSURE"
    )
    psi_A_matter_sector_closeout_recommended_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_DIRAC_"
        "PAIR_LINKED_MATTER_EXCHANGE_ROUTE_NO_CK_RULE_PROMOTION_OR_SEAM_CLOSURE"
    )
    psi_A_matter_sector_strict_closeout_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_LOCAL_"
        "MATTER_EXCHANGE_LINKAGE_NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
    )
    psi_A_matter_sector_closeout_result_review_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_"
        "REVIEW_ACCEPTS_DIRAC_PAIR_LINKED_MATTER_EXCHANGE_ROUTE_NO_CK_RULE_"
        "PROMOTION_OR_SEAM_CLOSURE"
    )
    psi_A_matter_sector_closeout_result_review_strict_outcome = (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_"
        "REVIEW_ACCEPTS_LOCAL_MATTER_EXCHANGE_LINKAGE_NO_ACTION_VARIATION_OR_"
        "MASTER_ACTION_PROMOTION"
    )
    psi_A_matter_exchange_selector_outcome = (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
        "EXCHANGE_CLOSEOUT_SELECTS_PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_"
        "GAP_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
    )
    psi_A_matter_exchange_selector_strict_outcome = (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
        "EXCHANGE_CLOSEOUT_SELECTS_GAUGE_EXCHANGE_LINKAGE_OBLIGATION_NO_GAP_"
        "DISCHARGE_OR_CK_RULE_PROMOTION"
    )
    psi_A_matter_exchange_selector_review_outcome = (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
        "EXCHANGE_CLOSEOUT_RESULT_REVIEW_ACCEPTS_PSI_A_GAUGE_SECTOR_EXCHANGE_"
        "THEOREM_LINKAGE_GAP_SELECTION_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
    )
    psi_A_matter_exchange_selector_review_strict_outcome = (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
        "EXCHANGE_CLOSEOUT_RESULT_REVIEW_ACCEPTS_GAUGE_EXCHANGE_SELECTION_ONLY_"
        "NO_GAP_DISCHARGE_OR_CK_RULE_PROMOTION"
    )
    psi_A_gauge_exchange_packet_outcome = (
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_"
        "GAUGE_EXCHANGE_ROUTE_SCOPED_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
    )
    psi_A_gauge_exchange_packet_strict_outcome = (
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_"
        "GAUGE_STRESS_DIVERGENCE_TO_SOURCED_MAXWELL_TARGET_NO_ACTION_VARIATION_OR_"
        "MASTER_ACTION_PROMOTION"
    )

    interaction_active_workstream = active_workstream(payload)
    assert interaction_active_workstream["workstream_id"] == ACTIVE_LANE
    assert interaction_active_workstream["active_lane"] == ACTIVE_LANE
    assert interaction_active_workstream["authorized_next_strict_target"] == LIVE_TARGET
    assert interaction_active_workstream["authorized_target"] == LIVE_TARGET
    assert interaction_active_workstream[
        "authorization_evidence"
    ] == str(LIVE_TARGET_EVIDENCE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    assert interaction_active_workstream["report"] == (
        "formal/docs/release/"
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_"
        "20260628_v0.json"
    )
    assert interaction_active_workstream["consumed_target"] == PREVIOUS_LIVE_TARGET
    assert interaction_active_workstream["packet_result"] == (
        psi_A_gauge_exchange_packet_outcome
    )
    assert interaction_active_workstream["strict_packet_result"] == (
        psi_A_gauge_exchange_packet_strict_outcome
    )
    assert interaction_active_workstream["review_result"] == "PENDING"
    assert interaction_active_workstream["selected_next_target"] == (
        "prepare_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route"
    )
    assert interaction_active_workstream["selected_next_target_kind"] == (
        "psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_preparation"
    )
    assert interaction_active_workstream["selected_obligation"] == (
        "psi-A gauge-sector exchange theorem-linkage gap"
    )
    assert interaction_active_workstream["gauge_exchange_target_rule"] == (
        "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha"
    )
    assert interaction_active_workstream["theorem_target_statement"] == (
        "Given nabla_mu T_A^{mu nu} = - F^nu{}_alpha nabla_mu F^{mu alpha} "
        "and nabla_mu F^{mu alpha} = J^alpha, show nabla_mu T_A^{mu nu} = "
        "- F^nu{}_alpha J^alpha."
    )
    assert "gauge stress-energy divergence identity" in interaction_active_workstream[
        "watch_items"
    ]
    assert interaction_active_workstream["proof_execution_authorized"] == "no"
    assert interaction_active_workstream["proof_attempt_executed"] == "no"
    assert interaction_active_workstream["theorem_discharged"] == "no"
    assert interaction_active_workstream["theorem_linkage_obligation_discharged"] == "no"
    assert interaction_active_workstream["rule_promoted"] == "no"
    assert interaction_active_workstream["gap_1_through_gap_8_discharged"] == "no"
    assert interaction_active_workstream["C_k_action_embedding_claimed"] == "no"
    assert interaction_active_workstream["C_k_action_variation_executed"] == "no"
    assert interaction_active_workstream["full_maxwell_closure_claimed"] == "no"
    assert interaction_active_workstream["em_qft_closure_claimed"] == "no"
    assert interaction_active_workstream["qft_gr_closure_claimed"] == "no"
    assert interaction_active_workstream["gr_qm_closure_claimed"] == "no"
    assert interaction_active_workstream["empirical_validation_claimed"] == "no"
    assert interaction_active_workstream["master_action_promoted"] == "no"

    consumed_a_ck_closeout = _workstream(payload, A_CK_CLOSEOUT_TARGET)
    assert consumed_a_ck_closeout["status"] == "paused"
    assert consumed_a_ck_closeout["closeout_result"] == a_ck_closeout_result
    assert consumed_a_ck_closeout["selected_next_target"] == A_CK_CLOSEOUT_SELECTED_TARGET
    assert consumed_a_ck_closeout[
        "selected_next_target_kind"
    ] == "master_action_interaction_selector_after_A_ck_triad"
    assert consumed_a_ck_closeout["A_ck_triad_closed"] == "yes"
    assert consumed_a_ck_closeout["source_bridge_transport_family_closed"] == "yes"
    assert consumed_a_ck_closeout["post_closeout_selector_authorized"] == "yes"
    assert consumed_a_ck_closeout["interaction_selector_executed"] == "no"
    assert consumed_a_ck_closeout["psi_A_current_exchange_route_selected"] == "no"
    assert consumed_a_ck_closeout["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert consumed_a_ck_closeout["J_nu_derived"] == "no"
    assert consumed_a_ck_closeout["sourced_maxwell_route_derived"] == "no"
    assert consumed_a_ck_closeout["full_em_closure_claimed"] == "no"
    assert consumed_a_ck_closeout["qft_gr_closure_claimed"] == "no"
    assert consumed_a_ck_closeout["master_action_promoted"] == "no"

    consumed_a_ck_synthesis_review = _workstream(payload, A_CK_SYNTHESIS_REVIEW_TARGET)
    assert consumed_a_ck_synthesis_review["status"] == "paused"
    assert consumed_a_ck_synthesis_review["review_result"] == a_ck_synthesis_review_result
    assert consumed_a_ck_synthesis_review["selected_next_target"] == A_CK_CLOSEOUT_TARGET
    assert consumed_a_ck_synthesis_review["triad_closeout_authorized"] == "yes"
    assert consumed_a_ck_synthesis_review["triad_closeout_prepared"] == "no"
    assert consumed_a_ck_synthesis_review["J_nu_derived"] == "no"
    assert consumed_a_ck_synthesis_review["sourced_maxwell_route_derived"] == "no"
    assert consumed_a_ck_synthesis_review["full_em_closure_claimed"] == "no"
    assert consumed_a_ck_synthesis_review["qft_gr_closure_claimed"] == "no"
    assert consumed_a_ck_synthesis_review["master_action_promoted"] == "no"

    consumed_a_transport_closeout = _workstream(payload, A_TRANSPORT_CLOSEOUT_TARGET)
    assert consumed_a_transport_closeout["status"] == "paused"
    assert consumed_a_transport_closeout["packet_result"] == "CLOSEOUT_ACCEPTED"
    assert consumed_a_transport_closeout["outcome_id"] == a_transport_closeout_result
    assert consumed_a_transport_closeout["closeout_result"] == a_transport_closeout_result
    assert consumed_a_transport_closeout["selected_next_target"] == A_CK_SYNTHESIS_PACKET_TARGET
    assert consumed_a_transport_closeout[
        "selected_next_target_kind"
    ] == "toe_native_A_ck_source_bridge_transport_rule_family_synthesis_packet_preparation"
    assert consumed_a_transport_closeout[
        "three_rule_family_synthesis_packet_authorized"
    ] == "yes"
    assert consumed_a_transport_closeout[
        "three_rule_family_synthesis_packet_prepared"
    ] == "no"
    assert consumed_a_transport_closeout["transport_consistency_rule_closed"] == "yes"
    assert consumed_a_transport_closeout["transport_consistency_proved"] == "no"
    assert consumed_a_transport_closeout["C_k_variation_executed"] == "no"
    assert consumed_a_transport_closeout["J_nu_derived"] == "no"
    assert consumed_a_transport_closeout["sourced_maxwell_equation_derived"] == "no"
    assert consumed_a_transport_closeout["full_em_closure_claimed"] == "no"
    assert consumed_a_transport_closeout["qft_gr_closure_claimed"] == "no"
    assert consumed_a_transport_closeout["master_action_promoted"] == "no"

    consumed_a_transport_embedding_review = _workstream(
        payload, A_TRANSPORT_FUNCTIONAL_EMBEDDING_REVIEW_TARGET
    )
    assert consumed_a_transport_embedding_review["status"] == "paused"
    assert consumed_a_transport_embedding_review["packet_result"] == "REVIEW_ACCEPTED"
    assert consumed_a_transport_embedding_review["outcome_id"] == (
        a_transport_functional_embedding_review_result
    )
    assert consumed_a_transport_embedding_review["review_result"] == (
        a_transport_functional_embedding_review_result
    )
    assert consumed_a_transport_embedding_review["selected_next_target"] == (
        A_TRANSPORT_CLOSEOUT_TARGET
    )
    assert consumed_a_transport_embedding_review[
        "selected_next_target_kind"
    ] == "toe_native_A_transport_consistency_ck_admissibility_rule_closeout_preparation"
    assert consumed_a_transport_embedding_review[
        "admissibility_rule_closeout_authorized"
    ] == "yes"
    assert consumed_a_transport_embedding_review[
        "admissibility_rule_closeout_prepared"
    ] == "no"
    assert consumed_a_transport_embedding_review["admissibility_only_route_selected"] == "yes"
    assert consumed_a_transport_embedding_review["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed_a_transport_embedding_review["penalty_route_unlicensed"] == "yes"
    assert consumed_a_transport_embedding_review["penalty_route_licensed"] == "no"
    assert consumed_a_transport_embedding_review[
        "direct_dynamical_law_interpretation_selected"
    ] == "no"
    assert consumed_a_transport_embedding_review[
        "transport_candidate_functional_defined"
    ] == "no"
    assert consumed_a_transport_embedding_review["C_k_action_embedding_constructed"] == "no"
    assert consumed_a_transport_embedding_review["C_k_variation_executed"] == "no"
    assert consumed_a_transport_embedding_review["J_nu_derived"] == "no"
    assert consumed_a_transport_embedding_review[
        "sourced_maxwell_equation_derived"
    ] == "no"
    assert consumed_a_transport_embedding_review["full_em_closure_claimed"] == "no"
    assert consumed_a_transport_embedding_review["qft_gr_closure_claimed"] == "no"
    assert consumed_a_transport_embedding_review["master_action_promoted"] == "no"

    consumed_a_transport_embedding = _workstream(
        payload, A_TRANSPORT_FUNCTIONAL_EMBEDDING_PACKET_TARGET
    )
    assert consumed_a_transport_embedding["status"] == "paused"
    assert consumed_a_transport_embedding["packet_result"] == (
        "OPTIONS_RECORDED_ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
    )
    assert consumed_a_transport_embedding["outcome_id"] == (
        a_transport_functional_embedding_packet_result
    )
    assert consumed_a_transport_embedding["selected_next_target"] == (
        A_TRANSPORT_FUNCTIONAL_EMBEDDING_REVIEW_TARGET
    )
    assert consumed_a_transport_embedding["transport_candidate_id"] == (
        "A_transport_derivation_chain_stability_ck_candidate"
    )
    assert consumed_a_transport_embedding["transport_constraint_equation"] == (
        "C_transport^A = 0"
    )
    assert consumed_a_transport_embedding["admissibility_only_route_selected"] == "yes"
    assert consumed_a_transport_embedding["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed_a_transport_embedding["penalty_route_licensed"] == "no"
    assert consumed_a_transport_embedding[
        "direct_dynamical_law_interpretation_selected"
    ] == "no"
    assert consumed_a_transport_embedding["transport_candidate_functional_defined"] == "no"
    assert consumed_a_transport_embedding["C_k_variation_executed"] == "no"
    assert consumed_a_transport_embedding["J_nu_derived"] == "no"
    assert consumed_a_transport_embedding["sourced_maxwell_equation_derived"] == "no"
    assert consumed_a_transport_embedding["full_em_closure_claimed"] == "no"
    assert consumed_a_transport_embedding["qft_gr_closure_claimed"] == "no"
    assert consumed_a_transport_embedding["master_action_promoted"] == "no"

    consumed_a_transport_review = _workstream(
        payload, A_TRANSPORT_CANDIDATE_REVIEW_TARGET
    )
    assert consumed_a_transport_review["status"] == "paused"
    assert consumed_a_transport_review["review_result"] == (
        a_transport_candidate_review_result
    )
    assert consumed_a_transport_review["selected_next_target"] == (
        A_TRANSPORT_FUNCTIONAL_EMBEDDING_PACKET_TARGET
    )
    assert consumed_a_transport_review["functional_embedding_packet_authorized"] == "yes"
    assert consumed_a_transport_review["functional_embedding_packet_prepared"] == "no"

    consumed_a_transport_candidate = _workstream(
        payload, A_TRANSPORT_CANDIDATE_PACKET_TARGET
    )
    assert consumed_a_transport_candidate["status"] == "paused"
    assert consumed_a_transport_candidate["packet_result"] == (
        "A_TRANSPORT_STABILITY_RULE_RECORDED_NO_CURRENT_OR_EM_CLOSURE"
    )
    assert consumed_a_transport_candidate["outcome_id"] == a_transport_candidate_packet_result
    assert consumed_a_transport_candidate["selected_next_target"] == (
        A_TRANSPORT_CANDIDATE_REVIEW_TARGET
    )
    assert consumed_a_transport_candidate[
        "selected_next_target_kind"
    ] == "toe_native_A_transport_consistency_ck_constraint_candidate_packet_result_review"
    assert consumed_a_transport_candidate["result_review_authorized"] == "yes"
    assert consumed_a_transport_candidate["review_prepared"] == "no"
    assert consumed_a_transport_candidate["transport_candidate_recorded_as_admissibility_rule"] == "yes"
    assert consumed_a_transport_candidate["transport_candidate_functional_defined"] == "no"
    assert consumed_a_transport_candidate["transport_consistency_proved"] == "no"
    assert consumed_a_transport_candidate["C_k_variation_executed"] == "no"
    assert consumed_a_transport_candidate["J_nu_derived"] == "no"
    assert consumed_a_transport_candidate["sourced_maxwell_equation_derived"] == "no"
    assert consumed_a_transport_candidate["full_em_closure_claimed"] == "no"
    assert consumed_a_transport_candidate["qft_gr_closure_claimed"] == "no"
    assert consumed_a_transport_candidate["master_action_promoted"] == "no"


    consumed_a_source_bridge_selector = _workstream(
        payload, A_SOURCE_BRIDGE_SELECTOR_TARGET
    )
    assert consumed_a_source_bridge_selector["status"] == "paused"
    assert consumed_a_source_bridge_selector["selection_result"] == (
        a_source_bridge_selector_result
    )
    assert consumed_a_source_bridge_selector["selected_next_target"] == (
        A_TRANSPORT_CANDIDATE_PACKET_TARGET
    )
    assert consumed_a_source_bridge_selector[
        "selected_next_target_kind"
    ] == "toe_native_A_transport_consistency_ck_constraint_candidate_packet_preparation"
    assert consumed_a_source_bridge_selector[
        "transport_consistency_candidate_packet_authorized"
    ] == "yes"
    assert consumed_a_source_bridge_selector[
        "transport_consistency_candidate_packet_prepared"
    ] == "no"
    assert consumed_a_source_bridge_selector["transport_consistency_proved"] == "no"
    assert consumed_a_source_bridge_selector["C_k_variation_executed"] == "no"
    assert consumed_a_source_bridge_selector["J_nu_derived"] == "no"
    assert consumed_a_source_bridge_selector["full_em_closure_claimed"] == "no"
    assert consumed_a_source_bridge_selector["qft_gr_closure_claimed"] == "no"
    assert consumed_a_source_bridge_selector["master_action_promoted"] == "no"
    consumed_a_bridge_closeout = _workstream(payload, A_BRIDGE_CLOSEOUT_TARGET)
    assert consumed_a_bridge_closeout["status"] == "paused"
    assert consumed_a_bridge_closeout["packet_result"] == "CLOSEOUT_ACCEPTED"
    assert consumed_a_bridge_closeout["outcome_id"] == a_bridge_closeout_result
    assert consumed_a_bridge_closeout["closeout_result"] == a_bridge_closeout_result
    assert consumed_a_bridge_closeout["selected_next_target"] == A_SOURCE_BRIDGE_SELECTOR_TARGET
    assert consumed_a_bridge_closeout[
        "selected_next_target_kind"
    ] == "toe_native_A_ck_constraint_family_after_source_and_bridge_admissibility_selection"
    assert consumed_a_bridge_closeout["admissibility_rule_closeout_prepared"] == "yes"
    assert consumed_a_bridge_closeout["vacuum_U1_bridge_admissibility_rule_closed"] == "yes"
    assert consumed_a_bridge_closeout["next_selector_authorized"] == "yes"
    assert consumed_a_bridge_closeout["next_selector_prepared"] == "no"
    assert consumed_a_bridge_closeout["next_candidate_family_selected"] == "no"
    assert consumed_a_bridge_closeout["A_transport_consistency_family_selected"] == "no"
    assert consumed_a_bridge_closeout["C_k_variation_executed"] == "no"
    assert consumed_a_bridge_closeout["J_nu_derived"] == "no"
    assert consumed_a_bridge_closeout["sourced_maxwell_equation_derived"] == "no"
    assert consumed_a_bridge_closeout["full_em_closure_claimed"] == "no"
    assert consumed_a_bridge_closeout["qft_gr_closure_claimed"] == "no"
    assert consumed_a_bridge_closeout["master_action_promoted"] == "no"

    consumed_a_bridge_review = _workstream(
        payload, A_BRIDGE_FUNCTIONAL_EMBEDDING_REVIEW_TARGET
    )
    assert consumed_a_bridge_review["status"] == "paused"
    assert consumed_a_bridge_review["packet_result"] == "REVIEW_ACCEPTED"
    assert consumed_a_bridge_review["outcome_id"] == (
        a_bridge_functional_embedding_review_result
    )
    assert consumed_a_bridge_review["review_result"] == (
        a_bridge_functional_embedding_review_result
    )
    assert consumed_a_bridge_review["selected_next_target"] == A_BRIDGE_CLOSEOUT_TARGET
    assert consumed_a_bridge_review[
        "selected_next_target_kind"
    ] == "toe_native_A_bridge_admissibility_ck_admissibility_rule_closeout_preparation"
    assert consumed_a_bridge_review["admissibility_rule_closeout_authorized"] == "yes"
    assert consumed_a_bridge_review["admissibility_rule_closeout_prepared"] == "no"
    assert consumed_a_bridge_review["admissibility_only_route_selected"] == "yes"
    assert consumed_a_bridge_review["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed_a_bridge_review["penalty_route_unlicensed"] == "yes"
    assert consumed_a_bridge_review["heterogeneous_tuple_norm_defined"] == "no"
    assert consumed_a_bridge_review["C_k_action_embedding_constructed"] == "no"
    assert consumed_a_bridge_review["C_k_variation_executed"] == "no"
    assert consumed_a_bridge_review["J_nu_derived"] == "no"
    assert consumed_a_bridge_review["sourced_maxwell_equation_derived"] == "no"
    assert consumed_a_bridge_review["full_em_closure_claimed"] == "no"
    assert consumed_a_bridge_review["qft_gr_closure_claimed"] == "no"
    assert consumed_a_bridge_review["master_action_promoted"] == "no"

    consumed_a_bridge_embedding_packet = _workstream(
        payload, A_BRIDGE_FUNCTIONAL_EMBEDDING_PACKET_TARGET
    )
    assert consumed_a_bridge_embedding_packet["status"] == "paused"
    assert consumed_a_bridge_embedding_packet["packet_result"] == (
        "OPTIONS_RECORDED_ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
    )
    assert consumed_a_bridge_embedding_packet["outcome_id"] == (
        a_bridge_functional_embedding_result
    )
    assert consumed_a_bridge_embedding_packet[
        "selected_next_target"
    ] == A_BRIDGE_FUNCTIONAL_EMBEDDING_REVIEW_TARGET
    assert consumed_a_bridge_embedding_packet[
        "selected_next_target_kind"
    ] == "toe_native_A_bridge_admissibility_ck_functional_embedding_packet_result_review"
    assert consumed_a_bridge_embedding_packet["admissibility_only_route_selected"] == "yes"
    assert consumed_a_bridge_embedding_packet["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed_a_bridge_embedding_packet["penalty_route_unlicensed"] == "yes"
    assert consumed_a_bridge_embedding_packet["heterogeneous_tuple_norm_defined"] == "no"
    assert consumed_a_bridge_embedding_packet["C_k_action_embedding_constructed"] == "no"
    assert consumed_a_bridge_embedding_packet["C_k_variation_executed"] == "no"
    assert consumed_a_bridge_embedding_packet["J_nu_derived"] == "no"
    assert consumed_a_bridge_embedding_packet[
        "sourced_maxwell_equation_derived"
    ] == "no"
    assert consumed_a_bridge_embedding_packet["full_em_closure_claimed"] == "no"
    assert consumed_a_bridge_embedding_packet["qft_gr_closure_claimed"] == "no"
    assert consumed_a_bridge_embedding_packet["master_action_promoted"] == "no"

    consumed_a_bridge_candidate_review = _workstream(
        payload, A_BRIDGE_CANDIDATE_REVIEW_TARGET
    )
    assert consumed_a_bridge_candidate_review["status"] == "paused"
    assert consumed_a_bridge_candidate_review["review_result"] == (
        a_bridge_candidate_review_result
    )
    assert consumed_a_bridge_candidate_review["outcome_id"] == (
        a_bridge_candidate_review_result
    )
    assert consumed_a_bridge_candidate_review[
        "selected_next_target"
    ] == A_BRIDGE_FUNCTIONAL_EMBEDDING_PACKET_TARGET
    assert consumed_a_bridge_candidate_review[
        "selected_next_target_kind"
    ] == "toe_native_A_bridge_admissibility_ck_functional_embedding_packet_preparation"
    assert consumed_a_bridge_candidate_review["A_bridge_candidate_id"] == (
        "A_bridge_vacuum_u1_route_consistency_ck_candidate"
    )
    assert consumed_a_bridge_candidate_review["A_bridge_constraint_equation"] == (
        "C_bridge^A = 0"
    )
    assert consumed_a_bridge_candidate_review[
        "review_accepts_vacuum_u1_route_consistency_candidate"
    ] == "yes"
    assert consumed_a_bridge_candidate_review[
        "functional_embedding_packet_authorized"
    ] == "yes"
    assert consumed_a_bridge_candidate_review["C_k_action_embedding_constructed"] == "no"
    assert consumed_a_bridge_candidate_review["C_k_variation_executed"] == "no"
    assert consumed_a_bridge_candidate_review["J_nu_derived"] == "no"
    assert consumed_a_bridge_candidate_review[
        "sourced_maxwell_closure_claimed"
    ] == "no"
    assert consumed_a_bridge_candidate_review["full_em_closure_claimed"] == "no"
    assert consumed_a_bridge_candidate_review["qft_gr_closure_claimed"] == "no"
    assert consumed_a_bridge_candidate_review["master_action_promoted"] == "no"

    consumed_a_bridge_candidate_packet = _workstream(
        payload, A_BRIDGE_CANDIDATE_PACKET_TARGET
    )
    assert consumed_a_bridge_candidate_packet["status"] == "paused"
    assert consumed_a_bridge_candidate_packet["packet_result"] == (
        a_bridge_candidate_packet_result
    )
    assert consumed_a_bridge_candidate_packet["outcome_id"] == (
        a_bridge_candidate_packet_result
    )
    assert consumed_a_bridge_candidate_packet[
        "selected_next_target"
    ] == A_BRIDGE_CANDIDATE_REVIEW_TARGET
    assert consumed_a_bridge_candidate_packet[
        "selected_next_target_kind"
    ] == "toe_native_A_bridge_admissibility_ck_constraint_candidate_packet_result_review"
    assert consumed_a_bridge_candidate_packet["A_bridge_candidate_id"] == (
        "A_bridge_vacuum_u1_route_consistency_ck_candidate"
    )
    assert consumed_a_bridge_candidate_packet["A_bridge_constraint_equation"] == (
        "C_bridge^A = 0"
    )
    assert consumed_a_bridge_candidate_packet[
        "A_bridge_candidate_recorded_as_admissibility_rule"
    ] == "yes"
    assert consumed_a_bridge_candidate_packet["A_bridge_candidate_rule_proved"] == "no"
    assert consumed_a_bridge_candidate_packet["C_k_variation_executed"] == "no"
    assert consumed_a_bridge_candidate_packet["J_nu_derived"] == "no"
    assert consumed_a_bridge_candidate_packet[
        "sourced_maxwell_closure_claimed"
    ] == "no"
    assert consumed_a_bridge_candidate_packet["full_em_closure_claimed"] == "no"
    assert consumed_a_bridge_candidate_packet["qft_gr_closure_claimed"] == "no"
    assert consumed_a_bridge_candidate_packet["master_action_promoted"] == "no"

    consumed_a_ck_selector = _workstream(payload, A_CK_SELECTOR_TARGET)
    assert consumed_a_ck_selector["status"] == "paused"
    assert consumed_a_ck_selector["packet_result"] == "SELECTION_ACCEPTED"
    assert consumed_a_ck_selector["outcome_id"] == a_ck_selector_result
    assert consumed_a_ck_selector["selection_result"] == a_ck_selector_result
    assert consumed_a_ck_selector["selected_next_target"] == A_BRIDGE_CANDIDATE_PACKET_TARGET
    assert consumed_a_ck_selector[
        "selected_next_target_kind"
    ] == "toe_native_A_bridge_admissibility_ck_constraint_candidate_packet_preparation"
    assert consumed_a_ck_selector["A_bridge_admissibility_family_selected"] == "yes"
    assert consumed_a_ck_selector["bridge_C_k_candidate_constructed"] == "no"
    assert consumed_a_ck_selector["C_k_action_embedding_constructed"] == "no"
    assert consumed_a_ck_selector["C_k_variation_executed"] == "no"
    assert consumed_a_ck_selector["J_nu_derived"] == "no"
    assert consumed_a_ck_selector["sourced_maxwell_closure_claimed"] == "no"
    assert consumed_a_ck_selector["full_em_closure_claimed"] == "no"
    assert consumed_a_ck_selector["qft_gr_closure_claimed"] == "no"
    assert consumed_a_ck_selector["master_action_promoted"] == "no"

    consumed_a_source_ck_closeout = _workstream(payload, A_SOURCE_CK_CLOSEOUT_TARGET)
    assert consumed_a_source_ck_closeout["status"] == "paused"
    assert consumed_a_source_ck_closeout["packet_result"] == "CLOSEOUT_ACCEPTED"
    assert consumed_a_source_ck_closeout["outcome_id"] == a_source_ck_closeout_result
    assert consumed_a_source_ck_closeout["closeout_result"] == a_source_ck_closeout_result
    assert consumed_a_source_ck_closeout["selected_next_target"] == A_CK_SELECTOR_TARGET
    assert consumed_a_source_ck_closeout[
        "selected_next_target_kind"
    ] == "toe_native_A_ck_constraint_family_after_source_admissibility_selection"
    assert consumed_a_source_ck_closeout["admissibility_rule_closeout_prepared"] == "yes"
    assert consumed_a_source_ck_closeout["vacuum_gauge_source_rule_closed"] == "yes"
    assert consumed_a_source_ck_closeout["C_k_variation_executed"] == "no"
    assert consumed_a_source_ck_closeout["J_nu_derived"] == "no"
    assert consumed_a_source_ck_closeout[
        "sourced_maxwell_equation_derived"
    ] == "no"
    assert consumed_a_source_ck_closeout["master_action_promoted"] == "no"

    consumed_a_source_ck_functional_embedding_review = _workstream(
        payload, A_SOURCE_CK_FUNCTIONAL_EMBEDDING_REVIEW_TARGET
    )
    assert consumed_a_source_ck_functional_embedding_review["status"] == "paused"
    assert consumed_a_source_ck_functional_embedding_review["packet_result"] == (
        "REVIEW_ACCEPTED"
    )
    assert consumed_a_source_ck_functional_embedding_review["outcome_id"] == (
        a_source_ck_functional_embedding_review_result
    )
    assert consumed_a_source_ck_functional_embedding_review["review_result"] == (
        a_source_ck_functional_embedding_review_result
    )
    assert consumed_a_source_ck_functional_embedding_review[
        "selected_next_target"
    ] == A_SOURCE_CK_CLOSEOUT_TARGET
    assert consumed_a_source_ck_functional_embedding_review[
        "selected_next_target_kind"
    ] == "toe_native_A_source_admissibility_ck_admissibility_rule_closeout_preparation"
    assert consumed_a_source_ck_functional_embedding_review[
        "admissibility_rule_closeout_authorized"
    ] == "yes"
    assert consumed_a_source_ck_functional_embedding_review[
        "admissibility_rule_closeout_prepared"
    ] == "no"
    assert consumed_a_source_ck_functional_embedding_review[
        "review_accepts_admissibility_only_route"
    ] == "yes"
    assert consumed_a_source_ck_functional_embedding_review[
        "lagrange_multiplier_route_blocked"
    ] == "yes"
    assert consumed_a_source_ck_functional_embedding_review[
        "quadratic_penalty_route_licensed"
    ] == "no"
    assert consumed_a_source_ck_functional_embedding_review[
        "ck_action_embedding_constructed"
    ] == "no"
    assert consumed_a_source_ck_functional_embedding_review[
        "C_k_variation_executed"
    ] == "no"
    assert consumed_a_source_ck_functional_embedding_review["J_nu_derived"] == "no"
    assert consumed_a_source_ck_functional_embedding_review[
        "sourced_maxwell_equation_derived"
    ] == "no"
    assert consumed_a_source_ck_functional_embedding_review[
        "master_action_promoted"
    ] == "no"

    consumed_a_source_ck_functional_embedding_packet = _workstream(
        payload, A_SOURCE_CK_FUNCTIONAL_EMBEDDING_PACKET_TARGET
    )
    assert consumed_a_source_ck_functional_embedding_packet["status"] == "paused"
    assert consumed_a_source_ck_functional_embedding_packet["packet_result"] == (
        "OPTIONS_RECORDED_ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
    )
    assert consumed_a_source_ck_functional_embedding_packet["outcome_id"] == (
        a_source_ck_functional_embedding_result
    )
    assert consumed_a_source_ck_functional_embedding_packet[
        "selected_next_target"
    ] == A_SOURCE_CK_FUNCTIONAL_EMBEDDING_REVIEW_TARGET
    assert consumed_a_source_ck_functional_embedding_packet[
        "selected_next_target_kind"
    ] == "toe_native_A_source_admissibility_ck_functional_embedding_packet_result_review"
    assert consumed_a_source_ck_functional_embedding_packet[
        "admissibility_only_route_selected"
    ] == "yes"
    assert consumed_a_source_ck_functional_embedding_packet[
        "lagrange_multiplier_route_blocked"
    ] == "yes"
    assert consumed_a_source_ck_functional_embedding_packet[
        "quadratic_penalty_route_licensed"
    ] == "no"
    assert consumed_a_source_ck_functional_embedding_packet[
        "component_pairing_rule_selected"
    ] == "no"
    assert consumed_a_source_ck_functional_embedding_packet[
        "higher_derivative_analysis_completed"
    ] == "no"
    assert consumed_a_source_ck_functional_embedding_packet[
        "ck_action_embedding_constructed"
    ] == "no"
    assert consumed_a_source_ck_functional_embedding_packet[
        "C_k_variation_executed"
    ] == "no"
    assert consumed_a_source_ck_functional_embedding_packet["J_nu_derived"] == "no"
    assert consumed_a_source_ck_functional_embedding_packet[
        "sourced_maxwell_equation_derived"
    ] == "no"
    assert consumed_a_source_ck_functional_embedding_packet[
        "master_action_promoted"
    ] == "no"

    consumed_a_source_ck_candidate_review = _workstream(
        payload, A_SOURCE_CK_CANDIDATE_REVIEW_TARGET
    )
    assert consumed_a_source_ck_candidate_review["status"] == "paused"
    assert consumed_a_source_ck_candidate_review["packet_result"] == "REVIEW_ACCEPTED"
    assert consumed_a_source_ck_candidate_review["outcome_id"] == (
        a_source_ck_candidate_review_result
    )
    assert consumed_a_source_ck_candidate_review["review_result"] == (
        a_source_ck_candidate_review_result
    )
    assert consumed_a_source_ck_candidate_review["selected_next_target"] == (
        A_SOURCE_CK_FUNCTIONAL_EMBEDDING_PACKET_TARGET
    )
    assert consumed_a_source_ck_candidate_review[
        "selected_next_target_kind"
    ] == "toe_native_A_source_admissibility_ck_functional_embedding_packet_preparation"
    assert consumed_a_source_ck_candidate_review[
        "review_accepts_vacuum_gauge_conservation_residual_candidate"
    ] == "yes"
    assert consumed_a_source_ck_candidate_review[
        "candidate_recorded_as_candidate_only"
    ] == "yes"
    assert consumed_a_source_ck_candidate_review[
        "functional_embedding_packet_authorized"
    ] == "yes"
    assert consumed_a_source_ck_candidate_review[
        "functional_embedding_packet_prepared"
    ] == "no"
    assert consumed_a_source_ck_candidate_review["C_k_variation_executed"] == "no"
    assert consumed_a_source_ck_candidate_review["J_nu_derived"] == "no"
    assert consumed_a_source_ck_candidate_review[
        "sourced_maxwell_equation_derived"
    ] == "no"
    assert consumed_a_source_ck_candidate_review["master_action_promoted"] == "no"

    consumed_a_source_ck_candidate_packet = _workstream(
        payload, A_SOURCE_CK_CANDIDATE_PACKET_TARGET
    )
    assert consumed_a_source_ck_candidate_packet["status"] == "paused"
    assert consumed_a_source_ck_candidate_packet["packet_result"] == (
        "A_SOURCE_ADMISSIBILITY_RULE_RECORDED_AS_VACUUM_CONSERVATION_RESIDUAL_"
        "NO_ACTION_VARIATION_OR_PROMOTION"
    )
    assert consumed_a_source_ck_candidate_packet["outcome_id"] == (
        a_source_ck_candidate_packet_result
    )
    assert (
        consumed_a_source_ck_candidate_packet["selected_next_target"]
        == A_SOURCE_CK_CANDIDATE_REVIEW_TARGET
    )
    assert consumed_a_source_ck_candidate_packet[
        "selected_next_target_kind"
    ] == "toe_native_A_source_admissibility_ck_constraint_candidate_packet_result_review"
    assert consumed_a_source_ck_candidate_packet["candidate_constraint_form"] == (
        "C_source^{A,nu}[g,A] := nabla_mu T_A^{mu nu}"
    )
    assert consumed_a_source_ck_candidate_packet["candidate_constraint_equation"] == (
        "C_source^{A,nu}[g,A] = 0"
    )
    assert consumed_a_source_ck_candidate_packet[
        "source_admissibility_rule_candidate_recorded"
    ] == "yes"
    assert consumed_a_source_ck_candidate_packet[
        "A_relevant_C_k_rule_candidate_recorded"
    ] == "yes"
    assert consumed_a_source_ck_candidate_packet[
        "A_relevant_C_k_rules_constructed"
    ] == "no"
    assert consumed_a_source_ck_candidate_packet[
        "ck_action_embedding_constructed"
    ] == "no"
    assert consumed_a_source_ck_candidate_packet["C_k_variation_executed"] == "no"
    assert consumed_a_source_ck_candidate_packet["J_nu_derived"] == "no"
    assert consumed_a_source_ck_candidate_packet[
        "sourced_maxwell_equation_derived"
    ] == "no"
    assert consumed_a_source_ck_candidate_packet["master_action_promoted"] == "no"

    consumed_a_after_vacuum_source_selector = _workstream(
        payload, A_AFTER_VACUUM_SOURCE_SELECTOR_TARGET
    )
    assert consumed_a_after_vacuum_source_selector["status"] == "paused"
    assert consumed_a_after_vacuum_source_selector["packet_result"] == "SELECTED"
    assert (
        consumed_a_after_vacuum_source_selector["outcome_id"]
        == a_after_vacuum_source_selection_result
    )
    assert consumed_a_after_vacuum_source_selector["selected_next_target"] == (
        A_SOURCE_CK_CANDIDATE_PACKET_TARGET
    )
    assert consumed_a_after_vacuum_source_selector[
        "selected_next_target_kind"
    ] == "toe_native_A_source_admissibility_ck_constraint_candidate_packet_preparation"
    assert consumed_a_after_vacuum_source_selector["source_rule_candidate"] == (
        "C_source^{A,nu}[g,A] := nabla_mu T_A^{mu nu}; "
        "C_source^{A,nu}[g,A] = 0"
    )
    assert consumed_a_after_vacuum_source_selector[
        "source_rule_candidate_recorded_for_next_packet"
    ] == "yes"
    assert consumed_a_after_vacuum_source_selector[
        "source_admissibility_ck_candidate_packet_prepared"
    ] == "no"
    assert consumed_a_after_vacuum_source_selector[
        "A_relevant_C_k_route_selected"
    ] == "yes"
    assert consumed_a_after_vacuum_source_selector[
        "A_relevant_C_k_rules_constructed"
    ] == "no"
    assert consumed_a_after_vacuum_source_selector[
        "ck_action_embedding_constructed"
    ] == "no"
    assert consumed_a_after_vacuum_source_selector["J_nu_derived"] == "no"
    assert consumed_a_after_vacuum_source_selector["master_action_promoted"] == "no"

    consumed_a_source_retry_result_review = _workstream(
        payload, A_SOURCE_RETRY_RESULT_REVIEW_TARGET
    )
    assert consumed_a_source_retry_result_review["status"] == "paused"
    assert consumed_a_source_retry_result_review["packet_result"] == "REVIEW_ACCEPTED"
    assert (
        consumed_a_source_retry_result_review["outcome_id"]
        == a_source_retry_result_review_result
    )
    assert (
        consumed_a_source_retry_result_review["selected_next_target"]
        == A_AFTER_VACUUM_SOURCE_SELECTOR_TARGET
    )
    assert consumed_a_source_retry_result_review[
        "selected_next_target_kind"
    ] == "toe_native_A_route_selection_after_vacuum_source_admissibility"
    assert consumed_a_source_retry_result_review["selector_authorized"] == "yes"
    assert consumed_a_source_retry_result_review[
        "ck_candidate_guidance_recorded"
    ] == "yes"
    assert consumed_a_source_retry_result_review[
        "source_admissibility_ck_candidate_packet_prepared"
    ] == "no"
    assert consumed_a_source_retry_result_review[
        "recommended_selector_candidate"
    ] == "prepare_toe_native_A_source_admissibility_ck_constraint_candidate_packet"
    assert consumed_a_source_retry_result_review[
        "A_relevant_C_k_rules_constructed"
    ] == "no"
    assert consumed_a_source_retry_result_review["J_nu_derived"] == "no"
    assert consumed_a_source_retry_result_review["master_action_promoted"] == "no"

    consumed_a_source_retry = _workstream(payload, A_SOURCE_RETRY_TARGET)
    assert consumed_a_source_retry["status"] == "paused"
    assert consumed_a_source_retry["packet_result"] == "ACCEPTED"
    assert consumed_a_source_retry["outcome_id"] == a_source_retry_result
    assert (
        consumed_a_source_retry["selected_next_target"]
        == A_SOURCE_RETRY_RESULT_REVIEW_TARGET
    )
    assert consumed_a_source_retry[
        "selected_next_target_kind"
    ] == "toe_native_A_source_admissibility_review_retry_after_vacuum_identity_result_review"
    assert consumed_a_source_retry["source_review_retry_result"] == (
        "LOCAL_ON_SHELL_VACUUM_GAUGE_SOURCE_ROUTE_ACCEPTED_NO_CURRENT_OR_EM_CLOSURE"
    )
    assert consumed_a_source_retry["bounded_review_criteria_count"] == 15
    assert consumed_a_source_retry["bounded_review_criteria_accepted_count"] == 12
    assert consumed_a_source_retry["bounded_review_criteria_blocked_count"] == 3
    assert consumed_a_source_retry[
        "accepted_divergence_identity_consumed"
    ] == "yes"
    assert consumed_a_source_retry[
        "source_admissibility_condition_satisfied_on_shell"
    ] == "yes"
    assert consumed_a_source_retry[
        "local_on_shell_vacuum_source_route_accepted"
    ] == "yes"
    assert consumed_a_source_retry["local_on_shell_vacuum_source_route_proved"] == "yes"
    assert consumed_a_source_retry[
        "full_source_admissibility_review_accepted"
    ] == "no"
    assert consumed_a_source_retry["source_admissibility_completed"] == "no"
    assert consumed_a_source_retry["source_admissibility_proved"] == "no"
    assert consumed_a_source_retry["J_nu_derived"] == "no"
    assert consumed_a_source_retry["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed_a_source_retry["master_action_promoted"] == "no"

    consumed_a_source_identity_review = _workstream(
        payload, A_SOURCE_IDENTITY_RESULT_REVIEW_TARGET
    )
    assert consumed_a_source_identity_review["status"] == "paused"
    assert consumed_a_source_identity_review["packet_result"] == "REVIEW_ACCEPTED"
    assert (
        consumed_a_source_identity_review["outcome_id"]
        == a_source_identity_result_review_result
    )
    assert consumed_a_source_identity_review[
        "selected_next_target"
    ] == A_SOURCE_RETRY_TARGET
    assert consumed_a_source_identity_review["divergence_identity_accepted"] == "yes"
    assert (
        consumed_a_source_identity_review["on_shell_vanishing_route_accepted"]
        == "yes"
    )
    assert consumed_a_source_identity_review[
        "full_source_admissibility_review_accepted"
    ] == "no"
    assert consumed_a_source_identity_review["source_admissibility_proved"] == "no"
    assert consumed_a_source_identity_review["J_nu_derived"] == "no"
    assert consumed_a_source_identity_review["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed_a_source_identity_review["master_action_promoted"] == "no"

    consumed_a_source_identity_packet = _workstream(
        payload, A_SOURCE_IDENTITY_PACKET_TARGET
    )
    assert consumed_a_source_identity_packet["status"] == "paused"
    assert consumed_a_source_identity_packet["packet_result"] == "PREPARED"
    assert consumed_a_source_identity_packet["identity_packet_result"] == (
        "ON_SHELL_DIVERGENCE_IDENTITY_CONSTRUCTED"
    )
    assert consumed_a_source_identity_packet["outcome_id"] == a_source_identity_result
    assert (
        consumed_a_source_identity_packet["selected_next_target"]
        == A_SOURCE_IDENTITY_RESULT_REVIEW_TARGET
    )
    assert consumed_a_source_identity_packet["divergence_identity_proved"] == "yes"
    assert (
        consumed_a_source_identity_packet["source_admissibility_identity_proved"]
        == "yes"
    )
    assert consumed_a_source_identity_packet["source_admissibility_proved"] == "no"
    assert consumed_a_source_identity_packet["J_nu_derived"] == "no"
    assert consumed_a_source_identity_packet["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed_a_source_identity_packet["master_action_promoted"] == "no"

    consumed_a_source_result_review = _workstream(payload, A_SOURCE_RESULT_REVIEW_TARGET)
    assert consumed_a_source_result_review["status"] == "paused"
    assert consumed_a_source_result_review["packet_result"] == "REVIEW_ACCEPTED"
    assert consumed_a_source_result_review["outcome_id"] == a_source_result_review_result
    assert (
        consumed_a_source_result_review["selected_next_target"]
        == A_SOURCE_IDENTITY_PACKET_TARGET
    )
    assert consumed_a_source_result_review["identity_packet_authorized"] == "yes"
    assert consumed_a_source_result_review["source_admissibility_identity_proved"] == "no"
    assert consumed_a_source_result_review["source_admissibility_proved"] == "no"
    assert consumed_a_source_result_review["current_route_derived"] == "no"
    assert consumed_a_source_result_review["J_nu_derived"] == "no"
    assert consumed_a_source_result_review["current_conservation_proved"] == "no"
    assert consumed_a_source_result_review["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed_a_source_result_review["em_closure_claimed"] == "no"
    assert consumed_a_source_result_review["qft_gr_closure_claimed"] == "no"
    assert consumed_a_source_result_review["master_action_promoted"] == "no"

    consumed_a_source_review_prep = _workstream(payload, A_SOURCE_REVIEW_PREP_TARGET)
    assert consumed_a_source_review_prep["status"] == "paused"
    assert consumed_a_source_review_prep["packet_result"] == "PREPARED"
    assert consumed_a_source_review_prep["outcome_id"] == a_source_review_prep_result
    assert consumed_a_source_review_prep["selected_next_target"] == A_SOURCE_RESULT_REVIEW_TARGET
    assert consumed_a_source_review_prep["source_admissibility_review_prepared"] == "yes"
    assert consumed_a_source_review_prep["local_on_shell_source_route_candidate_recorded"] == "yes"
    assert consumed_a_source_review_prep["source_admissibility_review_executed"] == "no"
    assert consumed_a_source_review_prep["source_admissibility_proved"] == "no"
    assert consumed_a_source_review_prep["current_route_derived"] == "no"
    assert consumed_a_source_review_prep["J_nu_derived"] == "no"
    assert consumed_a_source_review_prep["current_conservation_proved"] == "no"
    assert consumed_a_source_review_prep["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed_a_source_review_prep["em_closure_claimed"] == "no"
    assert consumed_a_source_review_prep["qft_gr_closure_claimed"] == "no"
    assert consumed_a_source_review_prep["master_action_promoted"] == "no"

    consumed_a_after_stress_selector = _workstream(payload, A_AFTER_STRESS_SELECTOR_TARGET)
    assert consumed_a_after_stress_selector["status"] == "paused"
    assert consumed_a_after_stress_selector["selection_result"] == a_after_stress_selection_result
    assert consumed_a_after_stress_selector["selected_next_target"] == A_SOURCE_REVIEW_PREP_TARGET
    assert consumed_a_after_stress_selector["source_admissibility_review_selected"] == "yes"
    assert consumed_a_after_stress_selector["source_admissibility_review_executed"] == "no"
    assert consumed_a_after_stress_selector["source_admissibility_proved"] == "no"
    assert consumed_a_after_stress_selector["current_route_derived"] == "no"
    assert consumed_a_after_stress_selector["J_nu_derived"] == "no"
    assert consumed_a_after_stress_selector["current_conservation_proved"] == "no"
    assert consumed_a_after_stress_selector["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed_a_after_stress_selector["em_closure_claimed"] == "no"
    assert consumed_a_after_stress_selector["qft_gr_closure_claimed"] == "no"
    assert consumed_a_after_stress_selector["master_action_promoted"] == "no"

    consumed_a_stress_energy_review = _workstream(payload, A_STRESS_ENERGY_REVIEW_TARGET)
    assert consumed_a_stress_energy_review["status"] == "paused"
    assert consumed_a_stress_energy_review["review_result"] == a_stress_energy_review_result
    assert (
        consumed_a_stress_energy_review["selected_next_target"]
        == A_AFTER_STRESS_SELECTOR_TARGET
    )
    assert consumed_a_stress_energy_review["stress_energy_route_accepted"] == "yes"
    assert consumed_a_stress_energy_review["gauge_stress_energy_route_accepted"] == "yes"
    assert consumed_a_stress_energy_review["current_route_derived"] == "no"
    assert consumed_a_stress_energy_review["J_nu_derived"] == "no"
    assert consumed_a_stress_energy_review["current_conservation_proved"] == "no"
    assert consumed_a_stress_energy_review["A_source_admissibility_proved"] == "no"
    assert consumed_a_stress_energy_review["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed_a_stress_energy_review["em_closure_claimed"] == "no"
    assert consumed_a_stress_energy_review["qft_gr_closure_claimed"] == "no"
    assert consumed_a_stress_energy_review["master_action_promoted"] == "no"

    consumed_a_stress_energy_packet = _workstream(payload, A_STRESS_ENERGY_PACKET_TARGET)
    assert consumed_a_stress_energy_packet["status"] == "paused"
    assert (
        consumed_a_stress_energy_packet["a_stress_energy_route_result"]
        == "GAUGE_STRESS_ENERGY_ROUTE_RECORDED_NO_SOURCE_ADMISSIBILITY_OR_EM_CLOSURE"
    )
    assert consumed_a_stress_energy_packet["selected_next_target"] == A_STRESS_ENERGY_REVIEW_TARGET
    assert consumed_a_stress_energy_packet["stress_energy_route_recorded"] == "yes"
    assert consumed_a_stress_energy_packet["stress_energy_T_A_derived"] == "yes"
    assert consumed_a_stress_energy_packet["current_route_derived"] == "no"
    assert consumed_a_stress_energy_packet["J_nu_derived"] == "no"
    assert consumed_a_stress_energy_packet["current_conservation_proved"] == "no"
    assert consumed_a_stress_energy_packet["A_source_admissibility_proved"] == "no"
    assert consumed_a_stress_energy_packet["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed_a_stress_energy_packet["em_closure_claimed"] == "no"
    assert consumed_a_stress_energy_packet["qft_gr_closure_claimed"] == "no"
    assert consumed_a_stress_energy_packet["master_action_promoted"] == "no"

    consumed_a_route_selector = _workstream(payload, A_ROUTE_SELECTOR_TARGET)
    assert consumed_a_route_selector["status"] == "paused"
    assert consumed_a_route_selector["selection_result"] == a_route_selection_result
    assert consumed_a_route_selector["selected_next_target"] == A_STRESS_ENERGY_PACKET_TARGET
    assert consumed_a_route_selector["selected_route_id"] == "A_stress_energy_route"
    assert consumed_a_route_selector["route_option_count"] == "5"
    assert consumed_a_route_selector["stress_energy_route_selected"] == "yes"
    assert consumed_a_route_selector["stress_energy_route_packet_authorized"] == "yes"
    assert consumed_a_route_selector["stress_energy_derivation_executed"] == "no"
    assert consumed_a_route_selector["stress_energy_T_A_derived"] == "no"
    assert consumed_a_route_selector["current_route_derived"] == "no"
    assert consumed_a_route_selector["J_nu_derived"] == "no"
    assert consumed_a_route_selector["current_conservation_proved"] == "no"
    assert consumed_a_route_selector["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed_a_route_selector["nonabelian_route_selected"] == "no"
    assert consumed_a_route_selector["em_closure_claimed"] == "no"
    assert consumed_a_route_selector["qft_gr_closure_claimed"] == "no"
    assert consumed_a_route_selector["master_action_promoted"] == "no"

    consumed_a_vacuum_review = _workstream(payload, A_VACUUM_RETRY_REVIEW_TARGET)
    assert consumed_a_vacuum_review["status"] == "paused"
    assert consumed_a_vacuum_review["review_result"] == (
        a_vacuum_variation_retry_review_result
    )
    assert consumed_a_vacuum_review["selected_next_target"] == A_ROUTE_SELECTOR_TARGET
    assert consumed_a_vacuum_review["vacuum_u1_gauge_route_accepted"] == "yes"
    assert consumed_a_vacuum_review["source_route_shape_only_preserved"] == "yes"
    assert consumed_a_vacuum_review["selector_authorized"] == "yes"
    assert consumed_a_vacuum_review[
        "recommended_selector_candidate"
    ] == A_STRESS_ENERGY_PACKET_TARGET
    assert consumed_a_vacuum_review["stress_energy_route_selected_here"] == "no"
    assert consumed_a_vacuum_review["current_route_derived"] == "no"
    assert consumed_a_vacuum_review["matter_current_J_nu_derived"] == "no"
    assert consumed_a_vacuum_review["stress_energy_T_A_derived"] == "no"
    assert consumed_a_vacuum_review["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed_a_vacuum_review["em_closure_claimed"] == "no"
    assert consumed_a_vacuum_review["qft_gr_closure_claimed"] == "no"
    assert consumed_a_vacuum_review["master_action_promoted"] == "no"

    consumed_a_vacuum_retry_packet = _workstream(payload, A_VACUUM_RETRY_PACKET_TARGET)
    assert consumed_a_vacuum_retry_packet["status"] == "paused"
    assert consumed_a_vacuum_retry_packet[
        "a_vacuum_variation_retry_result"
    ] == "VACUUM_GAUGE_VARIATION_ROUTE_CONSTRUCTED_NO_CURRENT_DERIVATION_OR_EM_CLOSURE"
    assert (
        consumed_a_vacuum_retry_packet["selected_next_target"]
        == A_VACUUM_RETRY_REVIEW_TARGET
    )
    assert consumed_a_vacuum_retry_packet[
        "vacuum_gauge_variation_route_constructed"
    ] == "yes"
    assert consumed_a_vacuum_retry_packet[
        "vacuum_euler_lagrange_route"
    ] == "nabla_mu F^{mu nu} = 0"
    assert consumed_a_vacuum_retry_packet["source_current_route_still_blocked"] == "yes"
    assert consumed_a_vacuum_retry_packet["current_route_derived"] == "no"
    assert consumed_a_vacuum_retry_packet["matter_current_J_nu_derived"] == "no"
    assert consumed_a_vacuum_retry_packet["stress_energy_T_A_derived"] == "no"
    assert consumed_a_vacuum_retry_packet["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed_a_vacuum_retry_packet["em_closure_claimed"] == "no"
    assert consumed_a_vacuum_retry_packet["qft_gr_closure_claimed"] == "no"
    assert consumed_a_vacuum_retry_packet["master_action_promoted"] == "no"

    consumed_a_gauge_policy_packet = _workstream(payload, A_GAUGE_POLICY_TARGET)
    assert consumed_a_gauge_policy_packet["status"] == "paused"
    assert (
        consumed_a_gauge_policy_packet["a_gauge_policy_packet_result"]
        == a_gauge_policy_packet_result
    )
    assert consumed_a_gauge_policy_packet["selected_next_target"] == A_VACUUM_RETRY_PACKET_TARGET
    assert consumed_a_gauge_policy_packet["u1_route_selected"] == "yes"
    assert consumed_a_gauge_policy_packet["definition_of_F_selected"] == "yes"
    assert consumed_a_gauge_policy_packet["current_derivation_blocked"] == "yes"
    assert consumed_a_gauge_policy_packet["external_current_policy_selected"] == "no"
    assert consumed_a_gauge_policy_packet["psi_derived_current_deferred"] == "yes"
    assert consumed_a_gauge_policy_packet["maxwell_equations_derived"] == "no"
    assert consumed_a_gauge_policy_packet["current_conservation_proved"] == "no"
    assert consumed_a_gauge_policy_packet["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed_a_gauge_policy_packet["em_closure_claimed"] == "no"
    assert consumed_a_gauge_policy_packet["qft_gr_closure_claimed"] == "no"
    assert consumed_a_gauge_policy_packet["master_action_promoted"] == "no"

    consumed_a_surface_review = _workstream(payload, A_SURFACE_ROUTE_REVIEW_TARGET)
    assert consumed_a_surface_review["status"] == "paused"
    assert consumed_a_surface_review["review_result"] == a_surface_route_review_result
    assert (
        consumed_a_surface_review["a_surface_route_packet_result"]
        == a_surface_route_packet_result
    )
    assert consumed_a_surface_review["selected_next_target"] == A_GAUGE_POLICY_TARGET
    assert consumed_a_surface_review["raw_A_to_F_route_preserved"] == "yes"
    assert consumed_a_surface_review["raw_variation_route_preserved"] == "yes"
    assert consumed_a_surface_review["source_form_recorded_as_shape_only"] == "yes"
    assert consumed_a_surface_review["gauge_policy_packet_authorized"] == "yes"
    assert consumed_a_surface_review["gauge_group_selected"] == "no"
    assert consumed_a_surface_review["matter_current_J_nu_derived"] == "no"
    assert consumed_a_surface_review["current_conservation_proved"] == "no"
    assert consumed_a_surface_review["C_k_analogues_constructed"] == "no"
    assert consumed_a_surface_review["em_closure_claimed"] == "no"
    assert consumed_a_surface_review["qft_gr_closure_claimed"] == "no"
    assert consumed_a_surface_review["master_action_promoted"] == "no"

    consumed_a_surface_packet = _workstream(payload, A_SURFACE_ROUTE_PACKET_TARGET)
    assert consumed_a_surface_packet["status"] == "paused"
    assert (
        consumed_a_surface_packet["a_surface_route_packet_result"]
        == a_surface_route_packet_result
    )
    assert consumed_a_surface_packet["selected_next_target"] == (
        A_SURFACE_ROUTE_REVIEW_TARGET
    )
    assert consumed_a_surface_packet["a_surface_variation_route_prepared"] == "yes"
    assert consumed_a_surface_packet["source_route_shape_only_not_derived"] == "yes"
    assert consumed_a_surface_packet["gauge_group_selected"] == "no"
    assert consumed_a_surface_packet["matter_current_J_nu_derived"] == "no"
    assert consumed_a_surface_packet["current_conservation_proved"] == "no"
    assert consumed_a_surface_packet["C_k_analogues_constructed"] == "no"
    assert consumed_a_surface_packet["em_closure_claimed"] == "no"
    assert consumed_a_surface_packet["qft_gr_closure_claimed"] == "no"
    assert consumed_a_surface_packet["master_action_promoted"] == "no"

    consumed_master_action_surface_selector = _workstream(
        payload, MASTER_ACTION_SURFACE_SELECTOR_TARGET
    )
    assert consumed_master_action_surface_selector["status"] == "paused"
    assert consumed_master_action_surface_selector["selection_result"] == (
        "MASTER_ACTION_SURFACE_SELECTION_AFTER_PHI_CK_TRIAD_SELECTS_A_SURFACE_"
        "GAUGE_ROUTE_NO_VARIATION_OR_PROMOTION"
    )
    assert consumed_master_action_surface_selector["selected_next_target"] == (
        A_SURFACE_ROUTE_PACKET_TARGET
    )
    assert consumed_master_action_surface_selector[
        "selected_master_action_surface"
    ] == "A_surface_gauge_route"
    assert consumed_master_action_surface_selector["selected_surface_symbol"] == "A"
    assert consumed_master_action_surface_selector[
        "selected_route_packet_authorized"
    ] == "yes"
    assert consumed_master_action_surface_selector[
        "selected_route_execution_authorized"
    ] == "no"
    assert consumed_master_action_surface_selector[
        "a_surface_gauge_route_selected"
    ] == "yes"
    assert consumed_master_action_surface_selector[
        "a_surface_gauge_route_packet_authorized"
    ] == "yes"
    assert consumed_master_action_surface_selector[
        "a_surface_variation_executed"
    ] == "no"
    assert consumed_master_action_surface_selector[
        "gauge_field_derived"
    ] == "no"
    assert consumed_master_action_surface_selector[
        "maxwell_equations_derived"
    ] == "no"
    assert consumed_master_action_surface_selector[
        "current_conservation_proved"
    ] == "no"
    assert consumed_master_action_surface_selector[
        "new_ck_rules_constructed"
    ] == "no"
    assert consumed_master_action_surface_selector[
        "full_toeformal_aggregate_status_for_packet"
    ] == "NOT_RUN"
    assert consumed_master_action_surface_selector["qft_gr_closure_claimed"] == "no"
    assert consumed_master_action_surface_selector["em_closure_claimed"] == "no"
    assert consumed_master_action_surface_selector["master_action_promoted"] == "no"

    consumed_source_bridge_transport_closeout = _workstream(
        payload, PHI_CK_SOURCE_BRIDGE_TRANSPORT_CLOSEOUT_TARGET
    )
    assert consumed_source_bridge_transport_closeout["status"] == "paused"
    assert consumed_source_bridge_transport_closeout["closeout_result"] == (
        "PHI_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_CLOSED_AS_THREE_RULE_"
        "ADMISSIBILITY_FAMILY_NO_ACTION_VARIATION_OR_PROMOTION"
    )
    assert consumed_source_bridge_transport_closeout["selected_next_target"] == (
        MASTER_ACTION_SURFACE_SELECTOR_TARGET
    )
    assert consumed_source_bridge_transport_closeout[
        "first_phi_relevant_three_rule_ck_family_closed"
    ] == "yes"
    assert consumed_source_bridge_transport_closeout[
        "source_bridge_transport_admissibility_rule_family_closed"
    ] == "yes"
    assert consumed_source_bridge_transport_closeout[
        "all_three_rules_admissibility_only"
    ] == "yes"
    assert consumed_source_bridge_transport_closeout[
        "all_three_rules_not_action_terms"
    ] == "yes"
    assert consumed_source_bridge_transport_closeout[
        "all_three_rules_not_action_embedded"
    ] == "yes"
    assert consumed_source_bridge_transport_closeout[
        "all_three_rules_not_varied"
    ] == "yes"
    assert consumed_source_bridge_transport_closeout[
        "all_three_rules_not_promoted"
    ] == "yes"
    assert consumed_source_bridge_transport_closeout[
        "selector_target_authorized"
    ] == "yes"
    assert consumed_source_bridge_transport_closeout[
        "selector_target_prepared"
    ] == "no"
    assert consumed_source_bridge_transport_closeout[
        "recommended_next_master_action_surface"
    ] == "A_surface_gauge_route"
    assert consumed_source_bridge_transport_closeout[
        "next_master_action_surface_selected"
    ] == "no"
    assert consumed_source_bridge_transport_closeout[
        "full_toeformal_aggregate_status_for_packet"
    ] == "NOT_RUN"
    assert consumed_source_bridge_transport_closeout["ck_variation_executed"] == "no"
    assert consumed_source_bridge_transport_closeout["qft_gr_closure_claimed"] == "no"
    assert consumed_source_bridge_transport_closeout["master_action_promoted"] == "no"

    consumed_source_bridge_transport_review = _workstream(
        payload, PHI_CK_SOURCE_BRIDGE_TRANSPORT_REVIEW_TARGET
    )
    assert consumed_source_bridge_transport_review["status"] == "paused"
    assert consumed_source_bridge_transport_review["review_result"] == (
        "PHI_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_"
        "ACCEPTS_THREE_RULE_SYNTHESIS_NO_ACTION_VARIATION_OR_PROMOTION"
    )
    assert consumed_source_bridge_transport_review["selected_next_target"] == (
        PHI_CK_SOURCE_BRIDGE_TRANSPORT_CLOSEOUT_TARGET
    )
    assert consumed_source_bridge_transport_review[
        "three_rule_family_review_accepted"
    ] == "yes"
    assert consumed_source_bridge_transport_review[
        "all_three_rules_admissibility_only"
    ] == "yes"
    assert consumed_source_bridge_transport_review[
        "all_three_rules_not_action_terms"
    ] == "yes"
    assert consumed_source_bridge_transport_review[
        "none_of_three_rules_derives_phi"
    ] == "yes"
    assert consumed_source_bridge_transport_review[
        "none_of_three_rules_derives_v_phi"
    ] == "yes"
    assert consumed_source_bridge_transport_review[
        "triad_closeout_authorized"
    ] == "yes"
    assert consumed_source_bridge_transport_review[
        "triad_closeout_prepared"
    ] == "no"
    assert consumed_source_bridge_transport_review[
        "full_toeformal_aggregate_status_for_packet"
    ] == "NOT_RUN"
    assert consumed_source_bridge_transport_review["ck_variation_executed"] == "no"
    assert consumed_source_bridge_transport_review["qft_gr_closure_claimed"] == "no"
    assert consumed_source_bridge_transport_review["master_action_promoted"] == "no"

    consumed_source_bridge_transport_synthesis = _workstream(
        payload, PHI_CK_SOURCE_BRIDGE_TRANSPORT_SYNTHESIS_PACKET_TARGET
    )
    assert consumed_source_bridge_transport_synthesis["status"] == "paused"
    assert consumed_source_bridge_transport_synthesis["packet_result"] == (
        "PHI_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_PACKET_PREPARED_"
        "THREE_ADMISSIBILITY_RULES_SYNTHESIZED_NO_ACTION_VARIATION_OR_PROMOTION"
    )
    assert consumed_source_bridge_transport_synthesis["selected_next_target"] == (
        PHI_CK_SOURCE_BRIDGE_TRANSPORT_REVIEW_TARGET
    )
    assert consumed_source_bridge_transport_synthesis[
        "three_rule_family_synthesized"
    ] == "yes"
    assert consumed_source_bridge_transport_synthesis[
        "all_three_rules_admissibility_only"
    ] == "yes"
    assert consumed_source_bridge_transport_synthesis[
        "all_three_rules_not_action_terms"
    ] == "yes"
    assert consumed_source_bridge_transport_synthesis[
        "none_of_three_rules_derives_phi"
    ] == "yes"
    assert consumed_source_bridge_transport_synthesis[
        "none_of_three_rules_derives_v_phi"
    ] == "yes"
    assert consumed_source_bridge_transport_synthesis[
        "full_toeformal_aggregate_status_for_packet"
    ] == "NOT_RUN"
    assert consumed_source_bridge_transport_synthesis["ck_variation_executed"] == "no"
    assert consumed_source_bridge_transport_synthesis["qft_gr_closure_claimed"] == "no"
    assert consumed_source_bridge_transport_synthesis["master_action_promoted"] == "no"

    consumed_transport_closeout = _workstream(payload, PHI_TRANSPORT_CLOSEOUT_TARGET)
    assert consumed_transport_closeout["status"] == "paused"
    assert consumed_transport_closeout["closeout_result"] == (
        "PHI_TRANSPORT_CONSISTENCY_CK_ADMISSIBILITY_RULE_CLOSED_AS_DERIVATION_"
        "CHAIN_STABILITY_RULE_NO_ACTION_VARIATION_OR_PROMOTION"
    )
    assert consumed_transport_closeout["selected_next_target"] == (
        PHI_CK_SOURCE_BRIDGE_TRANSPORT_SYNTHESIS_PACKET_TARGET
    )
    assert consumed_transport_closeout[
        "three_rule_family_synthesis_packet_authorized"
    ] == "yes"
    assert consumed_transport_closeout["ck_variation_executed"] == "no"
    assert consumed_transport_closeout["qft_gr_closure_claimed"] == "no"
    assert consumed_transport_closeout["master_action_promoted"] == "no"

    consumed_transport_functional_embedding_review = _workstream(
        payload, PHI_TRANSPORT_FUNCTIONAL_EMBEDDING_REVIEW_TARGET
    )
    assert consumed_transport_functional_embedding_review["status"] == "paused"
    assert consumed_transport_functional_embedding_review["review_result"] == (
        "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_RESULT_REVIEW_ACCEPTS_"
        "ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_OR_PROMOTION"
    )
    assert consumed_transport_functional_embedding_review["selected_next_target"] == (
        PHI_TRANSPORT_CLOSEOUT_TARGET
    )
    assert consumed_transport_functional_embedding_review[
        "transport_constraint_equation"
    ] == "C_transport^phi = 0"
    assert consumed_transport_functional_embedding_review[
        "review_accepts_admissibility_only_route"
    ] == "yes"
    assert consumed_transport_functional_embedding_review[
        "packet_result_review_accepts_admissibility_only_route"
    ] == "yes"
    assert consumed_transport_functional_embedding_review[
        "transport_admissibility_rule_closeout_authorized"
    ] == "yes"
    assert consumed_transport_functional_embedding_review[
        "transport_admissibility_rule_closeout_prepared"
    ] == "no"
    assert consumed_transport_functional_embedding_review[
        "admissibility_only_route_selected"
    ] == "yes"
    assert consumed_transport_functional_embedding_review[
        "lagrange_multiplier_route_blocked"
    ] == "yes"
    assert consumed_transport_functional_embedding_review[
        "penalty_route_licensed"
    ] == "no"
    assert consumed_transport_functional_embedding_review[
        "direct_dynamical_law_interpretation_blocked"
    ] == "yes"
    assert consumed_transport_functional_embedding_review[
        "transport_candidate_functional_defined"
    ] == "no"
    assert consumed_transport_functional_embedding_review[
        "transport_consistency_proved"
    ] == "no"
    assert consumed_transport_functional_embedding_review[
        "ck_variation_executed"
    ] == "no"
    assert consumed_transport_functional_embedding_review[
        "qft_gr_closure_claimed"
    ] == "no"
    assert consumed_transport_functional_embedding_review[
        "master_action_promoted"
    ] == "no"
    assert consumed_transport_functional_embedding_review[
        "full_toeformal_aggregate_status_for_packet"
    ] == "NOT_RUN"

    consumed_transport_functional_embedding = _workstream(
        payload, PHI_TRANSPORT_FUNCTIONAL_EMBEDDING_PACKET_TARGET
    )
    assert consumed_transport_functional_embedding["status"] == "paused"
    assert consumed_transport_functional_embedding["packet_result"] == (
        "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_OPTIONS_RECORDED_"
        "ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
    )
    assert consumed_transport_functional_embedding["selected_next_target"] == (
        PHI_TRANSPORT_FUNCTIONAL_EMBEDDING_REVIEW_TARGET
    )
    assert consumed_transport_functional_embedding[
        "transport_constraint_equation"
    ] == "C_transport^phi = 0"
    assert consumed_transport_functional_embedding[
        "admissibility_only_route_selected"
    ] == "yes"
    assert consumed_transport_functional_embedding[
        "lagrange_multiplier_route_blocked"
    ] == "yes"
    assert consumed_transport_functional_embedding["penalty_route_licensed"] == "no"
    assert consumed_transport_functional_embedding[
        "direct_dynamical_law_interpretation_blocked"
    ] == "yes"
    assert consumed_transport_functional_embedding[
        "transport_candidate_functional_defined"
    ] == "no"
    assert consumed_transport_functional_embedding["transport_consistency_proved"] == "no"
    assert consumed_transport_functional_embedding["ck_variation_executed"] == "no"
    assert consumed_transport_functional_embedding["qft_gr_closure_claimed"] == "no"
    assert consumed_transport_functional_embedding["master_action_promoted"] == "no"
    assert consumed_transport_functional_embedding[
        "full_toeformal_aggregate_status_for_packet"
    ] == "NOT_RUN"

    consumed_transport_review = _workstream(payload, PHI_TRANSPORT_CANDIDATE_REVIEW_TARGET)
    assert consumed_transport_review["status"] == "paused"
    assert consumed_transport_review["review_result"] == (
        "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_RESULT_REVIEW_ACCEPTS_"
        "DERIVATION_CHAIN_STABILITY_CANDIDATE_NO_FUNCTIONALIZATION_OR_PROMOTION"
    )
    assert consumed_transport_review["selected_next_target"] == (
        PHI_TRANSPORT_FUNCTIONAL_EMBEDDING_PACKET_TARGET
    )
    assert consumed_transport_review[
        "transport_constraint_equation"
    ] == "C_transport^phi = 0"
    assert consumed_transport_review[
        "review_accepts_derivation_chain_stability_candidate"
    ] == "yes"
    assert consumed_transport_review[
        "functional_embedding_packet_authorized"
    ] == "yes"
    assert consumed_transport_review["functional_embedding_packet_prepared"] == "no"
    assert consumed_transport_review["transport_candidate_functional_defined"] == "no"
    assert consumed_transport_review["transport_consistency_proved"] == "no"
    assert consumed_transport_review["ck_variation_executed"] == "no"
    assert consumed_transport_review["qft_gr_closure_claimed"] == "no"
    assert consumed_transport_review["master_action_promoted"] == "no"
    assert consumed_transport_review[
        "full_toeformal_aggregate_status_for_packet"
    ] == "NOT_RUN"

    consumed_transport_candidate = _workstream(
        payload, PHI_TRANSPORT_CANDIDATE_PACKET_TARGET
    )
    assert consumed_transport_candidate["status"] == "paused"
    assert consumed_transport_candidate["packet_result"] == (
        "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_RECORDED_AS_"
        "DERIVATION_CHAIN_STABILITY_RULE_NO_VARIATION_OR_PROMOTION"
    )
    assert (
        consumed_transport_candidate["selected_next_target"]
        == PHI_TRANSPORT_CANDIDATE_REVIEW_TARGET
    )
    assert consumed_transport_candidate[
        "transport_candidate_id"
    ] == "phi_transport_derivation_chain_stability_ck_candidate"
    assert consumed_transport_candidate[
        "transport_constraint_equation"
    ] == "C_transport^phi = 0"
    assert consumed_transport_candidate[
        "transport_candidate_recorded_as_admissibility_rule"
    ] == "yes"
    assert consumed_transport_candidate[
        "transport_candidate_functional_defined"
    ] == "no"
    assert consumed_transport_candidate["transport_consistency_proved"] == "no"
    assert consumed_transport_candidate["result_review_authorized"] == "yes"
    assert consumed_transport_candidate["review_prepared"] == "no"
    assert consumed_transport_candidate["ck_variation_executed"] == "no"
    assert consumed_transport_candidate["qft_gr_closure_claimed"] == "no"
    assert consumed_transport_candidate["master_action_promoted"] == "no"
    assert consumed_transport_candidate[
        "full_toeformal_aggregate_status_for_packet"
    ] == "NOT_RUN"

    consumed_transport_selector = _workstream(payload, PHI_TRANSPORT_SELECTOR_TARGET)
    assert consumed_transport_selector["status"] == "paused"
    assert consumed_transport_selector["selection_result"] == (
        "CK_CONSTRAINT_FAMILY_SELECTION_SELECTS_TRANSPORT_CONSISTENCY_AFTER_PHI_"
        "SOURCE_AND_BRIDGE_ADMISSIBILITY_NO_CK_VARIATION_OR_PROMOTION"
    )
    assert (
        consumed_transport_selector["selected_next_target"]
        == PHI_TRANSPORT_CANDIDATE_PACKET_TARGET
    )
    assert consumed_transport_selector[
        "selected_ck_option_class"
    ] == "transport_consistency_constraint"
    assert consumed_transport_selector[
        "selected_ck_constraint_family"
    ] == "transport_consistency_ck_constraint_family"
    assert consumed_transport_selector[
        "transport_consistency_family_selected"
    ] == "yes"
    assert consumed_transport_selector[
        "transport_consistency_candidate_packet_authorized"
    ] == "yes"
    assert consumed_transport_selector[
        "transport_consistency_candidate_packet_prepared"
    ] == "no"
    assert consumed_transport_selector["transport_consistency_proved"] == "no"
    assert consumed_transport_selector["ck_variation_executed"] == "no"
    assert consumed_transport_selector["qft_gr_closure_claimed"] == "no"
    assert consumed_transport_selector["master_action_promoted"] == "no"

    consumed_synthesis_closeout = _workstream(payload, PHI_CK_SYNTHESIS_CLOSEOUT_TARGET)
    assert consumed_synthesis_closeout["status"] == "paused"
    assert consumed_synthesis_closeout["closeout_result"] == (
        "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_CLOSED_AS_SOURCE_AND_BRIDGE_"
        "ADMISSIBILITY_RULE_FAMILY_NO_ACTION_VARIATION_OR_PROMOTION"
    )
    assert consumed_synthesis_closeout["selected_next_target"] == (
        PHI_TRANSPORT_SELECTOR_TARGET
    )
    assert consumed_synthesis_closeout[
        "closeout_accepted"
    ] == "yes"
    assert consumed_synthesis_closeout[
        "first_synthesized_phi_relevant_ck_admissibility_rule_family_closed"
    ] == "yes"
    assert consumed_synthesis_closeout[
        "source_and_bridge_admissibility_rule_family_closed"
    ] == "yes"
    assert consumed_synthesis_closeout[
        "selector_target_authorized"
    ] == "yes"
    assert consumed_synthesis_closeout[
        "selector_target_prepared"
    ] == "no"
    assert consumed_synthesis_closeout[
        "full_toeformal_aggregate_status_for_packet"
    ] == "NOT_RUN"
    assert consumed_synthesis_closeout["ck_variation_executed"] == "no"
    assert consumed_synthesis_closeout["qft_gr_closure_claimed"] == "no"
    assert consumed_synthesis_closeout["master_action_promoted"] == "no"
    consumed_synthesis_review = _workstream(
        payload, PHI_CK_SYNTHESIS_RESULT_REVIEW_TARGET
    )
    assert consumed_synthesis_review["status"] == "paused"
    assert consumed_synthesis_review["review_result"] == (
        "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_ACCEPTS_SOURCE_"
        "AND_BRIDGE_RULE_SYNTHESIS_NO_ACTION_VARIATION_OR_PROMOTION"
    )
    assert (
        consumed_synthesis_review["selected_next_target"]
        == PHI_CK_SYNTHESIS_CLOSEOUT_TARGET
    )
    assert consumed_synthesis_review[
        "source_rule_synthesis_accepted"
    ] == "yes"
    assert consumed_synthesis_review[
        "bridge_rule_synthesis_accepted"
    ] == "yes"
    assert consumed_synthesis_review[
        "synthesis_closeout_authorized"
    ] == "yes"
    assert consumed_synthesis_review[
        "full_toeformal_aggregate_status_for_packet"
    ] == "NOT_RUN"
    assert consumed_synthesis_review["ck_variation_executed"] == "no"
    assert consumed_synthesis_review["qft_gr_closure_claimed"] == "no"
    assert consumed_synthesis_review["master_action_promoted"] == "no"
    consumed_synthesis_packet = _workstream(payload, PHI_CK_SYNTHESIS_PACKET_TARGET)
    assert consumed_synthesis_packet["status"] == "paused"
    assert consumed_synthesis_packet["packet_result"] == (
        "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_PACKET_PREPARED_SOURCE_AND_"
        "BRIDGE_RULES_SYNTHESIZED_NO_ACTION_VARIATION_OR_PROMOTION"
    )
    assert (
        consumed_synthesis_packet["selected_next_target"]
        == PHI_CK_SYNTHESIS_RESULT_REVIEW_TARGET
    )
    assert consumed_synthesis_packet[
        "source_admissibility_rule_synthesized"
    ] == "yes"
    assert consumed_synthesis_packet[
        "bridge_admissibility_rule_synthesized"
    ] == "yes"
    assert consumed_synthesis_packet[
        "both_rules_admissibility_only"
    ] == "yes"
    assert consumed_synthesis_packet[
        "both_rules_not_action_terms"
    ] == "yes"
    assert consumed_synthesis_packet[
        "full_toeformal_aggregate_status_for_packet"
    ] == "NOT_RUN"
    assert consumed_synthesis_packet["ck_variation_executed"] == "no"
    assert consumed_synthesis_packet["qft_gr_closure_claimed"] == "no"
    assert consumed_synthesis_packet["master_action_promoted"] == "no"

    consumed_bridge_closeout = _workstream(payload, PHI_BRIDGE_CLOSEOUT_TARGET)
    assert consumed_bridge_closeout["status"] == "paused"
    assert consumed_bridge_closeout["closeout_result"] == (
        "PHI_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSED_AS_ROUTE_"
        "CONSISTENCY_RULE_NO_ACTION_VARIATION_OR_PROMOTION"
    )
    assert consumed_bridge_closeout["selected_next_target"] == PHI_CK_SYNTHESIS_PACKET_TARGET
    assert consumed_bridge_closeout[
        "admissibility_rule_closeout_prepared"
    ] == "yes"
    assert consumed_bridge_closeout[
        "second_phi_relevant_ck_admissibility_rule_candidate_closed"
    ] == "yes"
    assert consumed_bridge_closeout[
        "bridge_admissibility_rule_candidate_closed"
    ] == "yes"
    assert consumed_bridge_closeout[
        "rule_family_synthesis_packet_authorized"
    ] == "yes"
    assert consumed_bridge_closeout[
        "rule_family_synthesis_packet_prepared"
    ] == "no"
    assert consumed_bridge_closeout["ck_variation_executed"] == "no"
    assert consumed_bridge_closeout["bridge_admissibility_proved"] == "no"
    assert consumed_bridge_closeout["qft_gr_closure_claimed"] == "no"
    assert consumed_bridge_closeout["master_action_promoted"] == "no"

    consumed_bridge_embedding_review = _workstream(
        payload, BRIDGE_FUNCTIONAL_EMBEDDING_REVIEW_TARGET
    )
    assert consumed_bridge_embedding_review["status"] == "paused"
    assert consumed_bridge_embedding_review["review_result"] == (
        "PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_RESULT_REVIEW_ACCEPTS_"
        "ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_OR_PROMOTION"
    )
    assert (
        consumed_bridge_embedding_review["selected_next_target"]
        == PHI_BRIDGE_CLOSEOUT_TARGET
    )
    assert consumed_bridge_embedding_review["admissibility_rule_closeout_authorized"] == "yes"
    assert consumed_bridge_embedding_review["admissibility_rule_closeout_prepared"] == "no"
    assert consumed_bridge_embedding_review["admissibility_only_route_selected"] == "yes"
    assert consumed_bridge_embedding_review["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed_bridge_embedding_review["penalty_route_licensed"] == "no"
    assert consumed_bridge_embedding_review["ck_variation_executed"] == "no"
    assert consumed_bridge_embedding_review["bridge_admissibility_proved"] == "no"
    assert consumed_bridge_embedding_review["qft_gr_closure_claimed"] == "no"
    assert consumed_bridge_embedding_review["master_action_promoted"] == "no"

    consumed_bridge_embedding_packet = _workstream(
        payload, "prepare_phi_bridge_admissibility_ck_functional_embedding_packet"
    )
    assert consumed_bridge_embedding_packet["status"] == "paused"
    assert consumed_bridge_embedding_packet["packet_result"] == (
        "PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_OPTIONS_RECORDED_"
        "ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
    )
    assert consumed_bridge_embedding_packet["selected_next_target"] == (
        BRIDGE_FUNCTIONAL_EMBEDDING_REVIEW_TARGET
    )
    assert consumed_bridge_embedding_packet["bridge_candidate_id"] == (
        "phi_bridge_route_consistency_ck_candidate"
    )
    assert consumed_bridge_embedding_packet["bridge_constraint_equation"] == (
        "C_bridge^phi = 0"
    )
    assert consumed_bridge_embedding_packet["embedding_route_count"] == "3"
    assert (
        consumed_bridge_embedding_packet["selected_embedding_route_id"]
        == "phi_bridge_ck_admissibility_only_route"
    )
    assert consumed_bridge_embedding_packet["admissibility_only_route_selected"] == "yes"
    assert consumed_bridge_embedding_packet["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed_bridge_embedding_packet["penalty_route_licensed"] == "no"
    assert consumed_bridge_embedding_packet["component_pairing_rule_selected"] == "no"
    assert consumed_bridge_embedding_packet["ck_variation_executed"] == "no"
    assert consumed_bridge_embedding_packet["bridge_admissibility_claimed"] == "no"
    assert consumed_bridge_embedding_packet["qft_gr_closure_claimed"] == "no"
    assert consumed_bridge_embedding_packet["master_action_promoted"] == "no"

    consumed_bridge_candidate = _workstream(
        payload, "prepare_phi_bridge_admissibility_ck_constraint_candidate_packet"
    )
    assert consumed_bridge_candidate["status"] == "paused"
    assert consumed_bridge_candidate["packet_result"] == (
        "PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_RECORDED_AS_ROUTE_"
        "CONSISTENCY_RULE_NO_VARIATION_OR_PROMOTION"
    )
    assert consumed_bridge_candidate["selected_next_target"] == (
        "review_phi_bridge_admissibility_ck_constraint_candidate_packet_result"
    )
    assert consumed_bridge_candidate["bridge_candidate_id"] == (
        "phi_bridge_route_consistency_ck_candidate"
    )
    assert consumed_bridge_candidate["bridge_constraint_equation"] == (
        "C_bridge^phi = 0"
    )
    assert consumed_bridge_candidate["bridge_candidate_recorded_as_admissibility_rule"] == "yes"
    assert consumed_bridge_candidate["route_consistency_tuple_recorded"] == "yes"
    assert consumed_bridge_candidate["field_equation_match_recorded"] == "yes"
    assert consumed_bridge_candidate["stress_energy_match_recorded"] == "yes"
    assert consumed_bridge_candidate["source_residual_match_recorded"] == "yes"
    assert consumed_bridge_candidate["bridge_candidate_functional_defined"] == "no"
    assert consumed_bridge_candidate["bridge_candidate_rule_proved"] == "no"
    assert consumed_bridge_candidate["bridge_route_alignment_verified"] == "no"
    assert consumed_bridge_candidate["ck_variation_executed"] == "no"
    assert consumed_bridge_candidate["source_admissibility_claimed"] == "no"
    assert consumed_bridge_candidate["bridge_admissibility_claimed"] == "no"
    assert consumed_bridge_candidate["qft_gr_closure_claimed"] == "no"
    assert consumed_bridge_candidate["master_action_promoted"] == "no"

    consumed_bridge_selector = _workstream(
        payload, "select_next_phi_relevant_ck_constraint_family_after_source_admissibility"
    )
    assert consumed_bridge_selector["status"] == "paused"
    assert consumed_bridge_selector["selection_result"] == (
        "PHI_RELEVANT_CK_CONSTRAINT_FAMILY_SELECTION_SELECTS_BRIDGE_"
        "ADMISSIBILITY_AFTER_SOURCE_ADMISSIBILITY_NO_CK_VARIATION_OR_PROMOTION"
    )
    assert consumed_bridge_selector["selected_next_target"] == (
        "prepare_phi_bridge_admissibility_ck_constraint_candidate_packet"
    )
    assert consumed_bridge_selector["selected_ck_option_class"] == (
        "bridge_admissibility_constraint"
    )
    assert consumed_bridge_selector["selected_ck_constraint_family"] == (
        "phi_bridge_admissibility_constraint_family"
    )
    assert consumed_bridge_selector["source_selected_ck_constraint_family"] == (
        "phi_source_admissibility_constraint_family"
    )
    assert consumed_bridge_selector["bridge_admissibility_family_selected"] == "yes"
    assert consumed_bridge_selector["bridge_admissibility_candidate_packet_authorized"] == "yes"
    assert consumed_bridge_selector["bridge_candidate_functional_defined"] == "no"
    assert consumed_bridge_selector["bridge_route_alignment_verified"] == "no"
    assert consumed_bridge_selector["ck_variation_executed"] == "no"
    assert consumed_bridge_selector["source_admissibility_claimed"] == "no"
    assert consumed_bridge_selector["bridge_admissibility_claimed"] == "no"
    assert consumed_bridge_selector["qft_gr_closure_claimed"] == "no"
    assert consumed_bridge_selector["master_action_promoted"] == "no"

    consumed_rule_closeout = _workstream(
        payload, "prepare_phi_source_admissibility_ck_admissibility_rule_closeout"
    )
    assert consumed_rule_closeout["status"] == "paused"
    assert consumed_rule_closeout["closeout_result"] == (
        "PHI_SOURCE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSED_AS_FIRST_PHI_"
        "RELEVANT_CK_RULE_CANDIDATE_NO_ACTION_VARIATION_OR_PROMOTION"
    )
    assert consumed_rule_closeout["selected_next_target"] == (
        "select_next_phi_relevant_ck_constraint_family_after_source_admissibility"
    )
    assert consumed_rule_closeout["admissibility_rule_closeout_prepared"] == "yes"
    assert (
        consumed_rule_closeout[
            "first_phi_relevant_ck_admissibility_rule_candidate_closed"
        ]
        == "yes"
    )
    assert consumed_rule_closeout["candidate_recorded_as_rule_only"] == "yes"
    assert consumed_rule_closeout["next_selector_authorized"] == "yes"
    assert consumed_rule_closeout["next_candidate_family_selected"] == "no"
    assert consumed_rule_closeout["bridge_admissibility_family_selected"] == "no"
    assert consumed_rule_closeout["ck_variation_executed"] == "no"
    assert consumed_rule_closeout["source_admissibility_claimed"] == "no"
    assert consumed_rule_closeout["qft_gr_closure_claimed"] == "no"
    assert consumed_rule_closeout["master_action_promoted"] == "no"

    consumed_functional_embedding_review = _workstream(
        payload, "review_phi_source_admissibility_ck_functional_embedding_packet_result"
    )
    assert consumed_functional_embedding_review["status"] == "paused"
    assert consumed_functional_embedding_review["review_result"] == (
        "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_RESULT_REVIEW_ACCEPTS_"
        "ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_OR_PROMOTION"
    )
    assert consumed_functional_embedding_review["selected_next_target"] == (
        "prepare_phi_source_admissibility_ck_admissibility_rule_closeout"
    )
    assert (
        consumed_functional_embedding_review["review_accepts_admissibility_only_route"]
        == "yes"
    )
    assert (
        consumed_functional_embedding_review["admissibility_rule_closeout_authorized"]
        == "yes"
    )
    assert consumed_functional_embedding_review["admissibility_rule_closeout_prepared"] == "no"
    assert consumed_functional_embedding_review["admissibility_only_route_selected"] == "yes"
    assert consumed_functional_embedding_review["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed_functional_embedding_review["quadratic_penalty_route_licensed"] == "no"
    assert consumed_functional_embedding_review["ck_variation_executed"] == "no"
    assert consumed_functional_embedding_review["source_admissibility_claimed"] == "no"
    assert consumed_functional_embedding_review["qft_gr_closure_claimed"] == "no"
    assert consumed_functional_embedding_review["master_action_promoted"] == "no"

    consumed_functional_embedding_packet = _workstream(
        payload, "prepare_phi_source_admissibility_ck_functional_embedding_packet"
    )
    assert consumed_functional_embedding_packet["status"] == "paused"
    assert consumed_functional_embedding_packet["packet_result"] == (
        "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_OPTIONS_RECORDED_"
        "ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
    )
    assert consumed_functional_embedding_packet["selected_next_target"] == (
        "review_phi_source_admissibility_ck_functional_embedding_packet_result"
    )
    assert consumed_functional_embedding_packet["admissibility_only_route_selected"] == "yes"
    assert consumed_functional_embedding_packet["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed_functional_embedding_packet["quadratic_penalty_route_licensed"] == "no"
    assert consumed_functional_embedding_packet["ck_variation_executed"] == "no"
    assert consumed_functional_embedding_packet["source_admissibility_claimed"] == "no"
    assert consumed_functional_embedding_packet["qft_gr_closure_claimed"] == "no"
    assert consumed_functional_embedding_packet["master_action_promoted"] == "no"

    consumed_ck_candidate_review = _workstream(
        payload, "review_phi_source_admissibility_ck_constraint_candidate_packet_result"
    )
    assert consumed_ck_candidate_review["status"] == "paused"
    assert consumed_ck_candidate_review["review_result"] == (
        "PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_RESULT_REVIEW_ACCEPTS_"
        "CONSERVATION_RESIDUAL_CANDIDATE_NO_FUNCTIONALIZATION_OR_PROMOTION"
    )
    assert consumed_ck_candidate_review["selected_next_target"] == (
        "prepare_phi_source_admissibility_ck_functional_embedding_packet"
    )
    assert consumed_ck_candidate_review["review_accepts_conservation_residual_candidate"] == "yes"
    assert consumed_ck_candidate_review["functional_embedding_packet_authorized"] == "yes"
    assert consumed_ck_candidate_review["functional_embedding_executed"] == "no"
    assert consumed_ck_candidate_review["ck_variation_executed"] == "no"
    assert consumed_ck_candidate_review["source_admissibility_claimed"] == "no"
    assert consumed_ck_candidate_review["qft_gr_closure_claimed"] == "no"
    assert consumed_ck_candidate_review["master_action_promoted"] == "no"

    consumed_phi_source_candidate = _workstream(
        payload, "prepare_phi_source_admissibility_ck_constraint_candidate_packet"
    )
    assert consumed_phi_source_candidate["status"] == "paused"
    assert consumed_phi_source_candidate["packet_result"] == (
        "PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_RECORDED_AS_"
        "CONSERVATION_RESIDUAL_NO_VARIATION_OR_PROMOTION"
    )
    assert consumed_phi_source_candidate["selected_next_target"] == (
        "review_phi_source_admissibility_ck_constraint_candidate_packet_result"
    )
    assert consumed_phi_source_candidate["candidate_constraint_id"] == (
        "phi_source_conservation_residual_ck_candidate"
    )
    assert consumed_phi_source_candidate["candidate_constraint_shape_recorded"] == "yes"
    assert consumed_phi_source_candidate["ck_variation_executed"] == "no"
    assert consumed_phi_source_candidate["source_admissibility_claimed"] == "no"
    assert consumed_phi_source_candidate["qft_gr_closure_claimed"] == "no"
    assert consumed_phi_source_candidate["master_action_promoted"] == "no"

    consumed_ck_family_selector = _workstream(
        payload, "select_master_action_ck_constraint_family_for_phi_route"
    )
    assert consumed_ck_family_selector["status"] == "paused"
    assert consumed_ck_family_selector["selection_result"] == (
        "MASTER_ACTION_CK_CONSTRAINT_FAMILY_SELECTION_SELECTS_PHI_SOURCE_"
        "ADMISSIBILITY_CONSTRAINT_FAMILY_NO_CK_FUNCTIONAL_EXECUTION_OR_PROMOTION"
    )
    assert consumed_ck_family_selector["selected_next_target"] == (
        "prepare_phi_source_admissibility_ck_constraint_candidate_packet"
    )
    assert consumed_ck_family_selector["selected_ck_option_class"] == (
        "source_admissibility_constraint"
    )
    assert consumed_ck_family_selector["selected_ck_constraint_family"] == (
        "phi_source_admissibility_constraint_family"
    )
    assert consumed_ck_family_selector["concrete_ck_functional_selected"] == "no"
    assert consumed_ck_family_selector["ck_variation_executed"] == "no"
    assert consumed_ck_family_selector["phi_generated_by_ck_claimed"] == "no"
    assert consumed_ck_family_selector["potential_derived"] == "no"
    assert consumed_ck_family_selector["source_admissibility_claimed"] == "no"
    assert consumed_ck_family_selector["qft_gr_closure_claimed"] == "no"
    assert consumed_ck_family_selector["master_action_promoted"] == "no"

    consumed_ck_definition_review = _workstream(
        payload, "review_master_action_ck_constraint_functional_definition_packet_result"
    )
    assert consumed_ck_definition_review["status"] == "paused"
    assert consumed_ck_definition_review["review_result"] == (
        "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_RESULT_REVIEW_"
        "ACCEPTS_OPTIONS_INDEX_NO_SELECTION_OR_PROMOTION"
    )
    assert consumed_ck_definition_review["selected_next_target"] == (
        "select_master_action_ck_constraint_family_for_phi_route"
    )
    assert consumed_ck_definition_review["review_accepts_options_index"] == "yes"
    assert consumed_ck_definition_review["concrete_ck_family_selected"] == "no"
    assert consumed_ck_definition_review["ck_variation_executed"] == "no"
    assert consumed_ck_definition_review["phi_generated_by_ck_claimed"] == "no"
    assert consumed_ck_definition_review["potential_derived"] == "no"
    assert consumed_ck_definition_review["source_conservation_claimed"] == "no"
    assert consumed_ck_definition_review["qft_gr_closure_claimed"] == "no"
    assert consumed_ck_definition_review["master_action_promoted"] == "no"

    consumed_ck_definition_packet = _workstream(
        payload, "prepare_master_action_ck_constraint_functional_definition_packet"
    )
    assert consumed_ck_definition_packet["status"] == "paused"
    assert consumed_ck_definition_packet["packet_result"] == (
        "CK_CONSTRAINT_FUNCTIONAL_OPTIONS_INDEXED_NO_SELECTION"
    )
    assert consumed_ck_definition_packet["selected_next_target"] == (
        "review_master_action_ck_constraint_functional_definition_packet_result"
    )
    assert (
        consumed_ck_definition_packet[
            "master_action_ck_constraint_functional_definition_packet_prepared"
        ]
        == "yes"
    )
    assert (
        consumed_ck_definition_packet["ck_constraint_functional_options_indexed"]
        == "yes"
    )
    assert (
        consumed_ck_definition_packet["ck_constraint_functional_family_selected"]
        == "no"
    )
    assert consumed_ck_definition_packet["ck_content_fully_defined"] == "no"

    scalar_conservation_active_workstream = _workstream(
        payload, "prepare_toe_native_phi_surface_variation_and_source_route_packet"
    )
    assert scalar_conservation_active_workstream["status"] == "paused"
    assert (
        scalar_conservation_active_workstream["workstream_id"]
        == "prepare_toe_native_phi_surface_variation_and_source_route_packet"
    )
    assert (
        scalar_conservation_active_workstream["authorized_next_strict_target"]
        == "prepare_toe_native_phi_surface_variation_and_source_route_packet"
    )
    assert (
        scalar_conservation_active_workstream["authorized_target"]
        == "prepare_toe_native_phi_surface_variation_and_source_route_packet"
    )
    assert scalar_conservation_active_workstream["authorization_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "ToeNativePhiSurfaceVariationAndSourceRoutePacket.lean"
    )
    assert scalar_conservation_active_workstream["report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_PHI_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_"
        "20260618_v0.json"
    )
    assert (
        scalar_conservation_active_workstream["outcome_id"]
        == "TOE_NATIVE_MATTER_SECTOR_CALCULATION_ROUTE_SELECTION_SELECTS_"
        "PHI_SURFACE_VARIATION_AND_SOURCE_ROUTE_NO_DERIVATION_CLAIM"
    )
    assert (
        scalar_conservation_active_workstream["claim_level"]
        == "Level 3 ToE-native matter-sector calculation route selected; phi variation/source route packet preparation authorized"
    )
    assert (
        scalar_conservation_active_workstream["claim_ceiling"]
        == "phi route packet preparation only no phi route execution no toe-native matter derivation no standard model derivation no qft-gr closure no semiclassical coupling no canonical master-action promotion"
    )
    assert "raw symbolic variation/source route" in scalar_conservation_active_workstream[
        "non_claim_boundary"
    ]
    assert "signature, C_k, and native generation gaps" in scalar_conservation_active_workstream[
        "non_claim_boundary"
    ]
    assert (
        scalar_conservation_active_workstream["consumed_target"]
        == "select_toe_native_matter_sector_calculation_route"
    )
    assert (
        scalar_conservation_active_workstream["review_result"]
        == "TOE_NATIVE_MATTER_SECTOR_DEFINITION_RESULT_REVIEW_ACCEPTS_"
        "MASTER_ACTION_MATTER_SURFACE_INDEX_NO_DERIVATION_CLAIM"
    )
    assert (
        scalar_conservation_active_workstream["route_selection_result"]
        == "TOE_NATIVE_MATTER_SECTOR_CALCULATION_ROUTE_SELECTION_SELECTS_"
        "PHI_SURFACE_VARIATION_AND_SOURCE_ROUTE_NO_DERIVATION_CLAIM"
    )
    assert scalar_conservation_active_workstream["selected_surface_symbol"] == "phi"
    assert (
        scalar_conservation_active_workstream["selected_route_id"]
        == "toe_native_phi_surface_variation_and_source_route"
    )
    assert (
        scalar_conservation_active_workstream["selected_route_label"]
        == "candidate phi surface variation and source route"
    )
    assert (
        scalar_conservation_active_workstream["selected_route_status"]
        == "selected_for_packet_preparation"
    )
    assert (
        scalar_conservation_active_workstream["selected_route_target"]
        == "prepare_toe_native_phi_surface_variation_and_source_route_packet"
    )
    assert scalar_conservation_active_workstream["selected_route_packet_authorized"] == "yes"
    assert scalar_conservation_active_workstream["selected_route_execution_authorized"] == "no"
    assert (
        scalar_conservation_active_workstream["definition_result"]
        == "MASTER_ACTION_MATTER_SURFACES_INDEXED_AS_NATIVE_CANDIDATES_"
        "NO_DERIVATION_CLAIM"
    )
    assert scalar_conservation_active_workstream["candidate_surface_count"] == "5"
    assert (
        scalar_conservation_active_workstream["candidate_symbols"]
        == "psi,A,phi,rho,C_k"
    )
    assert (
        scalar_conservation_active_workstream[
            "master_action_working_form_noncanonical"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "master_action_matter_surfaces_indexed_as_native_candidates"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "native_candidate_surface_defined_nonpromotionally"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "toe_native_matter_sector_candidate_surface_defined"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "canonical_toe_native_matter_sector_defined"
        ]
        == "no"
    )
    assert (
        scalar_conservation_active_workstream[
            "post_review_route_selection_target"
        ]
        == "select_toe_native_matter_sector_calculation_route"
    )
    assert (
        scalar_conservation_active_workstream[
            "next_after_definition_review_suggested"
        ]
        == "select_toe_native_matter_sector_calculation_route"
    )
    assert scalar_conservation_active_workstream["route_selection_authorized"] == "yes"
    assert (
        scalar_conservation_active_workstream["selected_next_target"]
        == "review_toe_native_phi_surface_variation_and_source_route_result"
    )
    assert (
        scalar_conservation_active_workstream["selected_next_target_kind"]
        == "toe_native_phi_surface_variation_and_source_route_result_review"
    )
    assert scalar_conservation_active_workstream["recommended_first_route_hint"] == "phi"
    assert (
        scalar_conservation_active_workstream["recommended_first_route_status"]
        == "recorded_as_nonbinding_selector_input"
    )
    assert (
        scalar_conservation_active_workstream["recommended_first_route_target_hint"]
        == "prepare_toe_native_phi_surface_variation_and_source_route_packet"
    )
    assert (
        scalar_conservation_active_workstream[
            "next_after_route_selection_recommended"
        ]
        == "prepare_toe_native_phi_surface_variation_and_source_route_packet"
    )
    assert (
        scalar_conservation_active_workstream["direct_phi_route_execution_authorized"]
        == "no"
    )
    assert scalar_conservation_active_workstream["recommended_phi_route_binding"] == "no"
    assert (
        scalar_conservation_active_workstream["review_criteria_count"] == "10"
    )
    assert (
        scalar_conservation_active_workstream["review_criteria_accepted_count"]
        == "10"
    )
    assert scalar_conservation_active_workstream["route_option_count"] == "4"
    assert scalar_conservation_active_workstream["route_options_selected_count"] == "1"
    assert scalar_conservation_active_workstream["route_options_deferred_count"] == "3"
    assert scalar_conservation_active_workstream["selection_criteria_count"] == "10"
    assert (
        scalar_conservation_active_workstream["selection_criteria_accepted_count"]
        == "10"
    )
    assert (
        scalar_conservation_active_workstream["comparison_witness_use"]
        == "reference_only_not_derivation"
    )
    assert scalar_conservation_active_workstream["scalar_witness_reopened"] == "no"
    assert (
        scalar_conservation_active_workstream[
            "scalar_witness_used_as_toe_native_derivation"
        ]
        == "no"
    )
    assert scalar_conservation_active_workstream["phi_variation_route_prepared"] == "no"
    assert scalar_conservation_active_workstream["phi_variation_route_executed"] == "no"
    assert scalar_conservation_active_workstream["phi_variation_derived"] == "no"
    assert scalar_conservation_active_workstream["phi_stress_energy_derived"] == "no"
    assert (
        scalar_conservation_active_workstream[
            "toe_native_phi_source_route_constructed"
        ]
        == "no"
    )
    assert (
        scalar_conservation_active_workstream[
            "toe_native_phi_source_admissibility_claimed"
        ]
        == "no"
    )
    assert (
        scalar_conservation_active_workstream[
            "toe_native_phi_source_conservation_claimed"
        ]
        == "no"
    )
    assert (
        scalar_conservation_active_workstream[
            "matter_sector_candidates_listed"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "source_of_each_candidate_identified"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "imported_vs_native_candidate_status_marked"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "variation_route_specified_or_blocked"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "stress_energy_route_specified_or_blocked"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "quantum_operator_route_specified_or_blocked"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "seam_constraint_dependency_recorded"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "next_calculation_target_selected"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["psi_surface_status_decision"]
        == "imported_known_physics_term_indexed_as_provisional_toe_native_candidate_surface"
    )
    assert (
        scalar_conservation_active_workstream["a_surface_status_decision"]
        == "imported_known_physics_gauge_term_indexed_as_provisional_toe_native_candidate_surface"
    )
    assert (
        scalar_conservation_active_workstream["phi_surface_status_decision"]
        == "scalar_structure_term_indexed_as_provisional_toe_native_candidate_surface_with_imported_scalar_witness_boundary"
    )
    assert (
        scalar_conservation_active_workstream["rho_surface_status_decision"]
        == "speculative_statistical_state_surface_indexed_as_organizing_placeholder_and_candidate_dependency"
    )
    assert (
        scalar_conservation_active_workstream["ck_surface_status_decision"]
        == "seam_constraint_surface_indexed_as_required_organizing_dependency_not_matter_derivation"
    )
    assert (
        scalar_conservation_active_workstream["action_derivability_result"]
        == "ACTION_DERIVABILITY_CONSTRUCTED_FOR_PROVISIONAL_REAL_SCALAR_TEST_SECTOR_NO_TOE_NATIVE_MATTER_DERIVATION"
    )
    assert (
        scalar_conservation_active_workstream["selected_provisional_matter_sector_id"]
        == "provisional_real_scalar_field_test_sector_v0"
    )
    assert (
        scalar_conservation_active_workstream["selected_action_generated_source_subclass_id"]
        == "stress_energy_candidate_generated_by_provisional_real_scalar_lagrangian_v0"
    )
    assert (
        scalar_conservation_active_workstream["field_content"]
        == "real scalar field phi"
    )
    assert (
        scalar_conservation_active_workstream["lagrangian_density"]
        == "L_m(g, phi, nabla phi) = -1/2 g^{mu nu} nabla_mu phi nabla_nu phi - V(phi)"
    )
    assert (
        scalar_conservation_active_workstream["metric_variation_convention_stated"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["stress_energy_expression_derived"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["stress_energy_covariant_expression"]
        == "T_{mu nu} = partial_mu phi partial_nu phi - 1/2 g_{mu nu} g^{alpha beta} partial_alpha phi partial_beta phi - g_{mu nu} V(phi)"
    )
    assert (
        scalar_conservation_active_workstream["covariant_variation_form"]
        == "delta S_m[g, phi](k) = -1/2 integral_M T_{mu nu} k^{mu nu} dVol_g"
    )
    assert (
        scalar_conservation_active_workstream["weak_pairing_translation_stated"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["prior_contract_pairing_form"]
        == "<T, h> = integral_M T^{mu nu} h_{mu nu} dVol_g"
    )
    assert (
        scalar_conservation_active_workstream["action_derivability_constructed"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["weak_conservation_result"]
        == "WEAK_CONSERVATION_CONSTRUCTED_FOR_PROVISIONAL_SCALAR_SOURCE_ON_SHELL_NO_SOURCE_ADMISSIBILITY"
    )
    assert (
        scalar_conservation_active_workstream["weak_conservation_constructed"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["weak_conservation_claimed"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["weak_conservation_claimed_scope"]
        == "conditional on scalar equation of motion only"
    )
    assert scalar_conservation_active_workstream["on_shell_required"] == "yes"
    assert (
        scalar_conservation_active_workstream["scalar_equation_of_motion"]
        == "box_g phi - V'(phi) = 0"
    )
    assert (
        scalar_conservation_active_workstream["divergence_identity"]
        == "nabla_mu T^{mu nu} = (box_g phi - V'(phi)) nabla^nu phi"
    )
    assert (
        scalar_conservation_active_workstream["on_shell_conservation_statement"]
        == "If box_g phi - V'(phi) = 0, then nabla_mu T^{mu nu} = 0"
    )
    assert (
        scalar_conservation_active_workstream["bianchi_compatibility_result"]
        == "BIANCHI_COMPATIBILITY_CONSTRUCTED_FOR_PROVISIONAL_SCALAR_SOURCE_ON_SHELL_NO_QFT_GR_CLOSURE"
    )
    assert (
        scalar_conservation_active_workstream["bianchi_compatibility_constructed"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["Bianchi_compatibility_claimed"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["Bianchi_compatibility_claimed_scope"]
        == "conditional on scalar EOM, Levi-Civita connection, metric compatibility, constant coupling, and provisional scalar source only"
    )
    assert (
        scalar_conservation_active_workstream["contracted_bianchi_identity"]
        == "nabla_mu G^{mu nu} = 0"
    )
    assert (
        scalar_conservation_active_workstream["metric_compatibility_identity"]
        == "nabla_mu g^{mu nu} = 0"
    )
    assert (
        scalar_conservation_active_workstream[
            "einstein_source_equation_with_lambda_form"
        ]
        == "G^{mu nu} + Lambda g^{mu nu} = 8 pi G_N T^{mu nu}"
    )
    assert (
        scalar_conservation_active_workstream[
            "source_side_conservation_requirement"
        ]
        == "nabla_mu T^{mu nu} = 0"
    )
    assert (
        scalar_conservation_active_workstream["source_admissibility_review_authorized"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "provisional_scalar_source_admissibility_result"
        ]
        == "PROVISIONAL_SCALAR_SOURCE_PASSES_LOCAL_SOURCE_ADMISSIBILITY_REVIEW_ON_SHELL_NO_SEMICLASSICAL_OR_TOE_NATIVE_CLOSURE"
    )
    assert (
        scalar_conservation_active_workstream[
            "local_source_admissibility_review_completed"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["local_source_admissibility_review_passed"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "provisional_scalar_source_passes_local_source_admissibility_review"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "provisional_scalar_source_admissibility_constructed"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "semiclassical_coupling_gate_scope_review_authorized"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "semiclassical_coupling_gate_scope_review_completed"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["semiclassical_coupling_gate_result"]
        == "CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_RECORDED_SEMICLASSICAL_"
        "COUPLING_NOT_AUTHORIZED"
    )
    assert (
        scalar_conservation_active_workstream[
            "semiclassical_coupling_not_authorized_result"
        ]
        == "SEMICLASSICAL_COUPLING_NOT_AUTHORIZED_FOR_PROVISIONAL_CLASSICAL_"
        "SCALAR_SOURCE_REQUIRES_QUANTUM_EXPECTATION_RENORMALIZATION_AND_STATE_DOMAIN"
    )
    assert (
        scalar_conservation_active_workstream[
            "classical_einstein_scalar_coupling_route_recorded"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "classical_einstein_scalar_coupling_route_packet_authorized"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "classical_einstein_scalar_coupling_constructed"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "classical_einstein_scalar_coupling_route_packet_prepared"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "classical_einstein_scalar_coupling_route_constructed"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "classical_einstein_scalar_coupling_result"
        ]
        == "CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_CONSTRUCTED_FOR_"
        "PROVISIONAL_ON_SHELL_SCALAR_SOURCE_NO_QFT_GR_OR_TOE_NATIVE_CLOSURE"
    )
    assert (
        scalar_conservation_active_workstream[
            "classical_einstein_scalar_coupling_equation"
        ]
        == "G_{mu nu} + Lambda g_{mu nu} = 8 pi G_N T^{scalar}_{mu nu}"
    )
    assert (
        scalar_conservation_active_workstream["classical_einstein_scalar_equation_form"]
        == "G_{mu nu} + Lambda g_{mu nu} = 8 pi G_N T^{scalar}_{mu nu}"
    )
    assert (
        scalar_conservation_active_workstream["left_hand_side_divergence_identity"]
        == "nabla_mu(G^{mu nu} + Lambda g^{mu nu}) = 0"
    )
    assert (
        scalar_conservation_active_workstream["route_internal_compatibility_constructed"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "bounded_positive_classical_source_route_witness_candidate"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["closeout_result"]
        == "QFT_GR_PROVISIONAL_SCALAR_CLASSICAL_SOURCE_ROUTE_WITNESS_CLOSED_AS_"
        "POSITIVE_CLASSICAL_SANDBOX_NO_QFT_GR_OR_TOE_NATIVE_CLOSURE"
    )
    assert (
        scalar_conservation_active_workstream[
            "positive_local_classical_source_witness_closed"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["witness_closeout_completed"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["witness_closeout_scope"]
        == "positive local classical source witness for imported provisional real-scalar sandbox only"
    )
    assert (
        scalar_conservation_active_workstream["scalar_sandbox_branch_closed"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "default_scalar_sandbox_extension_authorized"
        ]
        == "no"
    )
    assert (
        scalar_conservation_active_workstream[
            "toe_native_matter_sector_definition_packet_authorized"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "imported_provisional_scalar_sector_only"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "provisional_classical_sandbox_route_only"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["next_after_result_review_suggested"]
        == "prepare_qft_gr_provisional_scalar_classical_source_route_witness_closeout"
    )
    assert (
        scalar_conservation_active_workstream["classical_route_result_review_completed"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["classical_route_result_review_accepted"]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "classical_einstein_scalar_coupling_route_reviewed"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["review_result"]
        == "TOE_NATIVE_MATTER_SECTOR_DEFINITION_RESULT_REVIEW_ACCEPTS_"
        "MASTER_ACTION_MATTER_SURFACE_INDEX_NO_DERIVATION_CLAIM"
    )
    assert (
        scalar_conservation_active_workstream[
            "positive_local_classical_source_witness_classification"
        ]
        == "positive local classical source witness"
    )
    assert (
        scalar_conservation_active_workstream[
            "positive_local_classical_source_witness_candidate"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream[
            "positive_local_classical_source_witness_closeout_authorized"
        ]
        == "yes"
    )
    assert (
        scalar_conservation_active_workstream["solution_existence_claimed"]
        == "no"
    )
    assert (
        scalar_conservation_active_workstream["solution_uniqueness_claimed"]
        == "no"
    )
    assert (
        scalar_conservation_active_workstream["global_wellposedness_claimed"]
        == "no"
    )
    assert (
        scalar_conservation_active_workstream["coupled_pde_solution_constructed"]
        == "no"
    )
    assert (
        scalar_conservation_active_workstream["coupled_einstein_scalar_system_solved"]
        == "no"
    )
    assert (
        scalar_conservation_active_workstream[
            "semiclassical_einstein_expectation_form"
        ]
        == "G_{mu nu} + Lambda g_{mu nu} = 8 pi G_N <T_hat_{mu nu}>_ren"
    )
    assert (
        scalar_conservation_active_workstream["proof_depth_label"]
        == "RECORD_ONLY_SELECTOR_VALIDATED"
    )
    assert scalar_conservation_active_workstream["record_validated"] == "yes"
    assert scalar_conservation_active_workstream["symbolic_calculation_recorded"] == "yes"
    assert (
        scalar_conservation_active_workstream[
            "formal_differential_geometry_theorem_backed"
        ]
        == "no"
    )
    assert (
        scalar_conservation_active_workstream[
            "aggregate_lean_validation_status_for_packet"
        ]
        == "NOT_RUN"
    )
    assert (
        scalar_conservation_active_workstream["auxiliary_hygiene_target_queued"]
        == "prepare_status_surface_stale_current_token_quarantine_for_public_summary_surfaces"
    )
    assert (
        scalar_conservation_active_workstream[
            "auxiliary_hygiene_target_supersedes_qft_gr_live_target"
        ]
        == "no"
    )
    assert (
        scalar_conservation_active_workstream["lean_validation_tier_policy_formalized"]
        == "yes"
    )
    for key in [
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "toe_native_matter_derivation_claimed",
        "arbitrary_distributional_source_action_derived_claimed",
        "arbitrary_distributional_source_admissibility_claimed",
        "arbitrary_distributional_source_conservation_claimed",
        "arbitrary_distributional_source_promoted",
        "quantum_stress_energy_expectation_constructed",
        "state_expectation_functional_link_claimed",
        "renormalization_result_claimed",
        "renormalized_stress_energy_constructed",
        "renormalized_expectation_value_constructed",
        "renormalization_scheme_supplied",
        "quantum_state_supplied",
        "stress_energy_operator_constructed",
        "state_domain_supplied",
        "anomaly_or_regularization_controls_supplied",
        "conservation_claimed",
        "off_shell_conservation_claimed",
        "arbitrary_phi_conserved_claimed",
        "unconditional_conservation_claimed",
        "Bianchi_compatibility_completed",
        "semiclassical_coupling_authorized",
        "semiclassical_quantum_expectation_route_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "quantum_state_source_constructed",
        "quantum_stress_energy_operator_constructed",
        "renormalized_stress_energy_expectation_constructed",
        "generic_source_admissibility_claimed",
        "solution_existence_claimed",
        "solution_uniqueness_claimed",
        "global_wellposedness_claimed",
        "coupled_pde_solution_constructed",
        "coupled_einstein_scalar_system_solved",
        "regularity_analysis_completed",
        "boundary_initial_data_supplied",
        "toe_native_matter_source_route_defined",
        "toe_native_matter_sector_defined",
        "toe_matter_model_derived",
        "standard_model_derivation_claimed",
        "direct_phi_route_execution_authorized",
        "selected_route_execution_authorized",
        "scalar_witness_reopened",
        "scalar_witness_used_as_toe_native_derivation",
        "phi_variation_route_prepared",
        "phi_variation_route_executed",
        "phi_variation_derived",
        "phi_stress_energy_derived",
        "toe_native_phi_source_route_constructed",
        "toe_native_phi_source_admissibility_claimed",
        "toe_native_phi_source_conservation_claimed",
        "recommended_phi_route_binding",
        "source_map_closed",
        "qft_gr_solved",
        "qft_gr_closure_claimed",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_authorized",
        "semiclassical_source_established",
        "toe_matter_sector_derived",
        "canonical_master_action_promoted",
        "default_scalar_sandbox_extension_authorized",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "public_submission_authorized",
        "public_release_completion_authorized",
        "master_action_promoted",
        "master_action_promotion_authorized",
    ]:
        assert scalar_conservation_active_workstream[key] == "no", key

    post_retest_refinement_conservation_retest_refinement_refinement_packet_workstream = _workstream(
        payload,
        POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_PACKET_TARGET,
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_packet_workstream[
            "status"
        ]
        == "paused"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_packet_workstream[
            "retest_packet_prepared"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_packet_workstream[
            "packet_preparation_only"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_packet_workstream[
            "selected_next_target"
        ]
        == POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_PACKET_RESULT_REVIEW_TARGET
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_packet_workstream[
            "retest_condition_id"
        ]
        == "weak_distributional_covariant_conservation_for_post_retest_refinement_conservation_retest_refinement_refined_toy_candidate"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_packet_workstream[
            "weak_pairing_domain_id"
        ]
        == "toy_weak_pairing_domain_v4_candidate"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_packet_workstream[
            "conservation_retest_executed"
        ]
        == "no"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_packet_workstream[
            "source_admissibility_claimed"
        ]
        == "no"
    )

    post_retest_refinement_conservation_retest_refinement_refinement_attempt_workstream = _workstream(
        payload,
        POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_ATTEMPT_TARGET,
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_attempt_workstream[
            "status"
        ]
        == "paused"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_attempt_workstream[
            "attempt_executed"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_attempt_workstream[
            "bounded_refinement_attempt_executed"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_attempt_workstream[
            "refinement_attempt_result_review_pending"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_attempt_workstream[
            "selected_next_target"
        ]
        == POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_attempt_workstream[
            "weak_pairing_domain_id"
        ]
        == "toy_weak_pairing_domain_v4_candidate"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_attempt_workstream[
            "obstruction_class"
        ]
        == "repeated_weak_divergence_undecided_under_candidate_pairing_domain_v3"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_refinement_attempt_workstream[
            "countermodel_packet_authorized"
        ]
        == "no"
    )
    post_retest_refinement_conservation_retest_refinement_packet_workstream = _workstream(
        payload,
        POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_TARGET,
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_packet_workstream[
            "status"
        ]
        == "paused"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_packet_workstream[
            "result_review_accepted"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_packet_workstream[
            "selected_next_target"
        ]
        == POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_ATTEMPT_TARGET
    )
    post_retest_refinement_conservation_retest_refinement_packet_preparation_workstream = (
        _workstream(
            payload,
            POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_PACKET_TARGET,
        )
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_packet_preparation_workstream[
            "status"
        ]
        == "paused"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_packet_preparation_workstream[
            "packet_prepared"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_packet_preparation_workstream[
            "selected_next_target"
        ]
        == POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_TARGET
    )

    post_retest_refinement_conservation_retest_refinement_attempt_workstream = _workstream(
        payload,
        POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RETEST_ATTEMPT_TARGET,
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_attempt_workstream[
            "status"
        ]
        == "paused"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_attempt_workstream[
            "selected_next_target"
        ]
        == POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RETEST_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_attempt_workstream[
            "bounded_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_executed"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_attempt_workstream[
            "conservation_retest_executed"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_attempt_workstream[
            "retest_result"
        ]
        == "inconclusive"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_attempt_workstream[
            "source_admissibility_claimed"
        ]
        == "no"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_attempt_workstream[
            "conservation_witness_constructed"
        ]
        == "no"
    )
    assert (
        post_retest_refinement_conservation_retest_refinement_attempt_workstream[
            "qft_gr_closure_claimed"
        ]
        == "no"
    )

    post_retest_retest_attempt_workstream = _workstream(
        payload, POST_RETEST_REFINEMENT_CONSERVATION_RETEST_ATTEMPT_TARGET
    )
    assert post_retest_retest_attempt_workstream["status"] == "paused"
    assert (
        post_retest_retest_attempt_workstream["selected_next_target"]
        == POST_RETEST_REFINEMENT_CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert (
        post_retest_retest_attempt_workstream[
            "bounded_conservation_retest_attempt_after_post_retest_refinement_executed"
        ]
        == "yes"
    )
    assert (
        post_retest_retest_attempt_workstream["conservation_retest_executed"]
        == "yes"
    )
    assert post_retest_retest_attempt_workstream["retest_result"] == "inconclusive"
    assert post_retest_retest_attempt_workstream["retest_inconclusive"] == "yes"
    assert (
        post_retest_retest_attempt_workstream["conservation_retest_passed"]
        == "no"
    )
    assert (
        post_retest_retest_attempt_workstream["conservation_retest_failed"]
        == "no"
    )
    assert (
        post_retest_retest_attempt_workstream[
            "source_admissibility_claimed"
        ]
        == "no"
    )
    assert (
        post_retest_retest_attempt_workstream[
            "conservation_witness_constructed"
        ]
        == "no"
    )
    assert (
        post_retest_retest_attempt_workstream[
            "qft_gr_closure_claimed"
        ]
        == "no"
    )

    post_retest_retest_packet_result_review_workstream = _workstream(
        payload, POST_RETEST_REFINEMENT_CONSERVATION_RETEST_PACKET_RESULT_REVIEW_TARGET
    )
    assert post_retest_retest_packet_result_review_workstream["status"] == "paused"
    assert (
        post_retest_retest_packet_result_review_workstream["selected_next_target"]
        == POST_RETEST_REFINEMENT_CONSERVATION_RETEST_ATTEMPT_TARGET
    )
    assert (
        post_retest_retest_packet_result_review_workstream["result_review_accepted"]
        == "yes"
    )
    assert (
        post_retest_retest_packet_result_review_workstream[
            "retest_packet_result_review_accepted"
        ]
        == "yes"
    )
    assert (
        post_retest_retest_packet_result_review_workstream[
            "bounded_conservation_retest_attempt_authorized"
        ]
        == "yes"
    )
    assert (
        post_retest_retest_packet_result_review_workstream[
            "bounded_conservation_retest_attempt_executed_by_review"
        ]
        == "no"
    )
    assert (
        post_retest_retest_packet_result_review_workstream[
            "conservation_retest_executed"
        ]
        == "no"
    )
    assert (
        post_retest_retest_packet_result_review_workstream[
            "source_admissibility_claimed"
        ]
        == "no"
    )
    assert (
        post_retest_retest_packet_result_review_workstream[
            "conservation_witness_constructed"
        ]
        == "no"
    )
    assert (
        post_retest_retest_packet_result_review_workstream[
            "qft_gr_closure_claimed"
        ]
        == "no"
    )

    post_retest_refinement_attempt_workstream = _workstream(
        payload, REFINEMENT_ATTEMPT_AFTER_RETEST_TARGET
    )
    assert post_retest_refinement_attempt_workstream["status"] == "paused"
    assert (
        post_retest_refinement_attempt_workstream["selected_next_target"]
        == POST_RETEST_REFINEMENT_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert (
        post_retest_refinement_attempt_workstream["attempt_executed"]
        == "yes"
    )
    assert (
        post_retest_refinement_attempt_workstream[
            "bounded_refinement_attempt_executed"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_attempt_workstream[
            "post_retest_refinement_attempt_executed"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_attempt_workstream[
            "weak_pairing_domain_adjusted"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_attempt_workstream[
            "regularity_assumptions_refined"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_attempt_workstream[
            "test_function_class_identified"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_attempt_workstream["refinement_objective"]
        == "refine_weak_pairing_domain_and_regular_context_after_inconclusive_retest_without_source_admissibility"
    )
    assert (
        post_retest_refinement_attempt_workstream[
            "conservation_retest_retried"
        ]
        == "no"
    )
    assert (
        post_retest_refinement_attempt_workstream[
            "source_admissibility_claimed"
        ]
        == "no"
    )
    assert (
        post_retest_refinement_attempt_workstream[
            "conservation_witness_constructed"
        ]
        == "no"
    )
    assert (
        post_retest_refinement_attempt_workstream[
            "qft_gr_closure_claimed"
        ]
        == "no"
    )

    post_retest_refinement_attempt_result_review_workstream = _workstream(
        payload, POST_RETEST_REFINEMENT_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert post_retest_refinement_attempt_result_review_workstream["status"] == "paused"
    assert (
        post_retest_refinement_attempt_result_review_workstream[
            "selected_next_target"
        ]
        == POST_RETEST_REFINEMENT_CONSERVATION_RETEST_PACKET_TARGET
    )
    assert (
        post_retest_refinement_attempt_result_review_workstream[
            "result_review_accepted"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_attempt_result_review_workstream[
            "refined_candidate_accepted"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_attempt_result_review_workstream[
            "bounded_conservation_retest_packet_authorized"
        ]
        == "yes"
    )
    assert (
        post_retest_refinement_attempt_result_review_workstream[
            "conservation_retest_packet_prepared_by_review"
        ]
        == "no"
    )
    assert (
        post_retest_refinement_attempt_result_review_workstream[
            "conservation_retest_executed_by_review"
        ]
        == "no"
    )
    assert (
        post_retest_refinement_attempt_result_review_workstream[
            "source_admissibility_claimed"
        ]
        == "no"
    )
    assert (
        post_retest_refinement_attempt_result_review_workstream[
            "conservation_witness_constructed"
        ]
        == "no"
    )
    assert (
        post_retest_refinement_attempt_result_review_workstream[
            "qft_gr_closure_claimed"
        ]
        == "no"
    )

    post_retest_conservation_retest_packet_workstream = _workstream(
        payload, POST_RETEST_REFINEMENT_CONSERVATION_RETEST_PACKET_TARGET
    )
    assert post_retest_conservation_retest_packet_workstream["status"] == "paused"
    assert (
        post_retest_conservation_retest_packet_workstream["selected_next_target"]
        == POST_RETEST_REFINEMENT_CONSERVATION_RETEST_PACKET_RESULT_REVIEW_TARGET
    )
    assert (
        post_retest_conservation_retest_packet_workstream["retest_packet_prepared"]
        == "yes"
    )
    assert (
        post_retest_conservation_retest_packet_workstream[
            "packet_preparation_only"
        ]
        == "yes"
    )
    assert (
        post_retest_conservation_retest_packet_workstream["retest_condition_id"]
        == "weak_distributional_covariant_conservation_for_post_retest_refined_toy_candidate"
    )
    assert (
        post_retest_conservation_retest_packet_workstream[
            "weak_pairing_domain_id"
        ]
        == "toy_weak_pairing_domain_v2_candidate"
    )
    assert (
        post_retest_conservation_retest_packet_workstream[
            "regularity_structure_id"
        ]
        == "toy_regular_context_v2_candidate"
    )
    assert (
        post_retest_conservation_retest_packet_workstream[
            "conservation_retest_executed"
        ]
        == "no"
    )
    assert (
        post_retest_conservation_retest_packet_workstream[
            "source_admissibility_claimed"
        ]
        == "no"
    )
    assert (
        post_retest_conservation_retest_packet_workstream[
            "conservation_witness_constructed"
        ]
        == "no"
    )
    assert (
        post_retest_conservation_retest_packet_workstream[
            "qft_gr_closure_claimed"
        ]
        == "no"
    )

    conservation_retest_attempt_result_review_workstream = _workstream(
        payload, CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert conservation_retest_attempt_result_review_workstream["status"] == "paused"
    assert (
        conservation_retest_attempt_result_review_workstream["selected_next_target"]
        == REFINEMENT_AFTER_RETEST_PACKET_TARGET
    )
    assert (
        conservation_retest_attempt_result_review_workstream[
            "accepted_inconclusive_result"
        ]
        == "yes"
    )
    assert (
        conservation_retest_attempt_result_review_workstream[
            "model_refinement_packet_authorized"
        ]
        == "yes"
    )
    assert (
        conservation_retest_attempt_result_review_workstream[
            "source_admissibility_claimed"
        ]
        == "no"
    )
    assert (
        conservation_retest_attempt_result_review_workstream[
            "conservation_witness_constructed"
        ]
        == "no"
    )
    assert (
        conservation_retest_attempt_result_review_workstream[
            "qft_gr_closure_claimed"
        ]
        == "no"
    )

    conservation_retest_attempt_workstream = _workstream(
        payload, CONSERVATION_RETEST_ATTEMPT_TARGET
    )
    assert conservation_retest_attempt_workstream["status"] == "paused"
    assert (
        conservation_retest_attempt_workstream["selected_next_target"]
        == CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert (
        conservation_retest_attempt_workstream[
            "bounded_conservation_retest_attempt_executed"
        ]
        == "yes"
    )
    assert (
        conservation_retest_attempt_workstream["conservation_retest_executed"]
        == "yes"
    )
    assert conservation_retest_attempt_workstream["retest_result"] == "inconclusive"
    assert conservation_retest_attempt_workstream["retest_inconclusive"] == "yes"
    assert (
        conservation_retest_attempt_workstream["source_admissibility_claimed"]
        == "no"
    )
    assert (
        conservation_retest_attempt_workstream["conservation_witness_constructed"]
        == "no"
    )
    assert conservation_retest_attempt_workstream["qft_gr_closure_claimed"] == "no"

    conservation_retest_packet_result_review_workstream = _workstream(
        payload, CONSERVATION_RETEST_PACKET_RESULT_REVIEW_TARGET
    )
    assert conservation_retest_packet_result_review_workstream["status"] == "paused"
    assert (
        conservation_retest_packet_result_review_workstream["selected_next_target"]
        == CONSERVATION_RETEST_ATTEMPT_TARGET
    )
    assert (
        conservation_retest_packet_result_review_workstream[
            "retest_packet_result_review_accepted"
        ]
        == "yes"
    )
    assert (
        conservation_retest_packet_result_review_workstream[
            "bounded_conservation_retest_attempt_authorized"
        ]
        == "yes"
    )
    assert (
        conservation_retest_packet_result_review_workstream[
            "bounded_conservation_retest_attempt_executed_by_review"
        ]
        == "no"
    )
    assert (
        conservation_retest_packet_result_review_workstream["retest_condition_id"]
        == "weak_distributional_covariant_conservation_for_refined_toy_candidate"
    )
    assert (
        conservation_retest_packet_result_review_workstream["weak_pairing_domain_id"]
        == "toy_weak_pairing_domain_v1"
    )
    assert (
        conservation_retest_packet_result_review_workstream["regularity_structure_id"]
        == "toy_regular_context_v1"
    )
    assert (
        conservation_retest_packet_result_review_workstream[
            "pass_fail_inconclusive_defined"
        ]
        == "yes"
    )
    assert (
        conservation_retest_packet_result_review_workstream[
            "pass_not_source_admissibility_or_qft_gr_closure_recorded"
        ]
        == "yes"
    )
    assert (
        conservation_retest_packet_result_review_workstream[
            "conservation_retest_executed"
        ]
        == "no"
    )
    assert (
        conservation_retest_packet_result_review_workstream[
            "source_admissibility_claimed"
        ]
        == "no"
    )
    assert (
        conservation_retest_packet_result_review_workstream[
            "conservation_witness_constructed"
        ]
        == "no"
    )
    assert (
        conservation_retest_packet_result_review_workstream[
            "qft_gr_closure_claimed"
        ]
        == "no"
    )

    conservation_retest_packet_workstream = _workstream(
        payload, CONSERVATION_RETEST_PACKET_TARGET
    )
    assert conservation_retest_packet_workstream["status"] == "paused"
    assert (
        conservation_retest_packet_workstream["selected_next_target"]
        == CONSERVATION_RETEST_PACKET_RESULT_REVIEW_TARGET
    )
    assert conservation_retest_packet_workstream["retest_packet_prepared"] == "yes"
    assert conservation_retest_packet_workstream["packet_preparation_only"] == "yes"

    refinement_attempt_result_review_workstream = _workstream(
        payload, REFINEMENT_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert refinement_attempt_result_review_workstream["status"] == "paused"
    assert (
        refinement_attempt_result_review_workstream["selected_next_target"]
        == CONSERVATION_RETEST_PACKET_TARGET
    )
    assert (
        refinement_attempt_result_review_workstream["result_review_accepted"]
        == "yes"
    )
    assert (
        refinement_attempt_result_review_workstream["qft_gr_closure_claimed"]
        == "no"
    )

    packet_result_review_workstream = _workstream(
        payload, CONSERVATION_TEST_PACKET_RESULT_REVIEW_TARGET
    )
    assert packet_result_review_workstream["status"] == "paused"
    assert (
        packet_result_review_workstream["selected_next_target"]
        == CONSUMED_TARGET
    )
    assert packet_result_review_workstream["packet_result_review_accepted"] == "yes"
    assert (
        packet_result_review_workstream[
            "bounded_conservation_test_attempt_authorized"
        ]
        == "yes"
    )
    assert (
        packet_result_review_workstream[
            "bounded_conservation_test_attempt_executed_by_review"
        ]
        == "no"
    )
    assert packet_result_review_workstream["conservation_test_executed"] == "no"
    assert packet_result_review_workstream["source_admissibility_claimed"] == "no"
    assert packet_result_review_workstream["conservation_witness_constructed"] == "no"
    assert packet_result_review_workstream["qft_gr_closure_claimed"] == "no"

    conservation_packet_workstream = _workstream(payload, CONSERVATION_TEST_PACKET_TARGET)
    assert conservation_packet_workstream["status"] == "paused"
    assert (
        conservation_packet_workstream["selected_next_target"]
        == CONSERVATION_TEST_PACKET_RESULT_REVIEW_TARGET
    )
    assert conservation_packet_workstream["packet_prepared"] == "yes"
    assert conservation_packet_workstream["packet_preparation_only"] == "yes"
    assert (
        conservation_packet_workstream["pass_fail_inconclusive_criteria_recorded"]
        == "yes"
    )
    assert conservation_packet_workstream["conservation_test_executed"] == "no"
    assert conservation_packet_workstream["source_admissibility_claimed"] == "no"
    assert conservation_packet_workstream["conservation_witness_constructed"] == "no"
    assert conservation_packet_workstream["qft_gr_closure_claimed"] == "no"

    candidate_analysis_result_review_workstream = _workstream(
        payload, "review_qft_gr_minimal_working_model_candidate_analysis_result"
    )
    assert candidate_analysis_result_review_workstream["status"] == "paused"
    assert (
        candidate_analysis_result_review_workstream["selected_next_target"]
        == CONSERVATION_TEST_PACKET_TARGET
    )
    assert (
        candidate_analysis_result_review_workstream["result_review_accepted"]
        == "yes"
    )
    assert (
        candidate_analysis_result_review_workstream[
            "bounded_conservation_test_packet_authorized"
        ]
        == "yes"
    )
    assert (
        candidate_analysis_result_review_workstream[
            "conservation_test_packet_prepared_by_review"
        ]
        == "no"
    )
    assert (
        candidate_analysis_result_review_workstream["source_admissibility_claimed"]
        == "no"
    )
    assert (
        candidate_analysis_result_review_workstream[
            "conservation_witness_constructed"
        ]
        == "no"
    )
    assert (
        candidate_analysis_result_review_workstream["qft_gr_closure_claimed"]
        == "no"
    )

    candidate_analysis_workstream = _workstream(
        payload, "analyze_qft_gr_minimal_working_model_candidate_only"
    )
    assert candidate_analysis_workstream["status"] == "paused"
    assert candidate_analysis_workstream["selected_next_target"] == (
        "review_qft_gr_minimal_working_model_candidate_analysis_result"
    )
    assert candidate_analysis_workstream["analysis_completed"] == "yes"
    assert candidate_analysis_workstream["candidate_analysis_only"] == "yes"
    assert (
        candidate_analysis_workstream["toy_source_candidate_status"]
        == "candidate_only_not_source_admissibility"
    )
    assert (
        candidate_analysis_workstream["domain_status"]
        == "supplied_imported_domain_conditions_only"
    )
    assert (
        candidate_analysis_workstream["regularity_status"]
        == "imported_regularities_recorded_not_reproved"
    )
    assert (
        candidate_analysis_workstream["pairing_status"]
        == "distributional_pairing_domain_imported_not_validated_for_source"
    )
    assert (
        candidate_analysis_workstream["weak_conservation_status"]
        == "test_target_recorded_not_proved"
    )
    assert candidate_analysis_workstream["source_admissibility_claimed"] == "no"
    assert candidate_analysis_workstream["conservation_witness_constructed"] == "no"
    assert candidate_analysis_workstream["qft_gr_closure_claimed"] == "no"

    construction_attempt_workstream = _workstream(
        payload, "execute_qft_gr_minimal_working_model_construction_attempt"
    )
    assert construction_attempt_workstream["status"] == "paused"
    assert construction_attempt_workstream["selected_next_target"] == (
        "review_qft_gr_minimal_working_model_construction_attempt_result"
    )
    assert (
        construction_attempt_workstream["bounded_model_construction_attempt_executed"]
        == "yes"
    )
    assert (
        construction_attempt_workstream["bounded_minimal_model_attempt_constructed"]
        == "yes"
    )
    assert construction_attempt_workstream["source_admissibility_claimed"] == "no"
    assert construction_attempt_workstream["conservation_witness_constructed"] == "no"
    assert construction_attempt_workstream["qft_gr_closure_claimed"] == "no"

    construction_attempt_result_review_workstream = _workstream(
        payload, "review_qft_gr_minimal_working_model_construction_attempt_result"
    )
    assert construction_attempt_result_review_workstream["status"] == "paused"
    assert (
        construction_attempt_result_review_workstream["selected_next_target"]
        == "analyze_qft_gr_minimal_working_model_candidate_only"
    )
    assert (
        construction_attempt_result_review_workstream["result_review_accepted"]
        == "yes"
    )
    assert (
        construction_attempt_result_review_workstream[
            "model_analysis_only_authorized"
        ]
        == "yes"
    )
    assert (
        construction_attempt_result_review_workstream[
            "model_analysis_executed_by_review"
        ]
        == "no"
    )
    assert (
        construction_attempt_result_review_workstream["source_admissibility_claimed"]
        == "no"
    )
    assert (
        construction_attempt_result_review_workstream[
            "conservation_witness_constructed"
        ]
        == "no"
    )
    assert (
        construction_attempt_result_review_workstream["qft_gr_closure_claimed"]
        == "no"
    )

    post_maturation_selector_workstream = _workstream(
        payload, "select_next_post_toe_expert_translation_bounded_target"
    )
    assert post_maturation_selector_workstream["status"] == "paused"
    assert post_maturation_selector_workstream["selected_next_target"] == (
        "prepare_qft_gr_minimal_working_model_demonstration_packet"
    )
    assert (
        post_maturation_selector_workstream["outcome_category"]
        == "post_translation_next_target_selected"
    )

    minimal_model_packet_workstream = _workstream(
        payload, "prepare_qft_gr_minimal_working_model_demonstration_packet"
    )
    assert minimal_model_packet_workstream["status"] == "paused"
    assert minimal_model_packet_workstream["selected_next_target"] == (
        "review_qft_gr_minimal_working_model_demonstration_packet_result"
    )
    assert minimal_model_packet_workstream["model_execution_authorized"] == "no"

    minimal_model_packet_review_workstream = _workstream(
        payload, "review_qft_gr_minimal_working_model_demonstration_packet_result"
    )
    assert minimal_model_packet_review_workstream["status"] == "paused"
    assert minimal_model_packet_review_workstream["selected_next_target"] == (
        "execute_qft_gr_minimal_working_model_construction_attempt"
    )
    assert (
        minimal_model_packet_review_workstream["packet_result_review_accepted"]
        == "yes"
    )
    assert (
        minimal_model_packet_review_workstream[
            "bounded_model_construction_attempt_authorized"
        ]
        == "yes"
    )

    current_active_workstream = _workstream(payload, MR_ROW_SELECTION_TARGET)
    assert current_active_workstream["status"] == "retained"
    assert current_active_workstream["workstream_id"] == MR_ROW_SELECTION_TARGET
    assert current_active_workstream["authorized_next_strict_target"] == (
        MR_ROW_SELECTION_TARGET
    )
    assert current_active_workstream["authorized_target"] == MR_ROW_SELECTION_TARGET
    assert (
        current_active_workstream["consumed_target"]
        == MR_ROW_SELECTION_CONSUMED_TARGET
    )
    assert (
        current_active_workstream["latest_surface"]
        == "qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result_review_v0"
    )
    assert current_active_workstream["latest_surface_evidence"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_SURFACE
    )
    assert current_active_workstream["latest_surface_report"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_REPORT
    )
    assert current_active_workstream["latest_surface_token"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_TOKEN
    )
    assert current_active_workstream["latest_surface_tool"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_TOOL
    )
    assert current_active_workstream["authorization_evidence"] == str(
        MR_ROW_SELECTION_EVIDENCE_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert current_active_workstream["construction_packet_surface"] == (
        "formal/toe_formal/ToeFormal/Release/"
        "V01RetainedTranche004SourceMapWitnessChainConstructionPacketFromResearchCandidate.lean"
    )
    assert current_active_workstream["construction_packet_report"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_20260523_v0.json"
    )
    assert current_active_workstream["result_surface"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_SURFACE
    )
    assert current_active_workstream["result_report"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_REPORT
    )
    assert current_active_workstream["result_token"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_TOKEN
    )
    assert current_active_workstream["result_tool"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_TOOL
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
        DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_SURFACE
    )
    assert current_active_workstream["consumed_result_review_report"] == (
        DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_REPORT
    )
    assert current_active_workstream["consumed_result_review_id"] == (
        DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_ID
    )
    assert current_active_workstream["consumed_result_review_tool"] == (
        DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOOL
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
        DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOKEN
    )
    assert current_active_workstream["output_token"] == (
        "QFT_GR_DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_"
        "PACKET_RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_"
        "MR_ASSUMP_003_ATTEMPT_ONLY"
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
        "qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_"
        "attempt_result_review_after_execution"
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
        WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_PENDING_CLASSIFICATION
    )
    assert current_active_workstream["result_review_classification"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_REVIEW_CLASSIFICATION
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
        STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_CLASSIFICATION
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
        == "no"
    )
    assert current_active_workstream["track2_remains_deferred"] == (
        "pending_mr_assump_003_distributional_pairing_regular_domain_assumption_reduction_attempt_result_review"
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
    assert current_active_workstream["track2_selected_after_result_review"] == (
        "distributional_pairing_regular_domain_assumption_reduction_attempt"
    )
    assert current_active_workstream["track2_selection_kind"] == (
        "qft_gr_distributional_pairing_regular_domain_assumption_reduction_attempt_execution"
    )
    assert current_active_workstream["track2_science_lane_execution_started"] == (
        "yes_operator_domain_closeout_result_review_accepted"
    )
    assert current_active_workstream["track2_started"] == (
        "state_expectation_compatibility_assumption_reduction_attempt_executed"
    )
    assert current_active_workstream["track2_selected_after_this_execution"] == (
        "state_expectation_compatibility_assumption_reduction_attempt_executed"
    )
    assert current_active_workstream["track2_selected_after_this_review"] == (
        "state_domain_assumption_reduction_closeout_packet_preparation"
    )
    assert current_active_workstream["next_action_scope"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_REVIEW_SCOPE
    )
    assert current_active_workstream["all_dependency_tranches_nonblocking"] == "yes"
    assert current_active_workstream["closeout_criteria_count"] == "4"
    assert current_active_workstream["documented_dependency_nonblocking_tranche_count"] == "6"
    assert current_active_workstream["selected_next_target"] == MR_ROW_SELECTION_TARGET
    assert (
        current_active_workstream["selected_next_target_kind"]
        == "qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result_review"
    )
    assert current_active_workstream["selected_next_action_scope"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_REVIEW_SCOPE
    )
    assert current_active_workstream["selected_next_authorization_token"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_TOKEN
    )
    assert current_active_workstream["result_review_accepted"] == "yes"
    assert current_active_workstream["result_review_completed"] == "yes"
    assert current_active_workstream["result_review_pending"] == "no"
    assert current_active_workstream["result_review_id"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_REVIEW_ID
    )
    assert current_active_workstream["review_decision"] == "accepted"
    assert current_active_workstream["result_review_target"] == MR_ROW_SELECTION_TARGET
    assert current_active_workstream["witness_attempt_executed"] == "yes"
    assert current_active_workstream["result_classification"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_CLASSIFICATION
    )
    assert current_active_workstream["result_review_classification"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_REVIEW_CLASSIFICATION
    )
    assert current_active_workstream["result_classification_count"] == "1"
    assert current_active_workstream["constructed_witness_result"] == "no"
    assert current_active_workstream["obstruction_identified_result"] == "no"
    assert current_active_workstream["inconclusive_result"] == "no"
    assert current_active_workstream["attempt_result_reviewed"] == "yes"
    assert current_active_workstream["attempt_result_review_accepted"] == "yes"
    assert current_active_workstream["attempt_result_review_completed"] == "yes"
    assert current_active_workstream["attempt_result_review_pending"] == "no"
    assert current_active_workstream["accepted_mathematical_regularity_assumption_row"] == (
        "MR-ASSUMP-003-distributional_pairing_regular_domain"
    )
    assert current_active_workstream["next_mathematical_regularity_assumption_row"] == (
        "MR-ASSUMP-004-limit_interchange_regularization_boundary"
    )
    assert current_active_workstream["next_mathematical_regularity_assumption_row_object"] == (
        "limit_interchange_regularization_boundary_for_renormalized_expectation_"
        "and_covariant_derivative"
    )
    assert current_active_workstream["selected_mathematical_regularity_assumption_row"] == (
        "MR-ASSUMP-004-limit_interchange_regularization_boundary"
    )
    assert current_active_workstream["selected_row_is_repo_authoritative_next_row"] == "yes"
    assert (
        current_active_workstream[
            "weak_strong_conservation_comparison_scope_assumption_reduction_packet_target"
        ]
        == "prepare_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet"
    )
    assert (
        current_active_workstream[
            "weak_strong_conservation_comparison_scope_assumption_reduction_packet_authorized"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "weak_strong_conservation_comparison_scope_assumption_reduction_packet_prepared"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "weak_strong_conservation_comparison_scope_assumption_reduction_packet_result_review_pending"
        ]
        == "no"
    )
    assert (
        current_active_workstream[
            "weak_strong_conservation_comparison_scope_assumption_reduction_packet_result_review_target"
        ]
        == WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    )
    assert (
        current_active_workstream[
            "weak_strong_conservation_comparison_scope_assumption_reduction_packet_report"
        ]
        == WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_REPORT
    )
    assert (
        current_active_workstream[
            "weak_strong_conservation_comparison_scope_assumption_reduction_packet_token"
        ]
        == WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_TOKEN
    )
    assert (
        current_active_workstream[
            "weak_strong_conservation_comparison_scope_assumption_reduction_packet_tool"
        ]
        == WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_TOOL
    )
    assert (
        current_active_workstream[
            "weak_strong_conservation_comparison_scope_assumption_reduction_packet_selected_row"
        ]
        == WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_SELECTED_ROW
    )
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
    assert (
        current_active_workstream["next_bounded_action"]
        == OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TARGET
    )

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
    assert current_active_workstream["proof_object_obstruction_accepted"] == "yes"
    assert current_active_workstream["inconclusive_result"] == "no"
    assert current_active_workstream["conservation_witness_upgraded_by_execution"] == "no"
    assert current_active_workstream["proof_object_attempt_result_reviewed"] == "yes"
    assert current_active_workstream["proof_object_obstruction_accepted"] == "yes"
    assert current_active_workstream["proof_object_obstruction_class"] == (
        "qft_gr_covariant_conservation_proof_object_obstruction_identified_requires_refinement"
    )
    assert current_active_workstream["qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result_review_classification"] == (
        "qft_gr_covariant_conservation_proof_object_obstruction_refinement_result_review_"
        "accepts_insufficient_assumptions_blocker_and_authorizes_assumption_reduction_"
        "packet_preparation_only"
    )
    assert current_active_workstream["qft_gr_covariant_conservation_assumption_reduction_packet_classification"] == (
        "qft_gr_covariant_conservation_assumption_reduction_packet_prepared_"
        "insufficient_assumptions_classified_no_conservation_witness_or_seam_closure"
    )
    assert current_active_workstream["qft_gr_covariant_conservation_assumption_reduction_packet_result_review_classification"] == (
        "qft_gr_covariant_conservation_assumption_reduction_packet_result_review_accepts_"
        "assumption_family_classification_and_authorizes_primary_assumption_reduction_"
        "target_selection_only"
    )
    assert current_active_workstream["assumption_family_classification_accepted"] == "yes"
    assert current_active_workstream["primary_assumption_reduction_family"] == (
        "mathematical_regularity_assumptions"
    )
    assert current_active_workstream["primary_assumption_reduction_target"] == (
        WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    )
    assert current_active_workstream["assumptions_reduced_or_discharged_by_review"] == "no"
    assert current_active_workstream["assumption_reduction_analysis_prepared"] == "yes"
    assert current_active_workstream["assumption_class_count"] == "6"
    assert current_active_workstream["reduces_or_discharges_assumptions_by_preparation"] == "no"
    assert current_active_workstream["qft_gr_operator_domain_assumption_reduction_packet_classification"] == (
        "qft_gr_operator_domain_assumption_reduction_packet_prepared_no_"
        "conservation_witness_or_seam_closure"
    )
    assert current_active_workstream["operator_domain_assumption_inventory_prepared"] == "yes"
    assert current_active_workstream["operator_domain_assumption_reduction_analysis_prepared"] == "yes"
    assert current_active_workstream["operator_domain_assumption_row_count"] == "6"
    assert current_active_workstream["selected_assumption_family"] == (
        "mathematical_regularity_assumptions"
    )
    assert current_active_workstream["assumptions_reduced_or_discharged_by_preparation"] == "no"
    assert current_active_workstream["result_review_target_selected"] == "yes"
    assert current_active_workstream["operational_position_material_in_scope"] == "no"
    assert current_active_workstream["qft_gr_operator_domain_assumption_reduction_packet_result_review_classification"] == (
        "qft_gr_operator_domain_assumption_reduction_packet_result_review_accepts_"
        "operator_domain_reduction_analysis_and_authorizes_next_bounded_assumption_"
        "target_only"
    )
    assert current_active_workstream["operator_domain_assumption_rows_confirmed_by_review"] == "yes"
    assert current_active_workstream["operator_domain_assumption_row_count_confirmed_by_review"] == "6"
    assert current_active_workstream["selected_operator_domain_assumption_row"] == (
        "OD-ASSUMP-006-metric_connection_scope"
    )
    assert current_active_workstream["selected_operator_domain_assumption_row_status"] == (
        "accepted|reduced_for_lane"
    )
    assert current_active_workstream["selected_operator_domain_assumption_reduction_target"] == (
        OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TARGET
    )
    assert current_active_workstream["packet_preparation_only_confirmed_by_review"] == "yes"
    assert current_active_workstream["assumptions_discharged_by_review"] == "no"
    assert current_active_workstream["result_review_accepted"] == "yes"
    assert current_active_workstream["result_review_completed"] == "yes"
    assert current_active_workstream["result_review_pending"] == "no"
    assert current_active_workstream["qft_gr_selected_operator_action_assumption_reduction_packet_classification"] == (
        "qft_gr_selected_operator_action_assumption_reduction_packet_prepared_no_"
        "assumption_discharge_or_seam_closure"
    )
    assert current_active_workstream["selected_operator_action_assumption_row"] == (
        "OD-ASSUMP-001-selected_operator_action"
    )
    assert current_active_workstream["selected_operator_action_assumption_status_tokens"] == (
        "required|supplied|missing|candidate_reducible"
    )
    assert current_active_workstream["selected_operator_action_assumption_reduction_analysis_prepared"] == "yes"
    assert current_active_workstream["selected_operator_action_assumption_available_repo_evidence_recorded"] == "yes"
    assert current_active_workstream["selected_operator_action_assumption_required_future_proof_object_recorded"] == "yes"
    assert current_active_workstream["selected_operator_action_assumption_candidate_reduction_route_recorded"] == "yes"
    assert current_active_workstream["selected_operator_action_assumption_claim_ceiling_recorded"] == "yes"
    assert current_active_workstream["selected_operator_action_assumption_failure_mode_recorded"] == "yes"
    assert current_active_workstream["selected_row_count"] == "1"
    assert current_active_workstream["selected_row_only_confirmed"] == "yes"
    assert current_active_workstream["operator_action_assumption_discharged"] == "no"
    assert current_active_workstream["qft_gr_selected_operator_action_assumption_reduction_packet_result_review_classification"] == (
        "qft_gr_selected_operator_action_assumption_reduction_packet_result_review_"
        "accepts_selected_operator_action_analysis_and_authorizes_bounded_reduction_"
        "attempt_only"
    )
    assert current_active_workstream["selected_operator_action_analysis_accepted_by_review"] == "yes"
    assert current_active_workstream["packet_preparation_only_confirmed_by_selected_operator_action_review"] == "yes"
    assert current_active_workstream["operator_action_assumption_discharged_by_review"] == "no"
    assert current_active_workstream["assumptions_reduced_or_discharged_by_review"] == "no"
    assert current_active_workstream["bounded_reduction_attempt_authorized"] == "yes"
    assert (
        current_active_workstream[
            "selected_operator_action_assumption_reduction_attempt_target"
        ]
        == "execute_qft_gr_selected_operator_action_assumption_reduction_attempt"
    )
    assert current_active_workstream["authorized_attempt_result_classification_count"] == "3"
    assert current_active_workstream["authorized_attempt_result_classifications"] == (
        "qft_gr_state_admissibility_boundary_assumption_reduced_pending_result_review|"
        "qft_gr_state_admissibility_boundary_assumption_obstruction_identified_"
        "requires_refinement|"
        "qft_gr_state_admissibility_boundary_assumption_inconclusive_requires_"
        "assumption_reduction"
    )
    assert current_active_workstream["qft_gr_selected_operator_action_assumption_reduction_attempt_classification"] == (
        "qft_gr_selected_operator_action_assumption_reduced_pending_result_review"
    )
    assert current_active_workstream["selected_operator_action_assumption_reduction_attempt_executed"] == "yes"
    assert current_active_workstream["selected_operator_action_attempt_result_classification_count"] == "1"
    assert current_active_workstream["selected_operator_action_contract_id"] == (
        "OD-ASSUMP-001-selected_operator_action_contract_v0"
    )
    assert current_active_workstream["operator_action_assumption_reduced_pending_result_review"] == "yes"
    assert current_active_workstream["operator_action_assumption_obstruction_identified"] == "no"
    assert current_active_workstream["operator_action_assumption_inconclusive"] == "no"
    assert current_active_workstream["assumption_discharge_claimed"] == "no"
    assert current_active_workstream["assumptions_reduced_or_discharged_by_implication"] == "no"
    assert (
        current_active_workstream["selected_operator_action_attempt_result_review_target"]
        == "review_qft_gr_selected_operator_action_assumption_reduction_attempt_result"
    )
    assert current_active_workstream["selected_operator_action_result_reviewed"] == "yes"
    assert (
        current_active_workstream["selected_operator_action_result_review_classification"]
        == (
            "qft_gr_selected_operator_action_assumption_reduction_attempt_result_review_"
            "accepts_reduced_operator_action_assumption_and_authorizes_next_operator_"
            "domain_row_selection_only"
        )
    )
    assert current_active_workstream["selected_operator_action_reduction_accepted_by_result_review"] == "yes"
    assert current_active_workstream["selected_operator_action_reduction_rejected_by_result_review"] == "no"
    assert current_active_workstream["selected_operator_action_result_review_accepted_contract_id"] == (
        "OD-ASSUMP-001-selected_operator_action_contract_v0"
    )
    assert current_active_workstream["next_operator_domain_assumption_row"] == (
        "OD-ASSUMP-006-metric_connection_scope"
    )
    assert (
        current_active_workstream["next_operator_domain_assumption_reduction_target"]
        == OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TARGET
    )
    assert current_active_workstream["qft_gr_candidate_source_domain_membership_assumption_reduction_packet_classification"] == (
        "qft_gr_candidate_source_domain_membership_assumption_reduction_packet_"
        "prepared_with_no_source_admissibility_or_seam_closure"
    )
    assert current_active_workstream["candidate_source_domain_membership_packet_prepared"] == "yes"
    assert current_active_workstream["candidate_source_domain_membership_packet_preparation_only"] == "yes"
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_reduction_analysis_prepared"
        ]
        == "yes"
    )
    assert current_active_workstream["candidate_source_domain_membership_assumption_row"] == (
        "OD-ASSUMP-002-candidate_source_domain_membership"
    )
    assert current_active_workstream["candidate_source_domain_membership_status_tokens"] == (
        "required|missing|candidate_reducible"
    )
    assert current_active_workstream["candidate_source_object"] == (
        "candidate_stress_energy_source"
    )
    assert current_active_workstream["operator_domain_membership_condition"] == (
        "candidate_stress_energy_source_in_prepared_operator_domain"
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_packet_result_review_target"
        ]
        == PACKET_RESULT_REVIEW_TARGET
    )
    assert current_active_workstream["candidate_source_domain_membership_packet_result_reviewed"] == "yes"
    assert current_active_workstream["qft_gr_candidate_source_domain_membership_assumption_reduction_packet_result_review_classification"] == (
        "qft_gr_candidate_source_domain_membership_assumption_reduction_packet_"
        "result_review_accepts_packet_and_authorizes_bounded_reduction_attempt_only"
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_packet_accepted_by_result_review"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_analysis_accepted_by_result_review"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "bounded_candidate_source_domain_membership_reduction_attempt_authorized"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_reduction_attempt_target"
        ]
        == ATTEMPT_TARGET
    )
    assert (
        current_active_workstream[
            "authorized_candidate_source_domain_membership_attempt_result_classification_count"
        ]
        == "3"
    )
    assert (
        current_active_workstream[
            "authorized_candidate_source_domain_membership_attempt_result_classifications"
        ]
        == (
            "qft_gr_candidate_source_domain_membership_assumption_reduced_pending_result_review|"
            "qft_gr_candidate_source_domain_membership_assumption_obstruction_identified_requires_refinement|"
            "qft_gr_candidate_source_domain_membership_assumption_inconclusive_requires_assumption_reduction"
        )
    )
    assert current_active_workstream["source_admissibility_claimed"] == "no"
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_reduction_attempt_classification"
        ]
        == "qft_gr_candidate_source_domain_membership_assumption_reduced_pending_result_review"
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_reduction_attempt_executed"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_attempt_result_classification_count"
        ]
        == "1"
    )
    assert current_active_workstream["candidate_source_domain_membership_contract_id"] == (
        "OD-ASSUMP-002-candidate_source_domain_membership_contract_v0"
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_reduced_pending_result_review"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_obstruction_identified"
        ]
        == "no"
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_inconclusive"
        ]
        == "no"
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_reduction_attempt_result_review_target"
        ]
        == CANDIDATE_SOURCE_ATTEMPT_REVIEW_TARGET
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_reduction_attempt_result_reviewed"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_reduction_attempt_result_review_accepted"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_reduction_attempt_result_review_classification"
        ]
        == (
            "qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_"
            "result_review_accepts_reduced_source_domain_membership_assumption_"
            "and_authorizes_next_operator_domain_row_selection_only"
        )
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_reduction_attempt_result_review_token"
        ]
        == (
            "QFT_GR_CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_ASSUMPTION_REDUCTION_ATTEMPT_"
            "RESULT_REVIEW_ACCEPTS_REDUCED_SOURCE_DOMAIN_MEMBERSHIP_ASSUMPTION_AND_"
            "AUTHORIZES_NEXT_OPERATOR_DOMAIN_ROW_SELECTION_ONLY"
        )
    )
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_reduction_rejected_by_review"
        ]
        == "no"
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_packet_target"
        ]
        == STATE_EXPECTATION_PACKET_TARGET
    )
    assert current_active_workstream["state_expectation_domain_link_assumption_row"] == (
        "OD-ASSUMP-003-state_expectation_domain_link"
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_packet_classification"
        ]
        == (
            "qft_gr_state_expectation_domain_link_assumption_reduction_packet_"
            "prepared_with_no_conservation_witness_or_seam_closure"
        )
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_packet_token"
        ]
        == (
            "QFT_GR_STATE_EXPECTATION_DOMAIN_LINK_ASSUMPTION_REDUCTION_PACKET_"
            "PREPARED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
        )
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_packet_result_review_target"
        ]
        == STATE_EXPECTATION_PACKET_RESULT_REVIEW_TARGET
    )
    assert current_active_workstream["state_expectation_object"] == (
        "qft_state_expectation_functional"
    )
    assert current_active_workstream["operator_domain_link_condition"] == (
        "state_expectation_semantics_preserve_operator_domain_membership"
    )
    assert current_active_workstream["state_expectation_domain_link_packet_prepared"] == "yes"
    assert (
        current_active_workstream["state_expectation_domain_link_packet_preparation_only"]
        == "yes"
    )
    assert (
        current_active_workstream["state_expectation_domain_link_claimed_as_operator_domain_closed"]
        == "no"
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_packet_result_review_target"
        ]
        == STATE_EXPECTATION_PACKET_RESULT_REVIEW_TARGET
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_packet_result_review_accepted"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_packet_result_review_classification"
        ]
        == (
            "qft_gr_state_expectation_domain_link_assumption_reduction_packet_"
            "result_review_accepts_packet_and_authorizes_bounded_reduction_"
            "attempt_only"
        )
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_packet_result_review_token"
        ]
        == (
            "QFT_GR_STATE_EXPECTATION_DOMAIN_LINK_ASSUMPTION_REDUCTION_PACKET_"
            "RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_REDUCTION_"
            "ATTEMPT_ONLY"
        )
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_packet_accepted_by_result_review"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduced_by_review"
        ]
        == "no"
    )
    assert (
        current_active_workstream[
            "bounded_state_expectation_domain_link_reduction_attempt_authorized"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "authorized_state_expectation_domain_link_attempt_result_classification_count"
        ]
        == "3"
    )
    assert (
        current_active_workstream[
            "authorized_state_expectation_domain_link_attempt_result_classifications"
        ]
        == (
            "qft_gr_state_expectation_domain_link_assumption_reduced_pending_result_review|"
            "qft_gr_state_expectation_domain_link_assumption_obstruction_identified_requires_refinement|"
            "qft_gr_state_expectation_domain_link_assumption_inconclusive_requires_assumption_reduction"
        )
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_attempt_target"
        ]
        == STATE_EXPECTATION_ATTEMPT_TARGET
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_attempt_classification"
        ]
        == "qft_gr_state_expectation_domain_link_assumption_reduced_pending_result_review"
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_attempt_executed"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_attempt_result_classification_count"
        ]
        == "1"
    )
    assert current_active_workstream["state_expectation_domain_link_contract_id"] == (
        "OD-ASSUMP-003-state_expectation_domain_link_contract_v0"
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduced_pending_result_review"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_obstruction_identified"
        ]
        == "no"
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_inconclusive"
        ]
        == "no"
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_attempt_result_review_target"
        ]
        == STATE_EXPECTATION_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_attempt_result_review_accepted"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_attempt_result_review_classification"
        ]
        == (
            "qft_gr_state_expectation_domain_link_assumption_reduction_attempt_"
            "result_review_accepts_reduced_state_expectation_domain_link_and_"
            "authorizes_next_operator_domain_row_selection_only"
        )
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_attempt_result_review_token"
        ]
        == (
            "QFT_GR_STATE_EXPECTATION_DOMAIN_LINK_ASSUMPTION_REDUCTION_ATTEMPT_"
            "RESULT_REVIEW_ACCEPTS_REDUCED_STATE_EXPECTATION_DOMAIN_LINK_AND_"
            "AUTHORIZES_NEXT_OPERATOR_DOMAIN_ROW_SELECTION_ONLY"
        )
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_attempt_result_reviewed"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "state_expectation_domain_link_assumption_reduction_accepted_by_review"
        ]
        == "yes"
    )
    assert current_active_workstream["next_operator_domain_assumption_row"] == (
        "OD-ASSUMP-006-metric_connection_scope"
    )
    assert current_active_workstream["renormalized_expectation_domain_link_next_row"] == (
        "OD-ASSUMP-005-conservation_form_scope"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_link_packet_preparation_authorized"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_packet_target"
    ] == RENORMALIZED_EXPECTATION_DOMAIN_LINK_PACKET_TARGET
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_packet_prepared"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_packet_result_review_target"
    ] == RENORMALIZED_EXPECTATION_DOMAIN_LINK_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_packet_classification"
    ] == (
        "qft_gr_renormalized_expectation_domain_link_assumption_reduction_"
        "packet_prepared_with_no_source_admissibility_or_seam_closure"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_packet_token"
    ] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_LINK_ASSUMPTION_REDUCTION_"
        "PACKET_PREPARED_WITH_NO_SOURCE_ADMISSIBILITY_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_packet_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_packet_result_review_classification"
    ] == (
        "qft_gr_renormalized_expectation_domain_link_assumption_reduction_packet_"
        "result_review_accepts_packet_and_authorizes_bounded_reduction_attempt_only"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_packet_result_review_token"
    ] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_LINK_ASSUMPTION_REDUCTION_PACKET_"
        "RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_REDUCTION_ATTEMPT_ONLY"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_attempt_target"
    ] == RENORMALIZED_EXPECTATION_DOMAIN_LINK_ATTEMPT_TARGET
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_attempt_executed"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_attempt_classification"
    ] == (
        "qft_gr_renormalized_expectation_domain_link_assumption_reduced_pending_"
        "result_review"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_attempt_token"
    ] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_LINK_ASSUMPTION_REDUCTION_"
        "ATTEMPT_EXECUTED_WITH_NO_SOURCE_ADMISSIBILITY_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_attempt_contract_id"
    ] == "OD-ASSUMP-004-renormalized_expectation_domain_link_contract_v0"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_attempt_result_review_target"
    ] == RENORMALIZED_EXPECTATION_DOMAIN_LINK_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_attempt_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_attempt_result_review_classification"
    ] == (
        "qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_"
        "result_review_accepts_reduced_renormalized_expectation_domain_link_and_"
        "authorizes_next_operator_domain_row_selection_only"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_attempt_result_review_token"
    ] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_LINK_ASSUMPTION_REDUCTION_"
        "ATTEMPT_RESULT_REVIEW_ACCEPTS_REDUCED_RENORMALIZED_EXPECTATION_"
        "DOMAIN_LINK_AND_AUTHORIZES_NEXT_OPERATOR_DOMAIN_ROW_SELECTION_ONLY"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduction_rejected"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_next_row"
    ] == "OD-ASSUMP-005-conservation_form_scope"
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_packet_target"
    ] == CONSERVATION_FORM_SCOPE_PACKET_TARGET
    assert current_active_workstream[
        "conservation_form_scope_packet_preparation_authorized"
    ] == "yes"
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_packet_prepared"
    ] == "yes"
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_packet_classification"
    ] == (
        "qft_gr_conservation_form_scope_assumption_reduction_packet_prepared_"
        "with_no_conservation_witness_or_seam_closure"
    )
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_packet_token"
    ] == (
        "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_PACKET_PREPARED_"
        "WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_packet_result_review_target"
    ] == CONSERVATION_FORM_SCOPE_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_packet_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_packet_result_review_classification"
    ] == (
        "qft_gr_conservation_form_scope_assumption_reduction_packet_result_"
        "review_accepts_packet_and_authorizes_bounded_reduction_attempt_only"
    )
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_packet_result_review_token"
    ] == (
        "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_PACKET_RESULT_"
        "REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_REDUCTION_ATTEMPT_ONLY"
    )
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduced_by_review"
    ] == "no"
    assert current_active_workstream[
        "conservation_form_scope_assumption_discharged_by_review"
    ] == "no"
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_attempt_target"
    ] == CONSERVATION_FORM_SCOPE_ATTEMPT_TARGET
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_attempt_executed"
    ] == "yes"
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_attempt_classification"
    ] == "qft_gr_conservation_form_scope_assumption_reduced_pending_result_review"
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_attempt_token"
    ] == (
        "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_"
        "EXECUTED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_attempt_contract_id"
    ] == "OD-ASSUMP-005-conservation_form_scope_contract_v0"
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_attempt_result_review_target"
    ] == CONSERVATION_FORM_SCOPE_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_attempt_result_reviewed"
    ] == "yes"
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_attempt_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_attempt_result_review_classification"
    ] == (
        "qft_gr_conservation_form_scope_assumption_reduction_attempt_result_review_"
        "accepts_reduced_conservation_form_scope_and_authorizes_next_operator_domain_"
        "row_selection_only"
    )
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_attempt_result_review_token"
    ] == (
        "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_"
        "ACCEPTS_REDUCED_CONSERVATION_FORM_SCOPE_AND_AUTHORIZES_NEXT_OPERATOR_"
        "DOMAIN_ROW_SELECTION_ONLY"
    )
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduction_attempt_result_review_selected_next_target"
    ] == METRIC_CONNECTION_SCOPE_PACKET_TARGET
    assert current_active_workstream[
        "conservation_form_scope_next_row_packet_target"
    ] == METRIC_CONNECTION_SCOPE_PACKET_TARGET
    assert current_active_workstream[
        "metric_connection_scope_packet_preparation_authorized"
    ] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_packet_target"
    ] == METRIC_CONNECTION_SCOPE_PACKET_TARGET
    assert current_active_workstream[
        "metric_connection_scope_next_operator_domain_assumption_row"
    ] == "OD-ASSUMP-006-metric_connection_scope"
    assert current_active_workstream["metric_connection_scope_packet_prepared"] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_packet_result_review_target"
    ] == METRIC_CONNECTION_SCOPE_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_packet_selected_next_target"
    ] == METRIC_CONNECTION_SCOPE_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_packet_token"
    ] == (
        "QFT_GR_METRIC_CONNECTION_SCOPE_ASSUMPTION_REDUCTION_PACKET_PREPARED_"
        "WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_packet_classification"
    ] == (
        "qft_gr_metric_connection_scope_assumption_reduction_packet_prepared_"
        "with_no_conservation_witness_or_seam_closure"
    )
    assert current_active_workstream[
        "metric_connection_scope_selected_operator_domain_assumption_row"
    ] == "OD-ASSUMP-006-metric_connection_scope"
    assert current_active_workstream[
        "metric_connection_scope_status_tokens"
    ] == "required|supplied|missing|candidate_reducible"
    assert current_active_workstream["metric_connection_scope_object"] == (
        "bounded_metric_connection_scope_for_selected_operator_domain"
    )
    assert current_active_workstream["metric_connection_scope_bounded_geometry_domain"] == (
        "selected_operator_domain_bounded_geometry_domain"
    )
    assert current_active_workstream[
        "metric_connection_scope_connection_compatibility_condition"
    ] == (
        "connection_preserves_selected_operator_domain_metric_scope_without_bianchi_claim"
    )
    assert current_active_workstream[
        "metric_connection_scope_required_future_proof_object"
    ] == "bounded_metric_connection_scope_supports_selected_operator_domain"
    assert current_active_workstream[
        "metric_connection_scope_reduction_analysis_prepared"
    ] == "yes"
    assert current_active_workstream["metric_connection_scope_packet_result_reviewed"] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_packet_result_reviewed"
    ] == "yes"
    assert (
        current_active_workstream["metric_connection_scope_packet_result_review_accepted"]
        == "yes"
    )
    assert (
        current_active_workstream[
            "metric_connection_scope_packet_accepted_by_result_review"
        ]
        == "yes"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_packet_result_review_selected_next_target"
    ] == METRIC_CONNECTION_SCOPE_ATTEMPT_TARGET
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_packet_result_review_token"
    ] == (
        "QFT_GR_METRIC_CONNECTION_SCOPE_ASSUMPTION_REDUCTION_PACKET_RESULT_"
        "REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_REDUCTION_ATTEMPT_ONLY"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_packet_result_review_classification"
    ] == (
        "qft_gr_metric_connection_scope_assumption_reduction_packet_result_"
        "review_accepts_packet_and_authorizes_bounded_reduction_attempt_only"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_packet_result_review_report"
    ] == (
        "formal/docs/release/QFT_GR_METRIC_CONNECTION_SCOPE_ASSUMPTION_REDUCTION_"
        "PACKET_RESULT_REVIEW_20260527_v0.json"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_packet_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_MetricConnectionScopeAssumptionReductionPacketResultReview.lean"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_packet_result_review_gate"
    ] == (
        "formal/python/tests/test_qft_gr_metric_connection_scope_assumption_"
        "reduction_packet_result_review_gate.py"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduced_by_review"
    ] == "no"
    assert current_active_workstream[
        "metric_connection_scope_assumption_discharged_by_review"
    ] == "no"
    assert current_active_workstream[
        "metric_connection_scope_bounded_reduction_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_target"
    ] == METRIC_CONNECTION_SCOPE_ATTEMPT_TARGET
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_executed"
    ] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_classification"
    ] == "qft_gr_metric_connection_scope_assumption_reduced_pending_result_review"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_token"
    ] == (
        "QFT_GR_METRIC_CONNECTION_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_"
        "EXECUTED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_contract_id"
    ] == "OD-ASSUMP-006-metric_connection_scope_contract_v0"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_report"
    ] == (
        "formal/docs/release/QFT_GR_METRIC_CONNECTION_SCOPE_ASSUMPTION_REDUCTION_"
        "ATTEMPT_20260527_v0.json"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_MetricConnectionScopeAssumptionReductionAttempt.lean"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_metric_connection_scope_assumption_reduction_attempt_report.py"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_gate"
    ] == (
        "formal/python/tests/test_qft_gr_metric_connection_scope_assumption_"
        "reduction_attempt_gate.py"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_selected_next_target"
    ] == METRIC_CONNECTION_SCOPE_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_result_review_target"
    ] == METRIC_CONNECTION_SCOPE_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_result_reviewed"
    ] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_result_review_authorized"
    ] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_result_review_classification"
    ] == (
        "qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review_"
        "accepts_reduced_metric_connection_scope_and_authorizes_operator_domain_"
        "assumption_reduction_closeout_preparation_only"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_result_review_token"
    ] == (
        "QFT_GR_METRIC_CONNECTION_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_"
        "ACCEPTS_REDUCED_METRIC_CONNECTION_SCOPE_AND_AUTHORIZES_OPERATOR_DOMAIN_"
        "ASSUMPTION_REDUCTION_CLOSEOUT_PREPARATION_ONLY"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_result_review_report"
    ] == (
        "formal/docs/release/QFT_GR_METRIC_CONNECTION_SCOPE_ASSUMPTION_REDUCTION_"
        "ATTEMPT_RESULT_REVIEW_20260527_v0.json"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_MetricConnectionScopeAssumptionReductionAttemptResultReview.lean"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_result_review_gate"
    ] == (
        "formal/python/tests/test_qft_gr_metric_connection_scope_assumption_"
        "reduction_attempt_result_review_gate.py"
    )
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_attempt_result_review_selected_next_target"
    ] == OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TARGET
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_accepted"
    ] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_rejected"
    ] == "no"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduced_pending_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduction_accepted_by_result_review"
    ] == "yes"
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_packet_authorized"
    ] == "yes"
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_preparation_only"
    ] == "yes"
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_target"
    ] == OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TARGET
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_packet_prepared"
    ] == "yes"
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_prepared"
    ] == "yes"
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_status"
    ] == "prepared_pending_result_review"
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_packet_result_review_required"
    ] == "yes"
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_packet_result_review_target"
    ] == OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_packet_selected_next_target"
    ] == OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_packet_classification"
    ] == (
        "qft_gr_operator_domain_assumption_reduction_closeout_packet_prepared_"
        "with_no_conservation_witness_or_seam_closure"
    )
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_packet_token"
    ] == (
        "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_PREPARED_"
        "WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_packet_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_packet_result_reviewed"
    ] == "yes"
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_packet_result_review_target"
    ] == OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "operator_domain_assumption_reduction_closeout_packet_result_review_token"
    ] == (
        "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_RESULT_REVIEW_"
        "ACCEPTS_OPERATOR_DOMAIN_ROWS_AND_AUTHORIZES_NEXT_ASSUMPTION_FAMILY_SELECTION_ONLY"
    )
    assert current_active_workstream[
        "operator_domain_assumptions_closed_for_this_lane"
    ] == "yes"
    assert current_active_workstream["next_assumption_family"] == (
        "mathematical_regularity_assumptions"
    )
    assert current_active_workstream[
        "renormalization_assumption_reduction_packet_authorized"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_assumption_reduction_packet_target"
    ] == RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "renormalization_assumption_reduction_packet_selected_next_target"
    ] == RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalization_assumption_reduction_packet_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_assumption_reduction_packet_result_reviewed"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_assumption_reduction_packet_result_review_token"
    ] == (
        "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_"
        "ACCEPTS_RENORMALIZATION_FAMILY_ANALYSIS_AND_AUTHORIZES_NEXT_BOUNDED_"
        "RENORMALIZATION_TARGET_ONLY"
    )
    assert current_active_workstream[
        "renormalization_assumption_reduction_packet_result_review_classification"
    ] == (
        "qft_gr_renormalization_assumption_reduction_packet_result_review_accepts_"
        "renormalization_family_analysis_and_authorizes_next_bounded_"
        "renormalization_target_only"
    )
    assert current_active_workstream[
        "renormalization_family_analysis_accepted_by_result_review"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_packet_preparation_only_confirmed_by_result_review"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_assumptions_discharged_by_result_review"
    ] == "no"
    assert current_active_workstream[
        "selected_bounded_renormalization_assumption_row"
    ] == "RN-ASSUMP-005-operator_domain_compatibility"
    assert current_active_workstream[
        "selected_bounded_renormalization_assumption_target"
    ] == RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_target"
    ] == RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_prepared"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_PACKET_20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizedStressEnergyObjectAssumptionReductionPacket.lean"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_renormalized_stress_energy_object_assumption_reduction_packet_report.py"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_gate"
    ] == (
        "formal/python/tests/"
        "test_qft_gr_renormalized_stress_energy_object_assumption_reduction_packet_gate.py"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_token"
    ] == (
        "QFT_GR_RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_PACKET_"
        "PREPARED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_classification"
    ] == (
        "qft_gr_renormalized_stress_energy_object_assumption_reduction_packet_"
        "prepared_with_no_conservation_witness_or_seam_closure"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_selected_next_target"
    ] == RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_result_review_target"
    ] == RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_result_reviewed"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_result_review_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_PACKET_"
        "RESULT_REVIEW_20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizedStressEnergyObjectAssumptionReductionPacketResultReview.lean"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_result_review_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_renormalized_stress_energy_object_assumption_reduction_packet_"
        "result_review_report.py"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_result_review_gate"
    ] == (
        "formal/python/tests/"
        "test_qft_gr_renormalized_stress_energy_object_assumption_reduction_packet_"
        "result_review_gate.py"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_result_review_token"
    ] == (
        "QFT_GR_RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_PACKET_"
        "RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_REDUCTION_ATTEMPT_ONLY"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_result_review_classification"
    ] == (
        "qft_gr_renormalized_stress_energy_object_assumption_reduction_packet_"
        "result_review_accepts_packet_and_authorizes_bounded_reduction_attempt_only"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_packet_result_review_selected_next_target"
    ] == RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_target"
    ] == RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_executed"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_"
        "ATTEMPT_20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizedStressEnergyObjectAssumptionReductionAttempt.lean"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_renormalized_stress_energy_object_assumption_reduction_"
        "attempt_report.py"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_gate"
    ] == (
        "formal/python/tests/"
        "test_qft_gr_renormalized_stress_energy_object_assumption_reduction_"
        "attempt_gate.py"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_token"
    ] == (
        "QFT_GR_RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_"
        "EXECUTED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_classification"
    ] == (
        "qft_gr_renormalized_stress_energy_object_assumption_reduced_pending_result_review"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_contract_id"
    ] == "RN-ASSUMP-001-renormalized_stress_energy_object_contract_v0"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_contract_status"
    ] == (
        "bounded_candidate_renormalized_stress_energy_object_contract_pending_"
        "result_review_not_final_definition_or_discharge"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_result_review_target"
    ] == RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_selected_next_target"
    ] == RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_result_reviewed"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_result_review_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_"
        "ATTEMPT_RESULT_REVIEW_20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizedStressEnergyObjectAssumptionReductionAttemptResultReview.lean"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_result_review_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_renormalized_stress_energy_object_assumption_reduction_"
        "attempt_result_review_report.py"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_result_review_gate"
    ] == (
        "formal/python/tests/"
        "test_qft_gr_renormalized_stress_energy_object_assumption_reduction_"
        "attempt_result_review_gate.py"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_result_review_token"
    ] == (
        "QFT_GR_RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_"
        "RESULT_REVIEW_ACCEPTS_REDUCED_RENORMALIZED_STRESS_ENERGY_OBJECT_AND_"
        "AUTHORIZES_NEXT_RENORMALIZATION_ROW_SELECTION_ONLY"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_result_review_classification"
    ] == (
        "qft_gr_renormalized_stress_energy_object_assumption_reduction_attempt_"
        "result_review_accepts_reduced_renormalized_stress_energy_object_and_"
        "authorizes_next_renormalization_row_selection_only"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_result_review_selected_next_row"
    ] == "RN-ASSUMP-002-renormalization_scope"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_attempt_result_review_selected_next_target"
    ] == RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "renormalized_stress_energy_object_authorized_attempt_result_classification_count"
    ] == "3"
    assert current_active_workstream[
        "renormalized_stress_energy_object_authorized_attempt_result_classifications"
    ] == (
        "qft_gr_renormalized_stress_energy_object_assumption_reduced_pending_result_review|"
        "qft_gr_renormalized_stress_energy_object_assumption_obstruction_identified_requires_refinement|"
        "qft_gr_renormalized_stress_energy_object_assumption_inconclusive_requires_assumption_reduction"
    )
    assert current_active_workstream[
        "renormalized_stress_energy_object_final_definition_claimed_by_review"
    ] == "no"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_discharged_by_review"
    ] == "no"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduced_by_review"
    ] == "no"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduced_by_attempt"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduced_pending_result_review"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_stress_energy_object_final_definition_claimed_by_attempt"
    ] == "no"
    assert current_active_workstream[
        "renormalized_stress_energy_object_final_definition_or_discharge_claimed_by_implication"
    ] == "no"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_discharged_by_attempt"
    ] == "no"
    assert current_active_workstream[
        "renormalized_stress_energy_object_claims_source_admissibility"
    ] == "no"
    assert current_active_workstream[
        "renormalized_stress_energy_object_claims_bianchi_compatibility"
    ] == "no"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduction_analysis_prepared"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_stress_energy_object_selected_row_only_confirmed"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_row"
    ] == "RN-ASSUMP-001-renormalized_stress_energy_object"
    assert current_active_workstream[
        "renormalized_stress_energy_object_status_tokens"
    ] == "required|supplied|candidate_reducible"
    assert current_active_workstream[
        "renormalized_stress_energy_object_definition_status"
    ] == "candidate_object_selected_for_reduction_analysis_not_final_definition_or_discharge"
    assert current_active_workstream[
        "renormalized_stress_energy_object_final_definition_claimed"
    ] == "no"
    assert current_active_workstream[
        "renormalized_stress_energy_object_defined_as_final"
    ] == "no"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_discharged"
    ] == "no"
    assert current_active_workstream[
        "renormalized_stress_energy_object_assumption_reduced_or_discharged_by_preparation"
    ] == "no"
    assert current_active_workstream[
        "renormalized_stress_energy_object_required_future_proof_object"
    ] == "renormalized_stress_energy_object_selected_for_candidate_source"
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_packet_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_packet_result_review_selected_next_target"
    ] == RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_target"
    ] == RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_executed"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_classification"
    ] == "qft_gr_renormalization_scope_assumption_reduced_pending_result_review"
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_token"
    ] == (
        "QFT_GR_RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_EXECUTED_"
        "WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_contract_id"
    ] == "RN-ASSUMP-002-renormalization_scope_contract_v0"
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_contract_status"
    ] == (
        "bounded_repo_local_renormalization_scope_contract_pending_result_review_"
        "not_scope_discharge"
    )
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_result_review_target"
    ] == RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_selected_next_target"
    ] == RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalization_scope_assumption_reduced_pending_result_review"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_scope_assumption_obstruction_identified"
    ] == "no"
    assert current_active_workstream[
        "renormalization_scope_assumption_inconclusive"
    ] == "no"
    assert current_active_workstream[
        "renormalization_scope_assumption_reduced_by_attempt"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_scope_assumption_discharged_by_attempt"
    ] == "no"
    assert current_active_workstream[
        "renormalization_scope_assumption_discharged_by_implication"
    ] == "no"
    assert current_active_workstream[
        "renormalization_scope_claims_source_admissibility"
    ] == "no"
    assert current_active_workstream[
        "renormalization_scope_claims_bianchi_compatibility"
    ] == "no"
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_result_review_target"
    ] == RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_result_reviewed"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_result_review_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_"
        "20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizationScopeAssumptionReductionAttemptResultReview.lean"
    )
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_result_review_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_renormalization_scope_assumption_reduction_attempt_result_review_report.py"
    )
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_result_review_gate"
    ] == (
        "formal/python/tests/"
        "test_qft_gr_renormalization_scope_assumption_reduction_attempt_result_review_gate.py"
    )
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_result_review_token"
    ] == (
        "QFT_GR_RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_"
        "ACCEPTS_REDUCED_RENORMALIZATION_SCOPE_AND_AUTHORIZES_NEXT_"
        "RENORMALIZATION_ROW_SELECTION_ONLY"
    )
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_result_review_classification"
    ] == (
        "qft_gr_renormalization_scope_assumption_reduction_attempt_result_review_"
        "accepts_reduced_renormalization_scope_and_authorizes_next_"
        "renormalization_row_selection_only"
    )
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_result_review_selected_next_row"
    ] == "RN-ASSUMP-003-renormalized_expectation_domain"
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_attempt_result_review_selected_next_target"
    ] == RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_scope_assumption_reduction_rejected"
    ] == "no"
    assert current_active_workstream[
        "renormalization_scope_assumption_discharged_by_review"
    ] == "no"
    assert current_active_workstream[
        "renormalization_scope_assumption_reduced_or_discharged_by_review"
    ] == "no"
    assert current_active_workstream[
        "next_renormalization_assumption_row"
    ] == "RN-ASSUMP-005-operator_domain_compatibility"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_prepared"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_target"
    ] == RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_"
        "20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizedExpectationDomainAssumptionReductionPacket.lean"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_renormalized_expectation_domain_assumption_reduction_packet_report.py"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_gate"
    ] == (
        "formal/python/tests/"
        "test_qft_gr_renormalized_expectation_domain_assumption_reduction_packet_gate.py"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_token"
    ] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_"
        "PREPARED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_classification"
    ] == (
        "qft_gr_renormalized_expectation_domain_assumption_reduction_packet_prepared_"
        "with_no_conservation_witness_or_seam_closure"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_selected_row"
    ] == "RN-ASSUMP-003-renormalized_expectation_domain"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_selected_next_target"
    ] == RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_result_reviewed"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_result_review_target"
    ] == RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_result_review_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_"
        "RESULT_REVIEW_20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizedExpectationDomainAssumptionReductionPacketResultReview.lean"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_result_review_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_renormalized_expectation_domain_assumption_reduction_packet_result_review_report.py"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_result_review_gate"
    ] == (
        "formal/python/tests/"
        "test_qft_gr_renormalized_expectation_domain_assumption_reduction_packet_result_review_gate.py"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_result_review_token"
    ] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_"
        "RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_REDUCTION_ATTEMPT_ONLY"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_result_review_classification"
    ] == (
        "qft_gr_renormalized_expectation_domain_assumption_reduction_packet_"
        "result_review_accepts_packet_and_authorizes_bounded_reduction_attempt_only"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_result_review_selected_next_target"
    ] == RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_packet_result_review_bounded_reduction_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_target"
    ] == RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_executed"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_"
        "20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizedExpectationDomainAssumptionReductionAttempt.lean"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_report.py"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_gate"
    ] == (
        "formal/python/tests/"
        "test_qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_gate.py"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_token"
    ] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_"
        "EXECUTED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_classification"
    ] == "qft_gr_renormalized_expectation_domain_assumption_reduced_pending_result_review"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_contract_id"
    ] == "RN-ASSUMP-003-renormalized_expectation_domain_contract_v0"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_contract_status"
    ] == (
        "bounded_repo_local_renormalized_expectation_domain_contract_pending_"
        "result_review_not_domain_discharge"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_selected_next_target"
    ] == RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_result_review_target"
    ] == RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_result_classification_count"
    ] == "1"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_result_reviewed"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_result_review_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_"
        "RESULT_REVIEW_20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizedExpectationDomainAssumptionReductionAttemptResultReview.lean"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_result_review_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_result_review_report.py"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_result_review_gate"
    ] == (
        "formal/python/tests/"
        "test_qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_result_review_gate.py"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_result_review_token"
    ] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_"
        "RESULT_REVIEW_ACCEPTS_REDUCED_RENORMALIZED_EXPECTATION_DOMAIN_AND_"
        "AUTHORIZES_NEXT_RENORMALIZATION_ROW_SELECTION_ONLY"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_result_review_classification"
    ] == (
        "qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_"
        "result_review_accepts_reduced_renormalized_expectation_domain_and_"
        "authorizes_next_renormalization_row_selection_only"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_result_review_selected_next_row"
    ] == "RN-ASSUMP-004-finiteness_regular_boundary"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_attempt_result_review_selected_next_target"
    ] == RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_prepared"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_target"
    ] == RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_PACKET_"
        "20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizedExpectationFinitenessAssumptionReductionPacket.lean"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_renormalized_expectation_finiteness_assumption_reduction_packet_report.py"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_gate"
    ] == (
        "formal/python/tests/"
        "test_qft_gr_renormalized_expectation_finiteness_assumption_reduction_packet_gate.py"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_token"
    ] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_PACKET_"
        "PREPARED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_classification"
    ] == (
        "qft_gr_renormalized_expectation_finiteness_assumption_reduction_packet_"
        "prepared_with_no_conservation_witness_or_seam_closure"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_selected_row"
    ] == "RN-ASSUMP-004-finiteness_regular_boundary"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_selected_next_target"
    ] == RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_result_review_target"
    ] == RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_status"
    ] == (
        "finiteness_regular_boundary_selected_for_reduction_analysis_not_"
        "renormalization_assumption_discharge"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_boundary_object"
    ] == (
        "finite_regular_renormalized_expectation_required_before_conservation_"
        "proof_object"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_required_future_proof_object"
    ] == (
        "finite_regular_renormalized_expectation_boundary_for_future_conservation_statement"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_prepares_reduction_analysis_only"
    ] == "yes"
    assert current_active_workstream["finiteness_regular_boundary_discharged"] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_constructs_conservation_proof_object"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_constructs_conservation_witness"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_claims_source_admissibility"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_claims_bianchi_compatibility"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_closes_qft_gr_seam"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_result_review_target"
    ] == RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_result_review_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_PACKET_"
        "RESULT_REVIEW_20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizedExpectationFinitenessAssumptionReductionPacketResultReview.lean"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_result_review_token"
    ] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_PACKET_"
        "RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_REDUCTION_ATTEMPT_ONLY"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_result_review_classification"
    ] == (
        "qft_gr_renormalized_expectation_finiteness_assumption_reduction_packet_"
        "result_review_accepts_packet_and_authorizes_bounded_reduction_attempt_only"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_result_review_selected_row"
    ] == "RN-ASSUMP-004-finiteness_regular_boundary"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_result_review_selected_next_target"
    ] == RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_packet_result_review_bounded_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_target"
    ] == RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_executed"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_"
        "20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizedExpectationFinitenessAssumptionReductionAttempt.lean"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_renormalized_expectation_finiteness_assumption_reduction_attempt_report.py"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_gate"
    ] == (
        "formal/python/tests/"
        "test_qft_gr_renormalized_expectation_finiteness_assumption_reduction_attempt_gate.py"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_token"
    ] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_FINITE_REGULARITY_ASSUMPTION_REDUCTION_"
        "ATTEMPT_EXECUTED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_classification"
    ] == (
        "qft_gr_renormalized_expectation_finiteness_assumption_reduced_pending_result_review"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_result_review_target"
    ] == RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_selected_next_target"
    ] == RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_result_review_id"
    ] == "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_result_review_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizedExpectationFinitenessAssumptionReductionAttemptResultReview.lean"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_result_review_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_"
        "RESULT_REVIEW_20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_result_review_token"
    ] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_"
        "RESULT_REVIEW_ACCEPTS_REDUCED_FINITE_REGULAR_BOUNDARY_AND_AUTHORIZES_"
        "NEXT_RENORMALIZATION_ROW_SELECTION_ONLY"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_result_review_classification"
    ] == (
        "qft_gr_renormalized_expectation_finiteness_assumption_reduction_attempt_"
        "result_review_accepts_reduced_finite_regular_boundary_and_authorizes_"
        "next_renormalization_row_selection_only"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_result_review_selected_next_row"
    ] == "RN-ASSUMP-005-operator_domain_compatibility"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_result_review_selected_next_target"
    ] == RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_prepared"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_target"
    ] == RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
        "REDUCTION_PACKET_20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizationOperatorDomainCompatibilityAssumptionReductionPacket.lean"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_packet_report.py"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_gate"
    ] == (
        "formal/python/tests/"
        "test_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_packet_gate.py"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_token"
    ] == (
        "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
        "REDUCTION_PACKET_PREPARED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_classification"
    ] == (
        "qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_"
        "packet_prepared_with_no_conservation_witness_or_seam_closure"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_selected_row"
    ] == "RN-ASSUMP-005-operator_domain_compatibility"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_selected_next_target"
    ] == RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_target"
    ] == RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_reviewed"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_consumed_packet"
    ] == "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_v0"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_prior_rows"
    ] == (
        "RN-ASSUMP-001-renormalized_stress_energy_object|"
        "RN-ASSUMP-002-renormalization_scope|"
        "RN-ASSUMP-003-renormalized_expectation_domain|"
        "RN-ASSUMP-004-finiteness_regular_boundary"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_selected_row"
    ] == "RN-ASSUMP-005-operator_domain_compatibility"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_packet_preparation_only_confirmed"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_discharges_operator_domain_compatibility"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_constructs_conservation_proof_object"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_constructs_conservation_witness"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_claims_source_admissibility"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_claims_bianchi_compatibility"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_derives_semiclassical_einstein_equation"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_closes_qft_gr_seam"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_selected_next_target"
    ] == RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_selection_count"
    ] == "1"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_result_review_token"
    ] == (
        "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
        "REDUCTION_PACKET_RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_"
        "REDUCTION_ATTEMPT_ONLY"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_prepares_reduction_analysis_only"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_packet_discharged"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_constructs_conservation_proof_object"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_constructs_conservation_witness"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_claims_source_admissibility"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_claims_bianchi_compatibility"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_closes_qft_gr_seam"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_target"
    ] == RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_executed"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_report"
    ] == (
        "formal/docs/release/"
        "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
        "REDUCTION_ATTEMPT_20260606_v0.json"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_surface"
    ] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizationOperatorDomainCompatibilityAssumptionReductionAttempt.lean"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_tool"
    ] == (
        "formal/python/tools/"
        "qft_gr_renormalization_operator_domain_compatibility_assumption_"
        "reduction_attempt_report.py"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_gate"
    ] == (
        "formal/python/tests/"
        "test_qft_gr_renormalization_operator_domain_compatibility_assumption_"
        "reduction_attempt_gate.py"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_token"
    ] == (
        "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
        "REDUCTION_ATTEMPT_EXECUTED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_classification"
    ] == (
        "qft_gr_renormalization_operator_domain_compatibility_assumption_"
        "reduced_pending_result_review"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_contract"
    ] == "RN-ASSUMP-005-operator_domain_compatibility_contract_v0"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_contract_status"
    ] == (
        "bounded_repo_local_operator_domain_compatibility_contract_pending_result_"
        "review_not_operator_domain_compatibility_discharge"
    )
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_selected_next_target"
    ] == RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_reviewed"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review_classification"
    ] == RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_CLASSIFICATION
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review_selected_row"
    ] == "RN-ASSUMP-005-operator_domain_compatibility"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review_no_next_row_available"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review_selected_next_target"
    ] == RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TARGET
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review_selection_count"
    ] == "1"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review_token"
    ] == RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOKEN
    assert current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_prepared"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_classification"
    ] == RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_CLASSIFICATION
    assert current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_report"
    ] == RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_REPORT
    assert current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_surface"
    ] == RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_SURFACE
    assert current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_tool"
    ] == RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TOOL
    assert current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_token"
    ] == RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TOKEN
    assert current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_selected_next_target"
    ] == RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_result_review_target"
    ] == RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_result_review_selected_next_target"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_selected_next_target"
    ] != current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_result_review_selected_next_target"
    ]
    assert current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_result_reviewed"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_assumption_reduction_closeout_packet_result_review_token"
    ] == RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TOKEN
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_prepared"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_classification"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_CLASSIFICATION
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_report"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_REPORT
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_surface"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_SURFACE
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_tool"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TOOL
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_token"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TOKEN
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_selected_next_target"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_result_review_target"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_result_review_selected_next_target"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_result_review_completed"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_result_review_pending"
    ] == "no"
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_result_review_classification"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_CLASSIFICATION
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_result_review_report"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_REPORT
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_result_review_surface"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_SURFACE
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_result_review_tool"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOOL
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_result_review_token"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOKEN
    assert current_active_workstream[
        "state_domain_assumption_reduction_packet_selected_next_target"
    ] != current_active_workstream[
        "state_domain_assumption_reduction_packet_result_review_selected_next_target"
    ]
    assert current_active_workstream["selected_bounded_state_domain_assumption_row"] == (
        STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_SELECTED_ROW
    )
    assert current_active_workstream[
        "selected_bounded_state_domain_assumption_row_status"
    ] == "required|missing|candidate_reducible"
    assert current_active_workstream[
        "selected_bounded_state_domain_assumption_target"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream["state_domain_object_assumption_row"] == (
        "SD-ASSUMP-001-state_domain_object"
    )
    assert current_active_workstream[
        "state_domain_object_assumption_packet_preparation_authorized"
    ] == "yes"
    assert current_active_workstream["state_domain_object_assumption_packet_target"] == (
        STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_TARGET
    )
    assert current_active_workstream["state_domain_object_assumption_packet_pending"] == "no"
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_prepared"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_classification"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_CLASSIFICATION
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_report"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_REPORT
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_surface"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_SURFACE
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_tool"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_TOOL
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_token"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_TOKEN
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_selected_next_target"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_result_review_target"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_result_review_classification"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_CLASSIFICATION
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_result_review_report"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_REPORT
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_result_review_surface"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_SURFACE
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_result_review_tool"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOOL
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_result_review_token"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOKEN
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_result_review_selected_next_target"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_packet_selected_next_target"
    ] != current_active_workstream[
        "state_domain_object_assumption_reduction_packet_result_review_selected_next_target"
    ]
    assert current_active_workstream[
        "state_domain_object_assumption_result_review_pending"
    ] == "no"
    assert current_active_workstream[
        "state_domain_object_assumption_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_object_assumption_result_review_completed"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_executed"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_report"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_REPORT
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_surface"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_SURFACE
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_tool"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_TOOL
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_token"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_TOKEN
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_classification"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_CLASSIFICATION
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_contract"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_contract_status"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT_STATUS
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_selected_next_target"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_result_review_target"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_result_review_pending"
    ] == "no"
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_result_review_completed"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_result_review_classification"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_CLASSIFICATION
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_result_review_report"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_REPORT
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_result_review_surface"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_SURFACE
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_result_review_tool"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOOL
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_result_review_token"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOKEN
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_result_review_selected_next_target"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_result_review_accepted_row"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_ACCEPTED_ROW
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_result_review_next_row"
    ] == STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_NEXT_ROW
    assert current_active_workstream[
        "state_domain_object_assumption_reduced_pending_result_review"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_object_assumption_obstruction_identified"
    ] == "no"
    assert current_active_workstream[
        "state_domain_object_assumption_inconclusive"
    ] == "no"
    assert current_active_workstream["accepted_state_domain_assumption_row"] == (
        STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_ACCEPTED_ROW
    )
    assert current_active_workstream["selected_state_domain_assumption_row"] == (
        STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_SELECTED_ROW
    )
    assert current_active_workstream[
        "selected_state_domain_assumption_row_status"
    ] == "required|missing|candidate_reducible"
    assert current_active_workstream["state_domain_object_definition_status"] == (
        "candidate_state_domain_object_selected_for_reduction_analysis_not_final_"
        "state_admissibility_or_conservation_discharge"
    )
    assert current_active_workstream["state_object_compatibility_condition"] == (
        "bounded_qft_state_domain_object_compatible_with_candidate_renormalized_"
        "stress_energy_expectation_without_source_admissibility_claim"
    )
    assert current_active_workstream["state_domain_object_assumption_discharged"] == "no"
    assert current_active_workstream[
        "state_domain_object_assumption_reduced_or_discharged_by_preparation"
    ] == "no"
    assert current_active_workstream["state_admissibility_discharged"] == "no"
    assert current_active_workstream["state_domain_object_assumption_reduced_by_review"] == (
        "no"
    )
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_executed"
    ] == "yes"
    assert current_active_workstream["bounded_reduction_attempt_authorized"] == "yes"
    assert current_active_workstream["bounded_reduction_attempt_executed"] == "yes"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_packet_preparation_authorized"
    ] == "yes"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_packet_target"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_packet_pending"
    ] == "no"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_prepared"
    ] == "yes"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_classification"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_CLASSIFICATION
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_report"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_REPORT
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_surface"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_SURFACE
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_tool"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_TOOL
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_token"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_TOKEN
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_selected_next_target"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_selected_next_target_kind"
    ] == (
        "qft_gr_state_admissibility_boundary_assumption_reduction_packet_result_review"
    )
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_result_review_target"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_result_review_pending"
    ] == "no"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_result_review_completed"
    ] == "yes"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_result_review_classification"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_CLASSIFICATION
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_result_review_report"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_REPORT
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_result_review_surface"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_SURFACE
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_result_review_tool"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOOL
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_result_review_token"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOKEN
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_result_review_selected_next_target"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_selected_next_target"
    ] != current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_result_review_selected_next_target"
    ]
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_executed"
    ] == "yes"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_id"
    ] == "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_v0"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_target"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_report"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_REPORT
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_surface"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_SURFACE
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_tool"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_TOOL
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_token"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_TOKEN
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_classification"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_CLASSIFICATION
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_classification"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_CLASSIFICATION
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_classification_count"
    ] == "1"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_selected_next_target"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_selected_next_target_kind"
    ] == "result_review"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_selected_next_authorization_token"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_TOKEN
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_review_target"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_review_pending"
    ] == "no"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_review_completed"
    ] == "yes"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_review_classification"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_CLASSIFICATION
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_review_surface"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_SURFACE
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_review_report"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_REPORT
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_review_tool"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOOL
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_review_token"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOKEN
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_review_selected_next_target"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_review_next_row"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_NEXT_ROW
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_result_review_accepted_row"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_ACCEPTED_ROW
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_prepared"
    ] == "yes"
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_target"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_TARGET
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_surface"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_SURFACE
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_report"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_REPORT
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_tool"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_TOOL
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_token"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_TOKEN
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_classification"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_CLASSIFICATION
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_selected_next_target"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_selected_next_target_kind"
    ] == "qft_gr_state_expectation_compatibility_assumption_reduction_packet_result_review"
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_selected_next_authorization_token"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_TOKEN
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_result_review_target"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_result_review_pending"
    ] == "no"
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_result_review_completed"
    ] == "yes"
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_result_review_surface"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_SURFACE
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_result_review_report"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_REPORT
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_result_review_tool"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOOL
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_result_review_token"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TOKEN
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_result_review_classification"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_CLASSIFICATION
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_packet_result_review_selected_next_target"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_TARGET
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_authorized"
    ] == "yes"
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_executed"
    ] == "yes"
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_classification"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_CLASSIFICATION
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_classification"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_CLASSIFICATION
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_contract_id"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_contract_status"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT_STATUS
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_contract_recorded"
    ] == "yes"
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_selected_next_target"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_review_pending"
    ] == "no"
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_review_accepted"
    ] == "yes"
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_review_completed"
    ] == "yes"
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_review_classification"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_CLASSIFICATION
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_review_surface"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_SURFACE
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_review_report"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_REPORT
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_review_tool"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOOL
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_review_token"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_TOKEN
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_review_accepted_row"
    ] == STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_ACCEPTED_ROW
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_review_no_next_row"
    ] == "yes"
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_review_row_inventory_exhausted"
    ] == "yes"
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_review_selected_next_target"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TARGET
    assert current_active_workstream[
        "state_expectation_compatibility_assumption_reduction_attempt_result_review_selected_next_target_kind"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TARGET_KIND
    assert current_active_workstream[
        "state_domain_assumption_reduction_closeout_packet_authorized"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_assumption_reduction_closeout_preparation_only"
    ] == "yes"
    assert current_active_workstream[
        "state_domain_assumption_reduction_closeout_target"
    ] == STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_TARGET
    assert (
        current_active_workstream[
            "state_domain_assumption_reduction_closeout_packet_selected_next_target"
        ]
        == STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_TARGET
    )
    assert (
        current_active_workstream[
            "state_domain_assumption_reduction_closeout_packet_prepared"
        ]
        == "yes"
    )
    assert (
        current_active_workstream[
            "state_domain_assumption_reduction_closeout_result_review_required"
        ]
        == "yes"
    )
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_contract_id"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_contract_status"
    ] == STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_CONTRACT_STATUS
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_attempt_contract_recorded"
    ] == "yes"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduced_pending_result_review"
    ] == "yes"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_obstruction_identified"
    ] == "no"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_inconclusive"
    ] == "no"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduced_by_attempt"
    ] == "yes"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_discharged"
    ] == "no"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_discharged_by_attempt"
    ] == "no"
    assert current_active_workstream[
        "state_admissibility_boundary_assumption_reduced_or_discharged_by_implication"
    ] == "no"
    assert current_active_workstream[
        "state_domain_object_assumption_reduction_attempt_result_review_selected_next_target"
    ] != current_active_workstream[
        "state_admissibility_boundary_assumption_reduction_packet_selected_next_target"
    ]
    assert current_active_workstream["state_admissibility_claimed"] == "no"
    assert current_active_workstream[
        "state_domain_assumption_reduction_analysis_prepared"
    ] == "yes"
    assert current_active_workstream["state_domain_assumptions_discharged"] == "no"
    assert current_active_workstream[
        "state_domain_assumptions_reduced_or_discharged_by_preparation"
    ] == "no"
    assert current_active_workstream[
        "state_admissibility_claimed_as_source_admissibility"
    ] == "no"
    assert current_active_workstream[
        "state_domain_candidate_reducible_assumption_count"
    ] == "3"
    assert current_active_workstream[
        "state_domain_not_reducible_in_current_lane_count"
    ] == "8"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduced_pending_result_review"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_obstruction_identified"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_inconclusive"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduced_by_attempt"
    ] == "yes"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_discharged_by_attempt"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduced_or_discharged_by_attempt"
    ] == "no"
    assert current_active_workstream[
        "renormalization_operator_domain_compatibility_assumption_reduced_or_discharged_by_implication"
    ] == "no"
    assert current_active_workstream[
        "operator_domain_compatibility_claimed_as_source_admissibility"
    ] == "no"
    assert current_active_workstream[
        "operator_domain_compatibility_claimed_as_bianchi_compatibility"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_contract"
    ] == "RN-ASSUMP-004-finiteness_regular_boundary_contract_v0"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduction_attempt_contract_status"
    ] == (
        "bounded_repo_local_finiteness_regular_boundary_contract_pending_result_"
        "review_not_finiteness_regular_boundary_discharge"
    )
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduced_pending_result_review"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_obstruction_identified"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_inconclusive"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduced_by_attempt"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_discharged_by_attempt"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduced_or_discharged_by_attempt"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_assumption_reduced_or_discharged_by_implication"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_claims_source_admissibility"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_claims_bianchi_compatibility"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_constructs_conservation_proof_object"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_constructs_conservation_witness"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_derives_semiclassical_einstein_equation"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_finiteness_closes_qft_gr_seam"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduced_pending_result_review"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_obstruction_identified"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_inconclusive"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduced_by_attempt"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_discharged_by_attempt"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduced_or_discharged_by_attempt"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduced_or_discharged_by_implication"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_claims_source_admissibility"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_claims_bianchi_compatibility"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_constructs_conservation_proof_object"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_constructs_conservation_witness"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_derives_semiclassical_einstein_equation"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_closes_qft_gr_seam"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_discharged_by_review"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduced_or_discharged_by_review"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduction_analysis_prepared"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_discharged"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_assumption_reduced_or_discharged_by_preparation"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_required_future_proof_object"
    ] == "renormalized_expectation_value_admitted_to_selected_operator_domain"
    assert current_active_workstream[
        "operator_domain_assumptions_reduced_for_this_lane"
    ] == "yes"
    assert current_active_workstream[
        "operator_domain_assumption_reduction_family_reduced"
    ] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduced_pending_result_review"
    ] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_obstruction_identified"
    ] == "no"
    assert current_active_workstream[
        "metric_connection_scope_assumption_inconclusive"
    ] == "no"
    assert current_active_workstream[
        "metric_connection_scope_assumption_reduced_by_attempt"
    ] == "yes"
    assert current_active_workstream[
        "metric_connection_scope_assumption_discharged_by_attempt"
    ] == "no"
    assert current_active_workstream[
        "metric_connection_scope_contract_id"
    ] == "OD-ASSUMP-006-metric_connection_scope_contract_v0"
    assert current_active_workstream[
        "authorized_metric_connection_scope_attempt_result_classification_count"
    ] == "3"
    assert current_active_workstream[
        "authorized_metric_connection_scope_attempt_result_classifications"
    ] == (
        "qft_gr_metric_connection_scope_assumption_reduced_pending_result_review|"
        "qft_gr_metric_connection_scope_assumption_obstruction_identified_requires_refinement|"
        "qft_gr_metric_connection_scope_assumption_inconclusive_requires_assumption_reduction"
    )
    assert current_active_workstream[
        "metric_connection_scope_claims_bianchi_compatibility"
    ] == "no"
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduced_by_attempt"
    ] == "yes"
    assert current_active_workstream[
        "conservation_form_scope_assumption_reduced_pending_result_review"
    ] == "yes"
    assert current_active_workstream[
        "conservation_form_scope_assumption_obstruction_identified"
    ] == "no"
    assert current_active_workstream[
        "conservation_form_scope_assumption_inconclusive"
    ] == "no"
    assert current_active_workstream[
        "authorized_conservation_form_scope_attempt_result_classification_count"
    ] == "3"
    assert current_active_workstream[
        "authorized_conservation_form_scope_attempt_result_classifications"
    ] == (
        "qft_gr_conservation_form_scope_assumption_reduced_pending_result_review|"
        "qft_gr_conservation_form_scope_assumption_obstruction_identified_requires_refinement|"
        "qft_gr_conservation_form_scope_assumption_inconclusive_requires_assumption_reduction"
    )
    assert current_active_workstream[
        "conservation_form_scope_selected_operator_domain_assumption_row"
    ] == "OD-ASSUMP-005-conservation_form_scope"
    assert current_active_workstream["conservation_form_scope_options"] == (
        "weak|strong|distributional"
    )
    assert current_active_workstream[
        "conservation_form_scope_selected_bounded_conservation_form"
    ] == "weak_operator_domain_covariant_divergence_zero_form"
    assert current_active_workstream[
        "conservation_form_scope_required_future_proof_object"
    ] == "bounded_weak_operator_domain_conservation_form_selected_for_future_proof_object"
    assert current_active_workstream["conservation_form_scope_conservation_proved"] == "no"
    assert (
        current_active_workstream[
            "conservation_form_scope_conservation_proof_object_constructed"
        ]
        == "no"
    )
    assert (
        current_active_workstream[
            "conservation_form_scope_conservation_witness_constructed"
        ]
        == "no"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduced_by_attempt"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduced_pending_result_review"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_obstruction_identified"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_inconclusive"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_reduced_by_review"
    ] == "no"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_analysis_accepted_by_result_review"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_packet_accepted_by_result_review"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_prior_rows001_002_003_remain_accepted"
    ] == "yes"
    assert current_active_workstream["renormalized_expectation_object"] == (
        "candidate_renormalized_qft_stress_energy_expectation_object"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_link_operator_domain_link_condition"
    ] == (
        "renormalized_expectation_value_admitted_to_operator_domain"
    )
    assert current_active_workstream[
        "renormalized_expectation_domain_link_packet_preparation_only"
    ] == "yes"
    assert current_active_workstream[
        "renormalized_expectation_domain_link_assumption_discharged"
    ] == "no"
    assert current_active_workstream[
        "renormalization_compatibility_with_conservation_claimed"
    ] == "no"
    assert (
        current_active_workstream[
            "candidate_source_domain_membership_assumption_discharged"
        ]
        == "no"
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
        interaction_active_workstream[
            "authorized_next_strict_target"
        ],
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
        f'  "{PREVIOUS_LIVE_TARGET}"'
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
