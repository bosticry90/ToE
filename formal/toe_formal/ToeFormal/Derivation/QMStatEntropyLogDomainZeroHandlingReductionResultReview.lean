/-
ToeFormal/Derivation/QMStatEntropyLogDomainZeroHandlingReductionResultReview.lean

Result-review packet for the QM-STAT entropy log-domain zero-handling
local convention reduction.

Scope:
- consume `review_qm_stat_entropy_log_domain_zero_handling_reduction_result`
- consume `QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_ASSUMPTION_REDUCED_LEAN_BACKED`
- accept only the Lean-backed local convention reduction
- keep the broader target STAT entropy semantics theorem gap supplied-only
- keep the remaining seven supporting assumptions active
- select `select_next_post_qm_stat_entropy_log_domain_reduction_bounded_attack`
- do not infer entropy-semantics theorem discharge, QM-STAT pillar completion,
  seam closure, Phase 2 readiness, empirical adequacy, canonical ToE status,
  master-action promotion, QFT-GR source-map closure, or governance-manifest
  enrollment
- do not enroll this focused review gate in the governance manifest
-/

import ToeFormal.Derivation.QMStatEntropyLogDomainZeroHandlingReduction

namespace ToeFormal
namespace Derivation
namespace QMStatEntropyLogDomainZeroHandlingReductionResultReview

open CrossPillarClosureFrontier
open CrossPillarDerivationProtocol
open QMStatEntropySemanticsSupportingAssumptionMap
open QMStatEntropyLogDomainZeroHandlingReduction

set_option autoImplicit false
set_option linter.style.longLine false

/-- Surface id for the QM-STAT log-domain zero-handling reduction review. -/
def qmStatEntropyLogDomainZeroHandlingReductionResultReviewSurfaceId :
    String :=
  "qm_stat_entropy_log_domain_zero_handling_reduction_result_review_v0"

/-- Live target consumed by this result-review packet. -/
def qmStatEntropyLogDomainZeroHandlingReductionResultReviewConsumedTargetId :
    String :=
  selectedQMStatEntropyLogDomainZeroHandlingReductionReviewTargetId

/-- Reduction result token consumed by this result-review packet. -/
def qmStatEntropyLogDomainZeroHandlingReductionResultReviewConsumedTokenId :
    String :=
  qmStatEntropyLogDomainZeroHandlingReducedLeanBackedTokenId

/-- Review token emitted by this result-review packet. -/
def qmStatEntropyLogDomainZeroHandlingReductionResultReviewTokenId : String :=
  "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_CONSUMED_LEAN_BACKED"

/-- Next strict target after reviewing the local convention reduction. -/
def selectedPostQMStatEntropyLogDomainReductionBoundedAttackTargetId :
    String :=
  "select_next_post_qm_stat_entropy_log_domain_reduction_bounded_attack"

/-- Canonical release report for this packet. -/
def qmStatEntropyLogDomainZeroHandlingReductionResultReviewReportPath :
    String :=
  "formal/docs/release/QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_20260510_v0.json"

/-- Focused validation target for this packet. -/
def qmStatEntropyLogDomainZeroHandlingReductionResultReviewValidationTarget :
    String :=
  "python -m pytest \
  formal/python/tests/test_qm_stat_entropy_log_domain_zero_handling_reduction_result_review_gate.py -q"

/-- Supporting assumption classes not reduced by the log-domain packet. -/
def remainingQMStatEntropySupportingAssumptionClassesAfterLogDomainReductionV0 :
    List QMStatEntropySemanticsSupportingAssumptionClass :=
  [ .targetEntropyFunctionalDefinitionRequired
  , .statisticalStateDomainSemanticsRequired
  , .normalizationOrProbabilityMassConditionRequired
  , .finiteSupportOrSummabilityConditionRequired
  , .transportAlignmentRelationRequired
  , .residualZeroBridgeConditionRequired
  , .comparisonTargetSemanticsRequired
  ]

/-- Stable ids for the remaining supporting assumptions. -/
def remainingQMStatEntropySupportingAssumptionClassIdsAfterLogDomainReductionV0 :
    List String :=
  [ "target_entropy_functional_definition_required"
  , "statistical_state_domain_semantics_required"
  , "normalization_or_probability_mass_condition_required"
  , "finite_support_or_summability_condition_required"
  , "transport_alignment_relation_required"
  , "residual_zero_bridge_condition_required"
  , "comparison_target_semantics_required"
  ]

/-- Status readout for the result-review packet. -/
structure QMStatEntropyLogDomainZeroHandlingReductionResultReviewStatus where
  reduction_result_consumed : Prop
  reduction_result_consumed_evidence : reduction_result_consumed
  reduced_assumption_class_id : String
  reduced_assumption_authority : String
  local_convention_reduction_only : Prop
  local_convention_reduction_only_evidence :
    local_convention_reduction_only
  local_convention_lean_backed : Prop
  local_convention_lean_backed_evidence : local_convention_lean_backed
  remaining_assumption_class_ids : List String
  remaining_assumption_class_count : Nat
  remaining_supporting_assumptions_active : Prop
  remaining_supporting_assumptions_active_evidence :
    remaining_supporting_assumptions_active
  consumed_target : String
  consumed_reduction_token : String
  review_token : String
  selected_next_target : String
  source_reduction_surface_id : String
  source_reduction_report_path : String
  surface_id : String
  report_path : String
  validation_target : String
  target_entropy_semantics_lean_backed : Prop
  target_entropy_semantics_not_lean_backed :
    Not target_entropy_semantics_lean_backed
  target_entropy_semantics_supplied_only : Prop
  target_entropy_semantics_supplied_only_evidence :
    target_entropy_semantics_supplied_only
  entropy_semantics_theorem_discharged : Prop
  entropy_semantics_theorem_not_discharged :
    Not entropy_semantics_theorem_discharged
  qm_stat_pillar_completion_inferred : Prop
  qm_stat_pillar_completion_not_inferred :
    Not qm_stat_pillar_completion_inferred
  seam_closure_inferred : Prop
  seam_closure_not_inferred : Not seam_closure_inferred
  phase2_readiness_claim : Prop
  phase2_readiness_not_claimed : Not phase2_readiness_claim
  empirical_adequacy_claim : Prop
  empirical_adequacy_not_claimed : Not empirical_adequacy_claim
  canonical_toe_claim : Prop
  canonical_toe_not_claimed : Not canonical_toe_claim
  master_action_promoted : Prop
  master_action_not_promoted : Not master_action_promoted
  qft_gr_source_map_closure_authorized : Prop
  qft_gr_source_map_closure_not_authorized :
    Not qft_gr_source_map_closure_authorized
  governance_manifest_enrollment_authorized : Prop
  governance_manifest_enrollment_not_authorized :
    Not governance_manifest_enrollment_authorized
  status : DerivationStatus

/--
Current packet: consume the local-convention reduction as review-only evidence
and rotate to the post-reduction selector without widening theorem authority.
-/
def qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusV0 :
    QMStatEntropyLogDomainZeroHandlingReductionResultReviewStatus where
  reduction_result_consumed :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.selected_assumption_reduced_to_lean_backed_local_convention
  reduction_result_consumed_evidence :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.selected_assumption_reduced_to_lean_backed_local_convention_evidence
  reduced_assumption_class_id :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.addressed_assumption_class_id
  reduced_assumption_authority :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.assumption_authority_after
  local_convention_reduction_only := True
  local_convention_reduction_only_evidence := True.intro
  local_convention_lean_backed :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.local_convention_structure_defined
  local_convention_lean_backed_evidence :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.local_convention_structure_defined_evidence
  remaining_assumption_class_ids :=
    remainingQMStatEntropySupportingAssumptionClassIdsAfterLogDomainReductionV0
  remaining_assumption_class_count :=
    remainingQMStatEntropySupportingAssumptionClassIdsAfterLogDomainReductionV0.length
  remaining_supporting_assumptions_active := True
  remaining_supporting_assumptions_active_evidence := True.intro
  consumed_target :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewConsumedTargetId
  consumed_reduction_token :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewConsumedTokenId
  review_token :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewTokenId
  selected_next_target :=
    selectedPostQMStatEntropyLogDomainReductionBoundedAttackTargetId
  source_reduction_surface_id :=
    qmStatEntropyLogDomainZeroHandlingReductionSurfaceId
  source_reduction_report_path :=
    qmStatEntropyLogDomainZeroHandlingReductionReportPath
  surface_id :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewSurfaceId
  report_path :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewReportPath
  validation_target :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewValidationTarget
  target_entropy_semantics_lean_backed :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.target_entropy_semantics_lean_backed
  target_entropy_semantics_not_lean_backed :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.target_entropy_semantics_not_lean_backed
  target_entropy_semantics_supplied_only :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.target_entropy_semantics_supplied_only
  target_entropy_semantics_supplied_only_evidence :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.target_entropy_semantics_supplied_only_evidence
  entropy_semantics_theorem_discharged :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.entropy_semantics_theorem_discharged
  entropy_semantics_theorem_not_discharged :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.entropy_semantics_theorem_not_discharged
  qm_stat_pillar_completion_inferred :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.qm_stat_pillar_completion_inferred
  qm_stat_pillar_completion_not_inferred :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.qm_stat_pillar_completion_not_inferred
  seam_closure_inferred :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.seam_closure_inferred
  seam_closure_not_inferred :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.seam_closure_not_inferred
  phase2_readiness_claim :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.phase2_readiness_claim
  phase2_readiness_not_claimed :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.phase2_readiness_not_claimed
  empirical_adequacy_claim :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.empirical_adequacy_claim
  empirical_adequacy_not_claimed :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.empirical_adequacy_not_claimed
  canonical_toe_claim :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.canonical_toe_claim
  canonical_toe_not_claimed :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.canonical_toe_not_claimed
  master_action_promoted :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.master_action_promoted
  master_action_not_promoted :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.master_action_not_promoted
  qft_gr_source_map_closure_authorized :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.qft_gr_source_map_closure_authorized
  qft_gr_source_map_closure_not_authorized :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.qft_gr_source_map_closure_not_authorized
  governance_manifest_enrollment_authorized :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.governance_manifest_enrollment_authorized
  governance_manifest_enrollment_not_authorized :=
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.governance_manifest_enrollment_not_authorized
  status := .retained

/-- Public readout for the result-review packet. -/
def qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0 :
    QMStatEntropyLogDomainZeroHandlingReductionResultReviewStatus :=
  qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusV0

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_consumes_live_target_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.consumed_target) =
      "review_qm_stat_entropy_log_domain_zero_handling_reduction_result" := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_consumes_reduction_token_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.consumed_reduction_token) =
      "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_ASSUMPTION_REDUCED_LEAN_BACKED" := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_token_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.review_token) =
      "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_CONSUMED_LEAN_BACKED" := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_next_target_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.selected_next_target) =
      "select_next_post_qm_stat_entropy_log_domain_reduction_bounded_attack" := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_reduced_assumption_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.reduced_assumption_class_id) =
      "log_domain_zero_handling_convention_required" := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_remaining_count_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.remaining_assumption_class_count) =
      7 := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_remaining_active_v0 :
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.remaining_supporting_assumptions_active := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.remaining_supporting_assumptions_active_evidence

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_local_only_v0 :
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.local_convention_reduction_only := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.local_convention_reduction_only_evidence

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_frontier_target_v0 :
    Option.map (fun entry => entry.next_strict_slice)
      (crossPillarFrontierEntryByRow? .masterAction) =
      some masterActionFrontierNextStrictTargetV0 := by
  decide

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_target_entropy_lean_backed_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
        |>.target_entropy_semantics_lean_backed) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.target_entropy_semantics_not_lean_backed

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_supplied_only_preserved_v0 :
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.target_entropy_semantics_supplied_only := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.target_entropy_semantics_supplied_only_evidence

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_entropy_theorem_discharge_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
        |>.entropy_semantics_theorem_discharged) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.entropy_semantics_theorem_not_discharged

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_qm_stat_completion_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
        |>.qm_stat_pillar_completion_inferred) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.qm_stat_pillar_completion_not_inferred

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_seam_closure_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
        |>.seam_closure_inferred) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.seam_closure_not_inferred

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_phase2_readiness_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
        |>.phase2_readiness_claim) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.phase2_readiness_not_claimed

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_empirical_adequacy_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
        |>.empirical_adequacy_claim) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.empirical_adequacy_not_claimed

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_no_canonical_toe_claim_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
        |>.canonical_toe_claim) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.canonical_toe_not_claimed

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_master_action_not_promoted_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
        |>.master_action_promoted) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.master_action_not_promoted

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_qft_gr_not_authorized_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
        |>.qft_gr_source_map_closure_authorized) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.qft_gr_source_map_closure_not_authorized

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_review_manifest_not_enrolled_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
        |>.governance_manifest_enrollment_authorized) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.governance_manifest_enrollment_not_authorized

end QMStatEntropyLogDomainZeroHandlingReductionResultReview
end Derivation
end ToeFormal
