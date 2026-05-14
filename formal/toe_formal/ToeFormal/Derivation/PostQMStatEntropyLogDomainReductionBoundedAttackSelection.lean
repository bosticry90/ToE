/-
ToeFormal/Derivation/PostQMStatEntropyLogDomainReductionBoundedAttackSelection.lean

Selection packet after the QM-STAT entropy log-domain zero-handling reduction
result review.

Scope:
- consume `select_next_post_qm_stat_entropy_log_domain_reduction_bounded_attack`
- consume `QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_CONSUMED_LEAN_BACKED`
- preserve the log-domain reduction as Lean-backed local convention authority only
- preserve that the target STAT entropy semantics theorem gap remains supplied-only
- preserve that seven supporting assumptions remain active
- select exactly one next bounded target
- select `prepare_qm_stat_entropy_assumption_reduction_candidate_selection`
- recommend `normalization_or_probability_mass_condition_required` as the
  next likely local candidate, without executing that candidate selection or
  any reduction
- do not attempt to discharge any entropy-semantics theorem or assumption here
- do not infer QM-STAT pillar completion, seam closure, Phase 2 readiness,
  empirical adequacy, canonical ToE status, master-action promotion,
  QFT-GR source-map closure, selected-target execution, or governance-manifest
  enrollment
- do not enroll this focused packet gate in the governance manifest
-/

import ToeFormal.Derivation.QMStatEntropyLogDomainZeroHandlingReductionResultReview

namespace ToeFormal
namespace Derivation
namespace PostQMStatEntropyLogDomainReductionBoundedAttackSelection

open CrossPillarClosureFrontier
open CrossPillarDerivationProtocol
open QMStatEntropyLogDomainZeroHandlingReductionResultReview

set_option autoImplicit false
set_option linter.style.longLine false

/-- Surface id for the post-log-domain-reduction selector. -/
def postQMStatEntropyLogDomainReductionBoundedAttackSelectionSurfaceId :
    String :=
  "post_qm_stat_entropy_log_domain_reduction_bounded_attack_selection_v0"

/-- Live target consumed by this selector packet. -/
def postQMStatEntropyLogDomainReductionBoundedAttackSelectionConsumedTargetId :
    String :=
  selectedPostQMStatEntropyLogDomainReductionBoundedAttackTargetId

/-- Result-review token consumed from the log-domain reduction review. -/
def postQMStatEntropyLogDomainReductionBoundedAttackSelectionConsumedReviewTokenId :
    String :=
  qmStatEntropyLogDomainZeroHandlingReductionResultReviewTokenId

/-- Output token emitted by this selector packet. -/
def postQMStatEntropyLogDomainReductionBoundedAttackSelectionOutputTokenId :
    String :=
  "POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_NEXT_ATTACK_SELECTED"

/-- Canonical release report for this selector packet. -/
def postQMStatEntropyLogDomainReductionBoundedAttackSelectionReportPath :
    String :=
  "formal/docs/release/POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_BOUNDED_ATTACK_SELECTION_20260510_v0.json"

/-- Focused validation target for this selector packet. -/
def postQMStatEntropyLogDomainReductionBoundedAttackSelectionValidationTarget :
    String :=
  "python -m pytest \
  formal/python/tests/test_post_qm_stat_entropy_log_domain_reduction_bounded_attack_selection_gate.py -q"

/-- Selected next target: run another bounded assumption candidate-selection pass. -/
def selectedPostQMStatEntropyLogDomainReductionNextTargetV0 : String :=
  "prepare_qm_stat_entropy_assumption_reduction_candidate_selection"

/-- Recommended next assumption candidate for that later packet. -/
def recommendedPostQMStatEntropyLogDomainReductionNextCandidateV0 :
    String :=
  "normalization_or_probability_mass_condition_required"

/-- Alternative target not selected here: return to the full-pillar selector. -/
def alternatePostQMStatEntropyLogDomainReductionFullPillarReturnTargetV0 :
    String :=
  "return_to_full_pillar_target_map_next_lane_selection"

/-- Candidate targets inspected by this selector packet. -/
def postQMStatEntropyLogDomainReductionCandidateNextTargetsV0 :
    List String :=
  [ selectedPostQMStatEntropyLogDomainReductionNextTargetV0
  , alternatePostQMStatEntropyLogDomainReductionFullPillarReturnTargetV0
  ]

/-- Selection decisions available after the log-domain reduction review. -/
inductive PostQMStatEntropyLogDomainReductionBoundedAttackSelectionDecision where
  | prepareQMStatEntropyAssumptionReductionCandidateSelection
  | returnToFullPillarTargetMapNextLaneSelection
  | inferLeanBackedEntropySemanticsDischarge
  | inferQMSTATCompletion
deriving DecidableEq, Repr

/-- Stable string rendering for post-log-domain selector decisions. -/
def postQMStatEntropyLogDomainReductionBoundedAttackSelectionDecisionId :
    PostQMStatEntropyLogDomainReductionBoundedAttackSelectionDecision ->
      String
  | .prepareQMStatEntropyAssumptionReductionCandidateSelection =>
      "prepare_qm_stat_entropy_assumption_reduction_candidate_selection"
  | .returnToFullPillarTargetMapNextLaneSelection =>
      "return_to_full_pillar_target_map_next_lane_selection"
  | .inferLeanBackedEntropySemanticsDischarge =>
      "infer_lean_backed_entropy_semantics_discharge"
  | .inferQMSTATCompletion => "infer_qm_stat_completion"

/-- Selection output. This authorizes selection only, not target execution. -/
structure PostQMStatEntropyLogDomainReductionBoundedAttackSelectionStatus where
  reduction_result_review_consumed : Prop
  reduction_result_review_consumed_evidence :
    reduction_result_review_consumed
  local_convention_reduction_only_preserved : Prop
  local_convention_reduction_only_preserved_evidence :
    local_convention_reduction_only_preserved
  local_convention_lean_backed_preserved : Prop
  local_convention_lean_backed_preserved_evidence :
    local_convention_lean_backed_preserved
  remaining_supporting_assumptions_active : Prop
  remaining_supporting_assumptions_active_evidence :
    remaining_supporting_assumptions_active
  remaining_assumption_class_ids : List String
  remaining_assumption_class_count : Nat
  exactly_one_next_bounded_target_selected : Prop
  exactly_one_next_bounded_target_selected_evidence :
    exactly_one_next_bounded_target_selected
  selected_decision :
    PostQMStatEntropyLogDomainReductionBoundedAttackSelectionDecision
  selected_next_bounded_target : String
  recommended_next_candidate : String
  output_token : String
  authorized_effect : String
  selected_target_count : Nat
  candidate_next_targets : List String
  selection_reason : String
  selection_executes_target : Prop
  selection_does_not_execute_target : Not selection_executes_target
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
  consumed_target : String
  consumed_review_token : String
  source_review_surface_id : String
  source_review_report_path : String
  source_reduction_surface_id : String
  surface_id : String
  report_path : String
  selected_validation_target : String
  status : DerivationStatus

/--
Current selector packet: after one local assumption has been reduced, select a
second bounded candidate-selection pass while preserving the supplied-only
entropy-semantics theorem boundary.
-/
def postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusV0 :
    PostQMStatEntropyLogDomainReductionBoundedAttackSelectionStatus where
  reduction_result_review_consumed :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.local_convention_lean_backed
  reduction_result_review_consumed_evidence :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.local_convention_lean_backed_evidence
  local_convention_reduction_only_preserved :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.local_convention_reduction_only
  local_convention_reduction_only_preserved_evidence :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.local_convention_reduction_only_evidence
  local_convention_lean_backed_preserved :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.local_convention_lean_backed
  local_convention_lean_backed_preserved_evidence :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.local_convention_lean_backed_evidence
  remaining_supporting_assumptions_active :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.remaining_supporting_assumptions_active
  remaining_supporting_assumptions_active_evidence :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.remaining_supporting_assumptions_active_evidence
  remaining_assumption_class_ids :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.remaining_assumption_class_ids
  remaining_assumption_class_count :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.remaining_assumption_class_count
  exactly_one_next_bounded_target_selected := True
  exactly_one_next_bounded_target_selected_evidence := True.intro
  selected_decision :=
    .prepareQMStatEntropyAssumptionReductionCandidateSelection
  selected_next_bounded_target :=
    selectedPostQMStatEntropyLogDomainReductionNextTargetV0
  recommended_next_candidate :=
    recommendedPostQMStatEntropyLogDomainReductionNextCandidateV0
  output_token :=
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionOutputTokenId
  authorized_effect := "SELECT_EXACTLY_ONE_NEXT_BOUNDED_TARGET"
  selected_target_count := 1
  candidate_next_targets :=
    postQMStatEntropyLogDomainReductionCandidateNextTargetsV0
  selection_reason :=
    "The log-domain zero-handling convention is now Lean-backed locally, but \
    seven supporting assumptions remain active. A second bounded \
    candidate-selection pass can identify the next local reduction candidate \
    without widening entropy-semantics theorem authority."
  selection_executes_target := False
  selection_does_not_execute_target := by
    intro h
    exact h
  target_entropy_semantics_lean_backed :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.target_entropy_semantics_lean_backed
  target_entropy_semantics_not_lean_backed :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.target_entropy_semantics_not_lean_backed
  target_entropy_semantics_supplied_only :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.target_entropy_semantics_supplied_only
  target_entropy_semantics_supplied_only_evidence :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.target_entropy_semantics_supplied_only_evidence
  entropy_semantics_theorem_discharged :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.entropy_semantics_theorem_discharged
  entropy_semantics_theorem_not_discharged :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.entropy_semantics_theorem_not_discharged
  qm_stat_pillar_completion_inferred :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.qm_stat_pillar_completion_inferred
  qm_stat_pillar_completion_not_inferred :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.qm_stat_pillar_completion_not_inferred
  seam_closure_inferred :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.seam_closure_inferred
  seam_closure_not_inferred :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.seam_closure_not_inferred
  phase2_readiness_claim :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.phase2_readiness_claim
  phase2_readiness_not_claimed :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.phase2_readiness_not_claimed
  empirical_adequacy_claim :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.empirical_adequacy_claim
  empirical_adequacy_not_claimed :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.empirical_adequacy_not_claimed
  canonical_toe_claim :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.canonical_toe_claim
  canonical_toe_not_claimed :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.canonical_toe_not_claimed
  master_action_promoted :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.master_action_promoted
  master_action_not_promoted :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.master_action_not_promoted
  qft_gr_source_map_closure_authorized :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.qft_gr_source_map_closure_authorized
  qft_gr_source_map_closure_not_authorized :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.qft_gr_source_map_closure_not_authorized
  governance_manifest_enrollment_authorized :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.governance_manifest_enrollment_authorized
  governance_manifest_enrollment_not_authorized :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.governance_manifest_enrollment_not_authorized
  consumed_target :=
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionConsumedTargetId
  consumed_review_token :=
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionConsumedReviewTokenId
  source_review_surface_id :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewSurfaceId
  source_review_report_path :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewReportPath
  source_reduction_surface_id :=
    qmStatEntropyLogDomainZeroHandlingReductionResultReviewStatusReadoutV0
      |>.source_reduction_surface_id
  surface_id :=
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionSurfaceId
  report_path :=
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionReportPath
  selected_validation_target :=
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionValidationTarget
  status := .retained

/-- Public readout for the post-log-domain selector. -/
def postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0 :
    PostQMStatEntropyLogDomainReductionBoundedAttackSelectionStatus :=
  postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusV0

theorem post_qm_stat_entropy_log_domain_reduction_selection_consumes_live_target_v0 :
    (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.consumed_target) =
      "select_next_post_qm_stat_entropy_log_domain_reduction_bounded_attack" := by
  rfl

theorem post_qm_stat_entropy_log_domain_reduction_selection_consumes_review_token_v0 :
    (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.consumed_review_token) =
      "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_RESULT_REVIEW_CONSUMED_LEAN_BACKED" := by
  rfl

theorem post_qm_stat_entropy_log_domain_reduction_selection_review_consumed_v0 :
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.reduction_result_review_consumed := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.reduction_result_review_consumed_evidence

theorem post_qm_stat_entropy_log_domain_reduction_selection_local_only_v0 :
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.local_convention_reduction_only_preserved := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.local_convention_reduction_only_preserved_evidence

theorem post_qm_stat_entropy_log_domain_reduction_selection_remaining_count_v0 :
    (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.remaining_assumption_class_count) =
      7 := by
  rfl

theorem post_qm_stat_entropy_log_domain_reduction_selection_remaining_active_v0 :
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.remaining_supporting_assumptions_active := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.remaining_supporting_assumptions_active_evidence

theorem post_qm_stat_entropy_log_domain_reduction_selection_exactly_one_target_v0 :
    (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.selected_target_count) =
      1 := by
  rfl

theorem post_qm_stat_entropy_log_domain_reduction_selection_output_token_v0 :
    (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.output_token) =
      "POST_QM_STAT_ENTROPY_LOG_DOMAIN_REDUCTION_NEXT_ATTACK_SELECTED" := by
  rfl

theorem post_qm_stat_entropy_log_domain_reduction_selection_decision_v0 :
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionDecisionId
      (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
        |>.selected_decision) =
      "prepare_qm_stat_entropy_assumption_reduction_candidate_selection" := by
  rfl

theorem post_qm_stat_entropy_log_domain_reduction_selection_selected_target_v0 :
    (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.selected_next_bounded_target) =
      "prepare_qm_stat_entropy_assumption_reduction_candidate_selection" := by
  rfl

theorem post_qm_stat_entropy_log_domain_reduction_selection_recommended_candidate_v0 :
    (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.recommended_next_candidate) =
      "normalization_or_probability_mass_condition_required" := by
  rfl

theorem post_qm_stat_entropy_log_domain_reduction_selection_candidate_count_v0 :
    (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.candidate_next_targets.length) =
      2 := by
  rfl

theorem post_qm_stat_entropy_log_domain_reduction_selection_frontier_target_v0 :
    Option.map (fun entry => entry.next_strict_slice)
      (crossPillarFrontierEntryByRow? .masterAction) =
      some "prepare_qm_stat_entropy_assumption_reduction_candidate_selection" := by
  decide

theorem post_qm_stat_entropy_log_domain_reduction_selection_does_not_execute_target_v0 :
    Not
      (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
        |>.selection_executes_target) := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.selection_does_not_execute_target

theorem post_qm_stat_entropy_log_domain_reduction_selection_no_lean_backed_entropy_semantics_v0 :
    Not
      (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
        |>.target_entropy_semantics_lean_backed) := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.target_entropy_semantics_not_lean_backed

theorem post_qm_stat_entropy_log_domain_reduction_selection_supplied_only_preserved_v0 :
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.target_entropy_semantics_supplied_only := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.target_entropy_semantics_supplied_only_evidence

theorem post_qm_stat_entropy_log_domain_reduction_selection_no_entropy_theorem_discharge_v0 :
    Not
      (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
        |>.entropy_semantics_theorem_discharged) := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.entropy_semantics_theorem_not_discharged

theorem post_qm_stat_entropy_log_domain_reduction_selection_no_qm_stat_completion_v0 :
    Not
      (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
        |>.qm_stat_pillar_completion_inferred) := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.qm_stat_pillar_completion_not_inferred

theorem post_qm_stat_entropy_log_domain_reduction_selection_no_seam_closure_v0 :
    Not
      (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
        |>.seam_closure_inferred) := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.seam_closure_not_inferred

theorem post_qm_stat_entropy_log_domain_reduction_selection_no_phase2_readiness_v0 :
    Not
      (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
        |>.phase2_readiness_claim) := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.phase2_readiness_not_claimed

theorem post_qm_stat_entropy_log_domain_reduction_selection_no_empirical_adequacy_v0 :
    Not
      (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
        |>.empirical_adequacy_claim) := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.empirical_adequacy_not_claimed

theorem post_qm_stat_entropy_log_domain_reduction_selection_no_canonical_toe_claim_v0 :
    Not
      (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
        |>.canonical_toe_claim) := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.canonical_toe_not_claimed

theorem post_qm_stat_entropy_log_domain_reduction_selection_master_action_not_promoted_v0 :
    Not
      (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
        |>.master_action_promoted) := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.master_action_not_promoted

theorem post_qm_stat_entropy_log_domain_reduction_selection_qft_gr_not_authorized_v0 :
    Not
      (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
        |>.qft_gr_source_map_closure_authorized) := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.qft_gr_source_map_closure_not_authorized

theorem post_qm_stat_entropy_log_domain_reduction_selection_manifest_not_enrolled_v0 :
    Not
      (postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
        |>.governance_manifest_enrollment_authorized) := by
  exact
    postQMStatEntropyLogDomainReductionBoundedAttackSelectionStatusReadoutV0
      |>.governance_manifest_enrollment_not_authorized

end PostQMStatEntropyLogDomainReductionBoundedAttackSelection
end Derivation
end ToeFormal
