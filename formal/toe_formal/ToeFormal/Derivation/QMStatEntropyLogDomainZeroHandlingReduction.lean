/-
ToeFormal/Derivation/QMStatEntropyLogDomainZeroHandlingReduction.lean

Bounded reduction packet for the selected QM-STAT entropy assumption:
`log_domain_zero_handling_convention_required`.

Scope:
- consume `prepare_selected_qm_stat_entropy_assumption_reduction_bounded_attack`
- consume `QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTED`
- address only `log_domain_zero_handling_convention_required`
- define a Lean-backed local convention structure for log-domain and
  zero-probability handling
- reduce the selected assumption to that local convention structure
- keep target STAT entropy semantics theorem authority supplied-only
- do not infer entropy-semantics theorem discharge, QM-STAT pillar completion,
  seam closure, Phase 2 readiness, empirical adequacy, canonical ToE status,
  master-action promotion, QFT-GR source-map closure, or governance-manifest
  enrollment
- do not enroll this focused packet gate in the governance manifest
- remain a local convention reduction, not a target entropy theorem discharge
-/

import ToeFormal.Derivation.QMStatEntropyAssumptionReductionCandidateSelection

namespace ToeFormal
namespace Derivation
namespace QMStatEntropyLogDomainZeroHandlingReduction

open CrossPillarClosureFrontier
open CrossPillarDerivationProtocol
open QMStatEntropySemanticsSupportingAssumptionMap
open QMStatEntropyAssumptionReductionCandidateSelection

set_option autoImplicit false
set_option linter.style.longLine false

/-- Surface id for the QM-STAT log-domain zero-handling reduction packet. -/
def qmStatEntropyLogDomainZeroHandlingReductionSurfaceId : String :=
  "qm_stat_entropy_log_domain_zero_handling_reduction_v0"

/-- Live target consumed by this bounded reduction packet. -/
def qmStatEntropyLogDomainZeroHandlingReductionConsumedTargetId : String :=
  selectedQMStatEntropyAssumptionReductionBoundedAttackTargetId

/-- Candidate-selection token consumed by this bounded reduction packet. -/
def qmStatEntropyLogDomainZeroHandlingReductionConsumedCandidateTokenId :
    String :=
  qmStatEntropyAssumptionReductionCandidateSelectionResultTokenId

/-- Successful local-convention reduction token. -/
def qmStatEntropyLogDomainZeroHandlingReducedLeanBackedTokenId : String :=
  "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_ASSUMPTION_REDUCED_LEAN_BACKED"

/-- Honest fallback token if the local convention could not be reduced. -/
def qmStatEntropyLogDomainZeroHandlingRetainedSuppliedOnlyTokenId : String :=
  "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_ASSUMPTION_RETAINED_SUPPLIED_ONLY"

/-- Honest fallback token if the local convention were refined but not discharged. -/
def qmStatEntropyLogDomainZeroHandlingRefinedNotDischargedTokenId : String :=
  "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_ASSUMPTION_REFINED_NOT_DISCHARGED"

/-- Next strict target after the bounded local reduction packet. -/
def selectedQMStatEntropyLogDomainZeroHandlingReductionReviewTargetId :
    String :=
  "review_qm_stat_entropy_log_domain_zero_handling_reduction_result"

/-- Canonical release report for this packet. -/
def qmStatEntropyLogDomainZeroHandlingReductionReportPath : String :=
  "formal/docs/release/QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_REDUCTION_20260510_v0.json"

/-- Focused validation target for this packet. -/
def qmStatEntropyLogDomainZeroHandlingReductionValidationTarget : String :=
  "python -m pytest \
  formal/python/tests/test_qm_stat_entropy_log_domain_zero_handling_reduction_gate.py -q"

/-- The three possible outcomes authorized by the bounded packet. -/
inductive QMStatEntropyLogDomainZeroHandlingReductionOutcome where
  | reducedLeanBacked
  | retainedSuppliedOnly
  | refinedNotDischarged
deriving DecidableEq, Repr

/-- Stable outcome ids. -/
def qmStatEntropyLogDomainZeroHandlingReductionOutcomeId :
    QMStatEntropyLogDomainZeroHandlingReductionOutcome -> String
  | .reducedLeanBacked =>
      qmStatEntropyLogDomainZeroHandlingReducedLeanBackedTokenId
  | .retainedSuppliedOnly =>
      qmStatEntropyLogDomainZeroHandlingRetainedSuppliedOnlyTokenId
  | .refinedNotDischarged =>
      qmStatEntropyLogDomainZeroHandlingRefinedNotDischargedTokenId

/-- Local mass cases governed by the zero-handling convention. -/
inductive QMStatEntropyLogDomainMassCase where
  | zeroProbability
  | positiveProbability
  | outsideConventionDomain
deriving DecidableEq, Repr

/-- Stable ids for the local convention cases. -/
def qmStatEntropyLogDomainMassCaseId :
    QMStatEntropyLogDomainMassCase -> String
  | .zeroProbability => "zero_probability"
  | .positiveProbability => "positive_probability"
  | .outsideConventionDomain => "outside_current_local_convention"

/-- Positive probability is the only case admitted to the local log-domain path. -/
def qmStatEntropyLogDomainAdmitsLog :
    QMStatEntropyLogDomainMassCase -> Bool
  | .positiveProbability => true
  | .zeroProbability => false
  | .outsideConventionDomain => false

/-- Zero probability is routed to the local zero-contribution convention. -/
def qmStatEntropyZeroProbabilityUsesZeroContribution :
    QMStatEntropyLogDomainMassCase -> Bool
  | .zeroProbability => true
  | .positiveProbability => false
  | .outsideConventionDomain => false

/-- Human-facing local contribution case ids. -/
def qmStatEntropyLogDomainContributionCaseId :
    QMStatEntropyLogDomainMassCase -> String
  | .zeroProbability => "zero_probability_contribution_0_by_convention"
  | .positiveProbability => "positive_probability_enters_log_domain"
  | .outsideConventionDomain => "outside_current_local_convention"

/-- Lean-backed local convention structure for log-domain and zero handling. -/
structure QMStatEntropyLogDomainZeroHandlingConvention where
  convention_id : String
  selected_assumption_class_id : String
  positive_probability_case_id : String
  positive_probability_enters_log_domain :
    qmStatEntropyLogDomainAdmitsLog .positiveProbability = true
  zero_probability_case_id : String
  zero_probability_excluded_from_log_domain :
    qmStatEntropyLogDomainAdmitsLog .zeroProbability = false
  zero_probability_uses_zero_contribution :
    qmStatEntropyZeroProbabilityUsesZeroContribution .zeroProbability = true
  zero_probability_contribution_case_id : String
  outside_domain_case_id : String
  outside_domain_not_admitted_to_log_domain :
    qmStatEntropyLogDomainAdmitsLog .outsideConventionDomain = false
  theorem_scope : String

/-- The reduced local convention object. -/
def qmStatEntropyLogDomainZeroHandlingConventionV0 :
    QMStatEntropyLogDomainZeroHandlingConvention where
  convention_id :=
    "qm_stat_entropy_log_domain_zero_handling_local_convention_v0"
  selected_assumption_class_id :=
    selectedQMStatEntropyAssumptionReductionCandidateIdV0
  positive_probability_case_id :=
    qmStatEntropyLogDomainMassCaseId .positiveProbability
  positive_probability_enters_log_domain := by
    rfl
  zero_probability_case_id :=
    qmStatEntropyLogDomainMassCaseId .zeroProbability
  zero_probability_excluded_from_log_domain := by
    rfl
  zero_probability_uses_zero_contribution := by
    rfl
  zero_probability_contribution_case_id :=
    qmStatEntropyLogDomainContributionCaseId .zeroProbability
  outside_domain_case_id :=
    qmStatEntropyLogDomainMassCaseId .outsideConventionDomain
  outside_domain_not_admitted_to_log_domain := by
    rfl
  theorem_scope :=
    "local convention only; not a target STAT entropy theorem discharge"

theorem qm_stat_entropy_log_domain_positive_case_admitted_v0 :
    qmStatEntropyLogDomainAdmitsLog .positiveProbability = true := by
  rfl

theorem qm_stat_entropy_log_domain_zero_case_not_admitted_v0 :
    qmStatEntropyLogDomainAdmitsLog .zeroProbability = false := by
  rfl

theorem qm_stat_entropy_log_domain_zero_case_uses_zero_contribution_v0 :
    qmStatEntropyZeroProbabilityUsesZeroContribution .zeroProbability =
      true := by
  rfl

theorem qm_stat_entropy_log_domain_outside_case_not_admitted_v0 :
    qmStatEntropyLogDomainAdmitsLog .outsideConventionDomain = false := by
  rfl

/-- Status readout for the bounded reduction packet. -/
structure QMStatEntropyLogDomainZeroHandlingReductionStatus where
  candidate_selection_consumed : Prop
  candidate_selection_consumed_evidence : candidate_selection_consumed
  selected_candidate_id : String
  selected_candidate_label : String
  addressed_assumption_class_id : String
  addressed_assumption_count : Nat
  source_assumption_class_count : Nat
  only_selected_assumption_addressed : Prop
  only_selected_assumption_addressed_evidence :
    only_selected_assumption_addressed
  local_convention_structure_defined : Prop
  local_convention_structure_defined_evidence :
    local_convention_structure_defined
  local_convention : QMStatEntropyLogDomainZeroHandlingConvention
  positive_probability_log_domain_rule_lean_backed : Prop
  positive_probability_log_domain_rule_lean_backed_evidence :
    positive_probability_log_domain_rule_lean_backed
  zero_probability_zero_contribution_rule_lean_backed : Prop
  zero_probability_zero_contribution_rule_lean_backed_evidence :
    zero_probability_zero_contribution_rule_lean_backed
  assumption_authority_before : String
  assumption_authority_after : String
  selected_assumption_reduced_to_lean_backed_local_convention : Prop
  selected_assumption_reduced_to_lean_backed_local_convention_evidence :
    selected_assumption_reduced_to_lean_backed_local_convention
  outcome : QMStatEntropyLogDomainZeroHandlingReductionOutcome
  result_token : String
  fallback_retained_token : String
  fallback_refined_token : String
  selected_next_target : String
  consumed_target : String
  consumed_candidate_token : String
  source_candidate_surface_id : String
  source_candidate_report_path : String
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
Current packet: reduce only the selected log-domain/zero-handling assumption
to a local Lean-backed convention object while preserving the target entropy
semantics theorem gap.
-/
def qmStatEntropyLogDomainZeroHandlingReductionStatusV0 :
    QMStatEntropyLogDomainZeroHandlingReductionStatus where
  candidate_selection_consumed :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.exactly_one_reduction_candidate_selected
  candidate_selection_consumed_evidence :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.exactly_one_reduction_candidate_selected_evidence
  selected_candidate_id :=
    selectedQMStatEntropyAssumptionReductionCandidateIdV0
  selected_candidate_label :=
    selectedQMStatEntropyAssumptionReductionCandidateLabelV0
  addressed_assumption_class_id :=
    selectedQMStatEntropyAssumptionReductionCandidateIdV0
  addressed_assumption_count := 1
  source_assumption_class_count :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.candidate_count
  only_selected_assumption_addressed := True
  only_selected_assumption_addressed_evidence := True.intro
  local_convention_structure_defined := True
  local_convention_structure_defined_evidence := True.intro
  local_convention := qmStatEntropyLogDomainZeroHandlingConventionV0
  positive_probability_log_domain_rule_lean_backed := True
  positive_probability_log_domain_rule_lean_backed_evidence := True.intro
  zero_probability_zero_contribution_rule_lean_backed := True
  zero_probability_zero_contribution_rule_lean_backed_evidence := True.intro
  assumption_authority_before := "not yet represented"
  assumption_authority_after := "Lean-backed local convention"
  selected_assumption_reduced_to_lean_backed_local_convention := True
  selected_assumption_reduced_to_lean_backed_local_convention_evidence :=
    True.intro
  outcome := .reducedLeanBacked
  result_token :=
    qmStatEntropyLogDomainZeroHandlingReductionOutcomeId .reducedLeanBacked
  fallback_retained_token :=
    qmStatEntropyLogDomainZeroHandlingRetainedSuppliedOnlyTokenId
  fallback_refined_token :=
    qmStatEntropyLogDomainZeroHandlingRefinedNotDischargedTokenId
  selected_next_target :=
    selectedQMStatEntropyLogDomainZeroHandlingReductionReviewTargetId
  consumed_target := qmStatEntropyLogDomainZeroHandlingReductionConsumedTargetId
  consumed_candidate_token :=
    qmStatEntropyLogDomainZeroHandlingReductionConsumedCandidateTokenId
  source_candidate_surface_id :=
    qmStatEntropyAssumptionReductionCandidateSelectionSurfaceId
  source_candidate_report_path :=
    qmStatEntropyAssumptionReductionCandidateSelectionReportPath
  surface_id := qmStatEntropyLogDomainZeroHandlingReductionSurfaceId
  report_path := qmStatEntropyLogDomainZeroHandlingReductionReportPath
  validation_target := qmStatEntropyLogDomainZeroHandlingReductionValidationTarget
  target_entropy_semantics_lean_backed :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.target_entropy_semantics_lean_backed
  target_entropy_semantics_not_lean_backed :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.target_entropy_semantics_not_lean_backed
  target_entropy_semantics_supplied_only :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.target_entropy_semantics_supplied_only
  target_entropy_semantics_supplied_only_evidence :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.target_entropy_semantics_supplied_only_evidence
  entropy_semantics_theorem_discharged :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.theorem_gap_discharged
  entropy_semantics_theorem_not_discharged :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.theorem_gap_not_discharged
  qm_stat_pillar_completion_inferred :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.qm_stat_pillar_completion_inferred
  qm_stat_pillar_completion_not_inferred :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.qm_stat_pillar_completion_not_inferred
  seam_closure_inferred :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.seam_closure_inferred
  seam_closure_not_inferred :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.seam_closure_not_inferred
  phase2_readiness_claim :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.phase2_readiness_claim
  phase2_readiness_not_claimed :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.phase2_readiness_not_claimed
  empirical_adequacy_claim :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.empirical_adequacy_claim
  empirical_adequacy_not_claimed :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.empirical_adequacy_not_claimed
  canonical_toe_claim :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.canonical_toe_claim
  canonical_toe_not_claimed :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.canonical_toe_not_claimed
  master_action_promoted :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.master_action_promoted
  master_action_not_promoted :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.master_action_not_promoted
  qft_gr_source_map_closure_authorized :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.qft_gr_source_map_closure_authorized
  qft_gr_source_map_closure_not_authorized :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.qft_gr_source_map_closure_not_authorized
  governance_manifest_enrollment_authorized :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.governance_manifest_enrollment_authorized
  governance_manifest_enrollment_not_authorized :=
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.governance_manifest_enrollment_not_authorized
  status := .retained

/-- Public readout for the bounded reduction packet. -/
def qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0 :
    QMStatEntropyLogDomainZeroHandlingReductionStatus :=
  qmStatEntropyLogDomainZeroHandlingReductionStatusV0

theorem qm_stat_entropy_log_domain_zero_handling_reduction_consumes_live_target_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.consumed_target) =
      "prepare_selected_qm_stat_entropy_assumption_reduction_bounded_attack" := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_consumes_candidate_token_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.consumed_candidate_token) =
      "QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTED" := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_selected_assumption_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.addressed_assumption_class_id) =
      "log_domain_zero_handling_convention_required" := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_addresses_one_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.addressed_assumption_count) =
      1 := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_source_map_count_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.source_assumption_class_count) =
      8 := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_only_selected_v0 :
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.only_selected_assumption_addressed := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.only_selected_assumption_addressed_evidence

theorem qm_stat_entropy_log_domain_zero_handling_reduction_local_convention_defined_v0 :
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.local_convention_structure_defined := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.local_convention_structure_defined_evidence

theorem qm_stat_entropy_log_domain_zero_handling_reduction_result_token_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.result_token) =
      "QM_STAT_ENTROPY_LOG_DOMAIN_ZERO_HANDLING_ASSUMPTION_REDUCED_LEAN_BACKED" := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_next_target_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.selected_next_target) =
      "review_qm_stat_entropy_log_domain_zero_handling_reduction_result" := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_frontier_target_v0 :
    Option.map (fun entry => entry.next_strict_slice)
      (crossPillarFrontierEntryByRow? .masterAction) =
      some "prepare_qm_stat_entropy_assumption_reduction_candidate_selection" := by
  decide

theorem qm_stat_entropy_log_domain_zero_handling_reduction_authority_after_v0 :
    (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.assumption_authority_after) =
      "Lean-backed local convention" := by
  rfl

theorem qm_stat_entropy_log_domain_zero_handling_reduction_reduced_local_convention_v0 :
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.selected_assumption_reduced_to_lean_backed_local_convention := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.selected_assumption_reduced_to_lean_backed_local_convention_evidence

theorem qm_stat_entropy_log_domain_zero_handling_reduction_no_target_entropy_lean_backed_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
        |>.target_entropy_semantics_lean_backed) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.target_entropy_semantics_not_lean_backed

theorem qm_stat_entropy_log_domain_zero_handling_reduction_supplied_only_preserved_v0 :
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.target_entropy_semantics_supplied_only := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.target_entropy_semantics_supplied_only_evidence

theorem qm_stat_entropy_log_domain_zero_handling_reduction_no_entropy_theorem_discharge_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
        |>.entropy_semantics_theorem_discharged) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.entropy_semantics_theorem_not_discharged

theorem qm_stat_entropy_log_domain_zero_handling_reduction_no_qm_stat_completion_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
        |>.qm_stat_pillar_completion_inferred) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.qm_stat_pillar_completion_not_inferred

theorem qm_stat_entropy_log_domain_zero_handling_reduction_no_seam_closure_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
        |>.seam_closure_inferred) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.seam_closure_not_inferred

theorem qm_stat_entropy_log_domain_zero_handling_reduction_no_phase2_readiness_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
        |>.phase2_readiness_claim) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.phase2_readiness_not_claimed

theorem qm_stat_entropy_log_domain_zero_handling_reduction_no_empirical_adequacy_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
        |>.empirical_adequacy_claim) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.empirical_adequacy_not_claimed

theorem qm_stat_entropy_log_domain_zero_handling_reduction_no_canonical_toe_claim_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
        |>.canonical_toe_claim) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.canonical_toe_not_claimed

theorem qm_stat_entropy_log_domain_zero_handling_reduction_master_action_not_promoted_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
        |>.master_action_promoted) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.master_action_not_promoted

theorem qm_stat_entropy_log_domain_zero_handling_reduction_qft_gr_not_authorized_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
        |>.qft_gr_source_map_closure_authorized) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.qft_gr_source_map_closure_not_authorized

theorem qm_stat_entropy_log_domain_zero_handling_reduction_manifest_not_enrolled_v0 :
    Not
      (qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
        |>.governance_manifest_enrollment_authorized) := by
  exact
    qmStatEntropyLogDomainZeroHandlingReductionStatusReadoutV0
      |>.governance_manifest_enrollment_not_authorized

end QMStatEntropyLogDomainZeroHandlingReduction
end Derivation
end ToeFormal
