/-
ToeFormal/Derivation/QMStatEntropyAssumptionReductionCandidateSelection.lean

Candidate-selection packet for the QM-STAT entropy-semantics supporting
assumption map.

Scope:
- consume `prepare_qm_stat_entropy_assumption_reduction_candidate_selection`
- consume `POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_NEXT_ATTACK_SELECTED`
- evaluate all eight mapped supporting assumptions
- select exactly one bounded reduction candidate
- select `log_domain_zero_handling_convention_required`
- record why that candidate is preferred
- rotate only to `prepare_selected_qm_stat_entropy_assumption_reduction_bounded_attack`
- do not execute the selected reduction here
- do not infer entropy-semantics theorem discharge, assumption discharge,
  QM-STAT pillar completion, seam closure, Phase 2 readiness, empirical
  adequacy, canonical ToE status, master-action promotion, QFT-GR source-map
  closure, selected-target execution, or governance-manifest enrollment
- do not enroll this focused packet gate in the governance manifest
- remain a candidate-selection map, not an attempted theorem discharge
-/

import ToeFormal.Derivation.PostQMStatEntropyAssumptionMapBoundedAttackSelection

namespace ToeFormal
namespace Derivation
namespace QMStatEntropyAssumptionReductionCandidateSelection

open CrossPillarClosureFrontier
open CrossPillarDerivationProtocol
open QMStatEntropySemanticsSupportingAssumptionMap
open QMStatEntropySemanticsSupportingAssumptionMapResultReview
open PostQMStatEntropyAssumptionMapBoundedAttackSelection

set_option autoImplicit false
set_option linter.style.longLine false

/-- Surface id for the QM-STAT entropy assumption-reduction candidate selection. -/
def qmStatEntropyAssumptionReductionCandidateSelectionSurfaceId : String :=
  "qm_stat_entropy_assumption_reduction_candidate_selection_v0"

/-- Live target consumed by this candidate-selection packet. -/
def qmStatEntropyAssumptionReductionCandidateSelectionConsumedTargetId :
    String :=
  selectedPostQMStatEntropyAssumptionMapNextTargetV0

/-- Selector token consumed by this candidate-selection packet. -/
def qmStatEntropyAssumptionReductionCandidateSelectionConsumedSelectorTokenId :
    String :=
  postQMStatEntropyAssumptionMapBoundedAttackSelectionOutputTokenId

/-- Result token emitted by this candidate-selection packet. -/
def qmStatEntropyAssumptionReductionCandidateSelectionResultTokenId : String :=
  "QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTED"

/-- Next strict target after selecting the candidate. -/
def selectedQMStatEntropyAssumptionReductionBoundedAttackTargetId : String :=
  "prepare_selected_qm_stat_entropy_assumption_reduction_bounded_attack"

/-- Canonical release report for this packet. -/
def qmStatEntropyAssumptionReductionCandidateSelectionReportPath : String :=
  "formal/docs/release/QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_20260510_v0.json"

/-- Focused validation target for this packet. -/
def qmStatEntropyAssumptionReductionCandidateSelectionValidationTarget :
    String :=
  "python -m pytest \
  formal/python/tests/test_qm_stat_entropy_assumption_reduction_candidate_selection_gate.py -q"

/-- Ranking criteria used for all mapped supporting assumptions. -/
inductive QMStatEntropyAssumptionReductionSelectionCriterion where
  | localFormalizability
  | lowOverclaimRisk
  | dependencyCount
  | leanDefinitionOrStructureFit
  | entropyGapClarification
deriving DecidableEq, Repr

/-- Stable criterion ids for release and gate parity. -/
def qmStatEntropyAssumptionReductionSelectionCriterionId :
    QMStatEntropyAssumptionReductionSelectionCriterion -> String
  | .localFormalizability => "local_formalizability"
  | .lowOverclaimRisk => "risk_of_overclaim"
  | .dependencyCount => "dependency_count"
  | .leanDefinitionOrStructureFit =>
      "representable_as_lean_definition_or_structure"
  | .entropyGapClarification =>
      "materially_clarifies_supplied_only_entropy_gap"

/-- Criteria applied to every candidate. -/
def qmStatEntropyAssumptionReductionSelectionCriteriaV0 : List String :=
  [ qmStatEntropyAssumptionReductionSelectionCriterionId
      .localFormalizability
  , qmStatEntropyAssumptionReductionSelectionCriterionId
      .lowOverclaimRisk
  , qmStatEntropyAssumptionReductionSelectionCriterionId
      .dependencyCount
  , qmStatEntropyAssumptionReductionSelectionCriterionId
      .leanDefinitionOrStructureFit
  , qmStatEntropyAssumptionReductionSelectionCriterionId
      .entropyGapClarification
  ]

/-- Reduction priority bands after evaluating the criteria. -/
inductive QMStatEntropyAssumptionReductionPriority where
  | highest
  | high
  | medium
  | deferred
deriving DecidableEq, Repr

/-- Stable priority ids. -/
def qmStatEntropyAssumptionReductionPriorityId :
    QMStatEntropyAssumptionReductionPriority -> String
  | .highest => "highest"
  | .high => "high"
  | .medium => "medium"
  | .deferred => "deferred"

/-- One scored candidate row. Scores are local selector metadata only. -/
structure QMStatEntropyAssumptionReductionCandidateRow where
  assumption_class : QMStatEntropySemanticsSupportingAssumptionClass
  class_id : String
  class_label : String
  authority_id : String
  local_formalizability_score : Nat
  low_overclaim_risk_score : Nat
  dependency_count : Nat
  lean_definition_or_structure_fit : Bool
  entropy_gap_clarification_score : Nat
  priority : QMStatEntropyAssumptionReductionPriority
  priority_id : String
  rank : Nat
  selected_for_reduction : Bool
  reason : String

/-- Selected candidate: make log/zero convention explicit before reduction. -/
def selectedQMStatEntropyAssumptionReductionCandidateClassV0 :
    QMStatEntropySemanticsSupportingAssumptionClass :=
  .logDomainZeroHandlingConventionRequired

/-- Selected candidate id. -/
def selectedQMStatEntropyAssumptionReductionCandidateIdV0 : String :=
  qmStatEntropySemanticsSupportingAssumptionClassId
    selectedQMStatEntropyAssumptionReductionCandidateClassV0

/-- Selected candidate label. -/
def selectedQMStatEntropyAssumptionReductionCandidateLabelV0 : String :=
  qmStatEntropySemanticsSupportingAssumptionClassLabel
    selectedQMStatEntropyAssumptionReductionCandidateClassV0

/-- Candidate rows after applying the five criteria to all eight assumptions. -/
def qmStatEntropyAssumptionReductionCandidateRowsV0 :
    List QMStatEntropyAssumptionReductionCandidateRow :=
  [ { assumption_class := .logDomainZeroHandlingConventionRequired
      class_id := "log_domain_zero_handling_convention_required"
      class_label := "log-domain / zero-handling convention required"
      authority_id := "not yet represented"
      local_formalizability_score := 5
      low_overclaim_risk_score := 5
      dependency_count := 1
      lean_definition_or_structure_fit := true
      entropy_gap_clarification_score := 5
      priority := .highest
      priority_id := "highest"
      rank := 1
      selected_for_reduction := true
      reason :=
        "The log-domain and zero-probability convention is absent, locally \
        representable as a small definition/structure, low dependency, and \
        directly clarifies the entropy functional semantics without asserting \
        a theorem discharge." }
  , { assumption_class := .normalizationOrProbabilityMassConditionRequired
      class_id := "normalization_or_probability_mass_condition_required"
      class_label := "normalization or probability-mass condition required"
      authority_id := "not yet represented"
      local_formalizability_score := 4
      low_overclaim_risk_score := 4
      dependency_count := 2
      lean_definition_or_structure_fit := true
      entropy_gap_clarification_score := 5
      priority := .high
      priority_id := "high"
      rank := 2
      selected_for_reduction := false
      reason :=
        "A mass condition is also local and important, but it risks widening \
        into probability-state semantics before the entropy convention is fixed." }
  , { assumption_class := .targetEntropyFunctionalDefinitionRequired
      class_id := "target_entropy_functional_definition_required"
      class_label := "target entropy functional definition required"
      authority_id := "Lean-backed"
      local_formalizability_score := 4
      low_overclaim_risk_score := 3
      dependency_count := 2
      lean_definition_or_structure_fit := true
      entropy_gap_clarification_score := 4
      priority := .medium
      priority_id := "medium"
      rank := 3
      selected_for_reduction := false
      reason :=
        "A finite entropy-like functional already exists, so this is less \
        immediate than the missing convention governing logarithms and zeros." }
  , { assumption_class := .finiteSupportOrSummabilityConditionRequired
      class_id := "finite_support_or_summability_condition_required"
      class_label := "finite-support or summability condition required"
      authority_id := "Lean-backed"
      local_formalizability_score := 4
      low_overclaim_risk_score := 4
      dependency_count := 2
      lean_definition_or_structure_fit := true
      entropy_gap_clarification_score := 3
      priority := .medium
      priority_id := "medium"
      rank := 4
      selected_for_reduction := false
      reason :=
        "The finite-state scope is already Lean-backed; changing support or \
        summability would be a later generalization rather than the first \
        missing semantic convention." }
  , { assumption_class := .comparisonTargetSemanticsRequired
      class_id := "comparison_target_semantics_required"
      class_label := "comparison target semantics required"
      authority_id := "supplied-only"
      local_formalizability_score := 3
      low_overclaim_risk_score := 2
      dependency_count := 4
      lean_definition_or_structure_fit := true
      entropy_gap_clarification_score := 5
      priority := .medium
      priority_id := "medium"
      rank := 5
      selected_for_reduction := false
      reason :=
        "Comparison target semantics would materially clarify the gap, but it \
        is broader and higher-risk than first recording a local entropy \
        convention." }
  , { assumption_class := .statisticalStateDomainSemanticsRequired
      class_id := "statistical_state_domain_semantics_required"
      class_label := "statistical state/domain semantics required"
      authority_id := "supplied-only"
      local_formalizability_score := 2
      low_overclaim_risk_score := 2
      dependency_count := 5
      lean_definition_or_structure_fit := true
      entropy_gap_clarification_score := 4
      priority := .deferred
      priority_id := "deferred"
      rank := 6
      selected_for_reduction := false
      reason :=
        "State/domain semantics are important but broader than the local \
        entropy convention and would risk claiming too much in one bounded \
        step." }
  , { assumption_class := .transportAlignmentRelationRequired
      class_id := "transport_alignment_relation_required"
      class_label := "transport/alignment relation required"
      authority_id := "Lean-backed"
      local_formalizability_score := 2
      low_overclaim_risk_score := 2
      dependency_count := 6
      lean_definition_or_structure_fit := true
      entropy_gap_clarification_score := 3
      priority := .deferred
      priority_id := "deferred"
      rank := 7
      selected_for_reduction := false
      reason :=
        "Transport/alignment is conditionally Lean-backed but concrete target \
        alignment is dependency-heavy and less local than zero handling." }
  , { assumption_class := .residualZeroBridgeConditionRequired
      class_id := "residual_zero_bridge_condition_required"
      class_label := "residual-zero bridge condition required"
      authority_id := "Lean-backed"
      local_formalizability_score := 1
      low_overclaim_risk_score := 1
      dependency_count := 7
      lean_definition_or_structure_fit := false
      entropy_gap_clarification_score := 4
      priority := .deferred
      priority_id := "deferred"
      rank := 8
      selected_for_reduction := false
      reason :=
        "The residual-zero bridge is central but dependency-heavy and would be \
        a theorem-bridge attempt, not a first local convention-reduction step." }
  ]

/-- Candidate-selection status readout. -/
structure QMStatEntropyAssumptionReductionCandidateSelectionStatus where
  selector_result_consumed : Prop
  selector_result_consumed_evidence : selector_result_consumed
  all_mapped_assumptions_evaluated : Prop
  all_mapped_assumptions_evaluated_evidence :
    all_mapped_assumptions_evaluated
  exactly_one_reduction_candidate_selected : Prop
  exactly_one_reduction_candidate_selected_evidence :
    exactly_one_reduction_candidate_selected
  candidate_rows : List QMStatEntropyAssumptionReductionCandidateRow
  candidate_count : Nat
  criteria : List String
  criteria_count : Nat
  selected_candidate_class :
    QMStatEntropySemanticsSupportingAssumptionClass
  selected_candidate_id : String
  selected_candidate_label : String
  selected_candidate_rank : Nat
  selected_candidate_reason : String
  result_token : String
  selected_next_target : String
  consumed_target : String
  consumed_selector_token : String
  source_selector_surface_id : String
  selected_gap_id : String
  selected_obligation_id : String
  surface_id : String
  report_path : String
  validation_target : String
  reduction_executed : Prop
  reduction_not_executed : Not reduction_executed
  assumption_discharge_claim : Prop
  assumption_discharge_not_claimed : Not assumption_discharge_claim
  target_entropy_semantics_lean_backed : Prop
  target_entropy_semantics_not_lean_backed :
    Not target_entropy_semantics_lean_backed
  target_entropy_semantics_supplied_only : Prop
  target_entropy_semantics_supplied_only_evidence :
    target_entropy_semantics_supplied_only
  theorem_gap_discharged : Prop
  theorem_gap_not_discharged : Not theorem_gap_discharged
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
Current packet: rank all eight assumptions and select exactly one local
candidate for the next bounded reduction attempt.
-/
def qmStatEntropyAssumptionReductionCandidateSelectionStatusV0 :
    QMStatEntropyAssumptionReductionCandidateSelectionStatus where
  selector_result_consumed :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.exactly_one_next_bounded_target_selected
  selector_result_consumed_evidence :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.exactly_one_next_bounded_target_selected_evidence
  all_mapped_assumptions_evaluated :=
    qmStatEntropyAssumptionReductionCandidateRowsV0.length = 8
  all_mapped_assumptions_evaluated_evidence := by
    rfl
  exactly_one_reduction_candidate_selected := True
  exactly_one_reduction_candidate_selected_evidence := True.intro
  candidate_rows := qmStatEntropyAssumptionReductionCandidateRowsV0
  candidate_count := qmStatEntropyAssumptionReductionCandidateRowsV0.length
  criteria := qmStatEntropyAssumptionReductionSelectionCriteriaV0
  criteria_count := qmStatEntropyAssumptionReductionSelectionCriteriaV0.length
  selected_candidate_class :=
    selectedQMStatEntropyAssumptionReductionCandidateClassV0
  selected_candidate_id :=
    selectedQMStatEntropyAssumptionReductionCandidateIdV0
  selected_candidate_label :=
    selectedQMStatEntropyAssumptionReductionCandidateLabelV0
  selected_candidate_rank := 1
  selected_candidate_reason :=
    "Log-domain and zero-handling convention is absent, locally \
    representable, low dependency, and directly clarifies the supplied-only \
    entropy semantics gap without executing a theorem discharge."
  result_token :=
    qmStatEntropyAssumptionReductionCandidateSelectionResultTokenId
  selected_next_target :=
    selectedQMStatEntropyAssumptionReductionBoundedAttackTargetId
  consumed_target :=
    qmStatEntropyAssumptionReductionCandidateSelectionConsumedTargetId
  consumed_selector_token :=
    qmStatEntropyAssumptionReductionCandidateSelectionConsumedSelectorTokenId
  source_selector_surface_id :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionSurfaceId
  selected_gap_id :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.selected_gap_id
  selected_obligation_id :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.selected_obligation_id
  surface_id := qmStatEntropyAssumptionReductionCandidateSelectionSurfaceId
  report_path := qmStatEntropyAssumptionReductionCandidateSelectionReportPath
  validation_target :=
    qmStatEntropyAssumptionReductionCandidateSelectionValidationTarget
  reduction_executed := False
  reduction_not_executed := by
    intro h
    exact h
  assumption_discharge_claim := False
  assumption_discharge_not_claimed := by
    intro h
    exact h
  target_entropy_semantics_lean_backed :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.target_entropy_semantics_lean_backed
  target_entropy_semantics_not_lean_backed :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.target_entropy_semantics_not_lean_backed
  target_entropy_semantics_supplied_only :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.target_entropy_semantics_supplied_only
  target_entropy_semantics_supplied_only_evidence :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.target_entropy_semantics_supplied_only_evidence
  theorem_gap_discharged :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.theorem_gap_discharged
  theorem_gap_not_discharged :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.theorem_gap_not_discharged
  qm_stat_pillar_completion_inferred :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.qm_stat_pillar_completion_inferred
  qm_stat_pillar_completion_not_inferred :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.qm_stat_pillar_completion_not_inferred
  seam_closure_inferred :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.seam_closure_inferred
  seam_closure_not_inferred :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.seam_closure_not_inferred
  phase2_readiness_claim :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.phase2_readiness_claim
  phase2_readiness_not_claimed :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.phase2_readiness_not_claimed
  empirical_adequacy_claim :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.empirical_adequacy_claim
  empirical_adequacy_not_claimed :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.empirical_adequacy_not_claimed
  canonical_toe_claim :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.canonical_toe_claim
  canonical_toe_not_claimed :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.canonical_toe_not_claimed
  master_action_promoted :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.master_action_promoted
  master_action_not_promoted :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.master_action_not_promoted
  qft_gr_source_map_closure_authorized :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.qft_gr_source_map_closure_authorized
  qft_gr_source_map_closure_not_authorized :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.qft_gr_source_map_closure_not_authorized
  governance_manifest_enrollment_authorized :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.governance_manifest_enrollment_authorized
  governance_manifest_enrollment_not_authorized :=
    postQMStatEntropyAssumptionMapBoundedAttackSelectionStatusReadoutV0
      |>.governance_manifest_enrollment_not_authorized
  status := .retained

/-- Public readout for the candidate-selection packet. -/
def qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0 :
    QMStatEntropyAssumptionReductionCandidateSelectionStatus :=
  qmStatEntropyAssumptionReductionCandidateSelectionStatusV0

theorem qm_stat_entropy_assumption_reduction_candidate_selection_consumes_live_target_v0 :
    (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.consumed_target) =
      "prepare_qm_stat_entropy_assumption_reduction_candidate_selection" := by
  rfl

theorem qm_stat_entropy_assumption_reduction_candidate_selection_consumes_selector_token_v0 :
    (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.consumed_selector_token) =
      "POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_NEXT_ATTACK_SELECTED" := by
  rfl

theorem qm_stat_entropy_assumption_reduction_candidate_selection_result_token_v0 :
    (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.result_token) =
      "QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTED" := by
  rfl

theorem qm_stat_entropy_assumption_reduction_candidate_selection_next_target_v0 :
    (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.selected_next_target) =
      "prepare_selected_qm_stat_entropy_assumption_reduction_bounded_attack" := by
  rfl

theorem qm_stat_entropy_assumption_reduction_candidate_selection_all_8_evaluated_v0 :
    (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.candidate_count) =
      8 := by
  rfl

theorem qm_stat_entropy_assumption_reduction_candidate_selection_criteria_count_v0 :
    (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.criteria_count) =
      5 := by
  rfl

theorem qm_stat_entropy_assumption_reduction_candidate_selection_exactly_one_v0 :
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.exactly_one_reduction_candidate_selected := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.exactly_one_reduction_candidate_selected_evidence

theorem qm_stat_entropy_assumption_reduction_candidate_selection_selected_candidate_v0 :
    (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.selected_candidate_id) =
      "log_domain_zero_handling_convention_required" := by
  rfl

theorem qm_stat_entropy_assumption_reduction_candidate_selection_selected_rank_v0 :
    (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.selected_candidate_rank) =
      1 := by
  rfl

theorem qm_stat_entropy_assumption_reduction_candidate_selection_frontier_target_v0 :
    Option.map (fun entry => entry.next_strict_slice)
      (crossPillarFrontierEntryByRow? .masterAction) =
      some "review_qm_stat_entropy_log_domain_zero_handling_reduction_result" := by
  decide

theorem qm_stat_entropy_assumption_reduction_candidate_selection_does_not_execute_reduction_v0 :
    Not
      (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
        |>.reduction_executed) := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.reduction_not_executed

theorem qm_stat_entropy_assumption_reduction_candidate_selection_no_assumption_discharge_v0 :
    Not
      (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
        |>.assumption_discharge_claim) := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.assumption_discharge_not_claimed

theorem qm_stat_entropy_assumption_reduction_candidate_selection_no_lean_backed_discharge_v0 :
    Not
      (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
        |>.target_entropy_semantics_lean_backed) := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.target_entropy_semantics_not_lean_backed

theorem qm_stat_entropy_assumption_reduction_candidate_selection_supplied_only_preserved_v0 :
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.target_entropy_semantics_supplied_only := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.target_entropy_semantics_supplied_only_evidence

theorem qm_stat_entropy_assumption_reduction_candidate_selection_no_gap_closure_v0 :
    Not
      (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
        |>.theorem_gap_discharged) := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.theorem_gap_not_discharged

theorem qm_stat_entropy_assumption_reduction_candidate_selection_no_qm_stat_completion_v0 :
    Not
      (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
        |>.qm_stat_pillar_completion_inferred) := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.qm_stat_pillar_completion_not_inferred

theorem qm_stat_entropy_assumption_reduction_candidate_selection_no_seam_closure_v0 :
    Not
      (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
        |>.seam_closure_inferred) := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.seam_closure_not_inferred

theorem qm_stat_entropy_assumption_reduction_candidate_selection_no_phase2_readiness_v0 :
    Not
      (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
        |>.phase2_readiness_claim) := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.phase2_readiness_not_claimed

theorem qm_stat_entropy_assumption_reduction_candidate_selection_no_empirical_adequacy_v0 :
    Not
      (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
        |>.empirical_adequacy_claim) := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.empirical_adequacy_not_claimed

theorem qm_stat_entropy_assumption_reduction_candidate_selection_no_canonical_toe_claim_v0 :
    Not
      (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
        |>.canonical_toe_claim) := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.canonical_toe_not_claimed

theorem qm_stat_entropy_assumption_reduction_candidate_selection_master_action_not_promoted_v0 :
    Not
      (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
        |>.master_action_promoted) := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.master_action_not_promoted

theorem qm_stat_entropy_assumption_reduction_candidate_selection_qft_gr_not_authorized_v0 :
    Not
      (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
        |>.qft_gr_source_map_closure_authorized) := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.qft_gr_source_map_closure_not_authorized

theorem qm_stat_entropy_assumption_reduction_candidate_selection_manifest_not_enrolled_v0 :
    Not
      (qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
        |>.governance_manifest_enrollment_authorized) := by
  exact
    qmStatEntropyAssumptionReductionCandidateSelectionStatusReadoutV0
      |>.governance_manifest_enrollment_not_authorized

end QMStatEntropyAssumptionReductionCandidateSelection
end Derivation
end ToeFormal
